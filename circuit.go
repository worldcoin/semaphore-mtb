package main

import (
	"worldcoin/gnark-mbu/keccak"
	"worldcoin/gnark-mbu/poseidon"

	"github.com/consensys/gnark/frontend"
)

const (
	batchSize = 100
	depth     = 20
	emptyLeaf = 0
)

type MbuCircuit struct {
	// single public input
	InputHash frontend.Variable `gnark:",public"`

	// private inputs, but used as public inputs
	StartIndex frontend.Variable            `gnark:"input"`
	PreRoot    frontend.Variable            `gnark:"input"`
	PostRoot   frontend.Variable            `gnark:"input"`
	IdComms    [batchSize]frontend.Variable `gnark:"input"`

	// private inputs
	MerkleProofs [batchSize][depth]frontend.Variable `gnark:"input"`
}

func VerifyProof(api frontend.API, h poseidon.Poseidon, proofSet, helper []frontend.Variable) frontend.Variable {
	sum := proofSet[0]
	for i := 1; i < len(proofSet); i++ {
		api.AssertIsBoolean(helper[i-1])
		d1 := api.Select(helper[i-1], proofSet[i], sum)
		d2 := api.Select(helper[i-1], sum, proofSet[i])
		sum = nodeSum(api, h, d1, d2)
	}
	return sum
}

func nodeSum(api frontend.API, h poseidon.Poseidon, a, b frontend.Variable) frontend.Variable {
	h.Write(a, b)
	res := h.Sum()
	h.Reset()
	return res
}

func (circuit *MbuCircuit) Define(api frontend.API) error {
	// Hash private inputs.
	// We keccak hash all input to save verification gas. Inputs are arranged as follows:
	// StartIndex || PreRoot || PostRoot || IdComms[0] || IdComms[1] || ... || IdComms[batchSize-1]
	//     32	  ||   256   ||   256    ||    256     ||    256     || ... ||     256 bits

	kh := keccak.NewKeccak256(api, (batchSize+2)*256+32)
	kh.Write(api.ToBinary(circuit.StartIndex, 32)...)
	kh.Write(api.ToBinary(circuit.PreRoot, 256)...)
	kh.Write(api.ToBinary(circuit.PostRoot, 256)...)
	for i := 0; i < batchSize; i++ {
		kh.Write(api.ToBinary(circuit.IdComms[i], 256)...)
	}
	sum := api.FromBinary(kh.Sum()...)
	api.AssertIsEqual(circuit.InputHash, sum)

	// Actual batch merkle proof verification.
	var root frontend.Variable
	ph := poseidon.NewPoseidon2(api)

	prevRoot := circuit.PreRoot

	// Individual insertions.
	for i := 0; i < batchSize; i += 1 {
		currentIndex := api.Add(circuit.StartIndex, i)
		currentPath := api.ToBinary(currentIndex, depth)

		// Verify proof for empty leaf.
		root = VerifyProof(api, ph, append([]frontend.Variable{emptyLeaf}, circuit.MerkleProofs[i][:]...), currentPath)
		api.AssertIsEqual(root, prevRoot)

		// Verify proof for idComm.
		root = VerifyProof(api, ph, append([]frontend.Variable{circuit.IdComms[i]}, circuit.MerkleProofs[i][:]...), currentPath)

		// Set root for next iteration.
		prevRoot = root
	}

	// Final root needs to match.
	api.AssertIsEqual(root, circuit.PostRoot)

	return nil
}
