package main

import (
	"worldcoin/gnark-mbu/poseidon"

	"github.com/consensys/gnark/frontend"
)

const (
	batchSize = 1
	depth     = 20
	emptyLeaf = 0
)

type MbuCircuit struct {
	MerkleProofs [batchSize][depth]frontend.Variable
	StartIndex   frontend.Variable            `gnark:",public"`
	PreRoot      frontend.Variable            `gnark:",public"`
	PostRoot     frontend.Variable            `gnark:",public"`
	IdComms      [batchSize]frontend.Variable `gnark:",public"`
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
	var root frontend.Variable
	h := poseidon.NewPoseidon2(api)

	// Empty proof for start.
	root = VerifyProof(api, h, append([]frontend.Variable{emptyLeaf}, circuit.MerkleProofs[0][:]...), api.ToBinary(circuit.StartIndex, depth))
	api.AssertIsEqual(root, circuit.PreRoot)

	// Individual insertions.
	for i := 0; i < batchSize; i += 1 {
		currentIndex := api.Add(circuit.StartIndex, i)
		merkleProof := append([]frontend.Variable{circuit.IdComms[i]}, circuit.MerkleProofs[i][:]...)
		root = VerifyProof(api, h, merkleProof, api.ToBinary(currentIndex, depth))
	}

	// Final root needs to match.
	api.AssertIsEqual(root, circuit.PostRoot)

	return nil
}
