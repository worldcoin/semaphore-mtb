package prover

import (
	"worldcoin/gnark-mbu/prover/keccak"
	"worldcoin/gnark-mbu/prover/poseidon"

	"github.com/consensys/gnark/frontend"
)

type DeletionMbuCircuit struct {
	// single public input
	InputHash frontend.Variable `gnark:",public"`

	// private inputs, but used as public inputs
	DeletionIndices []frontend.Variable `gnark:"input"`
	PreRoot         frontend.Variable   `gnark:"input"`
	PostRoot        frontend.Variable   `gnark:"input"`

	// private inputs
	IdComms      []frontend.Variable   `gnark:"input"`
	MerkleProofs [][]frontend.Variable `gnark:"input"`

	BatchSize int
	Depth     int
}

func (circuit *DeletionMbuCircuit) Define(api frontend.API) error {
	// Hash private inputs.
	// We keccak hash all input to save verification gas. Inputs are arranged as follows:
	// deletionIndices[0] || deletionIndices[1] || ... || deletionIndices[batchSize-1] || PreRoot || PostRoot
	//        32          ||        32          || ... ||              32              ||   256   ||    256
	kh := keccak.NewKeccak256(api, circuit.BatchSize*32+2*256)

	var bits []frontend.Variable
	var err error

	for i := 0; i < circuit.BatchSize; i++ {
		bits, err = ToBinaryBigEndian(circuit.DeletionIndices[i], 32, api)
		if err != nil {
			return err
		}
		kh.Write(bits...)
	}

	bits, err = ToBinaryBigEndian(circuit.PreRoot, 256, api)
	if err != nil {
		return err
	}
	kh.Write(bits...)

	bits, err = ToBinaryBigEndian(circuit.PostRoot, 256, api)
	if err != nil {
		return err
	}
	kh.Write(bits...)

	var sum frontend.Variable
	sum, err = FromBinaryBigEndian(kh.Sum(), api)
	if err != nil {
		return err
	}

	// The same endianness conversion has been performed in the hash generation
	// externally, so we can safely assert their equality here.
	api.AssertIsEqual(circuit.InputHash, sum)

	// Actual batch merkle proof verification.
	var root frontend.Variable
	ph := poseidon.NewPoseidon2(api)

	prevRoot := circuit.PreRoot

	// Individual insertions.
	for i := 0; i < circuit.BatchSize; i += 1 {
		currentPath := api.ToBinary(circuit.DeletionIndices[i], circuit.Depth)

		// Verify proof for empty leaf.
		root = VerifyProof(api, ph, append([]frontend.Variable{circuit.IdComms[i]}, circuit.MerkleProofs[i][:]...), currentPath)
		api.AssertIsEqual(root, prevRoot)

		// Verify proof for idComm.
		root = VerifyProof(api, ph, append([]frontend.Variable{emptyLeaf}, circuit.MerkleProofs[i][:]...), currentPath)

		// Set root for next iteration.
		prevRoot = root
	}

	// Final root needs to match.
	api.AssertIsEqual(root, circuit.PostRoot)

	return nil
}
