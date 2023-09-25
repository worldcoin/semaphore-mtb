package prover

import (
	"fmt"
	"worldcoin/gnark-mbu/prover/keccak"

	"github.com/consensys/gnark/frontend"
	"github.com/reilabs/gnark-lean-extractor/v2/abstractor"
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
	if circuit.Depth > 31 {
		return fmt.Errorf("max depth supported is 31")
	}
	// Hash private inputs.
	// We keccak hash all input to save verification gas. Inputs are arranged as follows:
	// deletionIndices[0] || deletionIndices[1] || ... || deletionIndices[batchSize-1] || PreRoot || PostRoot
	//        32          ||        32          || ... ||              32              ||   256   ||    256
	var bits []frontend.Variable

	for i := 0; i < circuit.BatchSize; i++ {
		bits_idx := abstractor.Call1(api, ToReducedBigEndian{Variable: circuit.DeletionIndices[i], Size: 32})
		bits = append(bits, bits_idx...)
	}

	bits_pre := abstractor.Call1(api, ToReducedBigEndian{Variable: circuit.PreRoot, Size: 256})
	bits = append(bits, bits_pre...)

	bits_post := abstractor.Call1(api, ToReducedBigEndian{Variable: circuit.PostRoot, Size: 256})
	bits = append(bits, bits_post...)

	hash := keccak.NewKeccak256(api, circuit.BatchSize*32+2*256, bits...)
	sum := abstractor.Call(api, FromBinaryBigEndian{Variable: hash})

	// The same endianness conversion has been performed in the hash generation
	// externally, so we can safely assert their equality here.
	api.AssertIsEqual(circuit.InputHash, sum)

	// Actual batch merkle proof verification.
	root := abstractor.Call(api, DeletionProof{
		DeletionIndices: circuit.DeletionIndices,
		PreRoot:         circuit.PreRoot,
		IdComms:         circuit.IdComms,
		MerkleProofs:    circuit.MerkleProofs,
		BatchSize:       circuit.BatchSize,
		Depth:           circuit.Depth,
	})

	// Final root needs to match.
	api.AssertIsEqual(root, circuit.PostRoot)

	return nil
}
