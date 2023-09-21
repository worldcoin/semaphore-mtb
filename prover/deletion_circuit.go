package prover

import (
	"fmt"
	"worldcoin/gnark-mbu/prover/keccak"

	"github.com/consensys/gnark/frontend"
	"github.com/reilabs/gnark-lean-extractor/abstractor"
	"github.com/reilabs/gnark-lean-extractor/extractor"
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

func (circuit *DeletionMbuCircuit) AbsDefine(api abstractor.API) error {
	if circuit.Depth > 31 {
		return fmt.Errorf("max depth supported is 31")
	}
	// Hash private inputs.
	// We keccak hash all input to save verification gas. Inputs are arranged as follows:
	// deletionIndices[0] || deletionIndices[1] || ... || deletionIndices[batchSize-1] || PreRoot || PostRoot
	//        32          ||        32          || ... ||              32              ||   256   ||    256
	var bits []frontend.Variable
	var err error

	for i := 0; i < circuit.BatchSize; i++ {
		bits_idx, err := ToReducedBinaryBigEndian(circuit.DeletionIndices[i], 32, api)
		if err != nil {
			return err
		}
		bits = append(bits, bits_idx...)
	}

	bits_pre, err := ToReducedBinaryBigEndian(circuit.PreRoot, 256, api)
	if err != nil {
		return err
	}
	bits = append(bits, bits_pre...)

	bits_post, err := ToReducedBinaryBigEndian(circuit.PostRoot, 256, api)
	if err != nil {
		return err
	}
	bits = append(bits, bits_post...)

	hash := keccak.NewKeccak256(api, circuit.BatchSize*32+2*256, bits...)
	sum, err := FromBinaryBigEndian(hash, api)
	if err != nil {
		return err
	}

	// The same endianness conversion has been performed in the hash generation
	// externally, so we can safely assert their equality here.
	api.AssertIsEqual(circuit.InputHash, sum)

	// Actual batch merkle proof verification.
	root := extractor.Call(api, DeletionProof{
		DeletionIndices: circuit.DeletionIndices,
		PreRoot: circuit.PreRoot,
		IdComms: circuit.IdComms,
		MerkleProofs: circuit.MerkleProofs,
		BatchSize: circuit.BatchSize,
		Depth: circuit.Depth,
	})

	// Final root needs to match.
	api.AssertIsEqual(root, circuit.PostRoot)

	return nil
}

func (circuit DeletionMbuCircuit) Define(api frontend.API) error {
	return abstractor.Concretize(api, &circuit)
}