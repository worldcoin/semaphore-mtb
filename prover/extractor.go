package prover

import (
	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/reilabs/gnark-lean-extractor/v3/extractor"
)

func ExtractLean(treeDepth uint32, batchSize uint32) (string, error) {
	// Not checking for batchSize === 0 or treeDepth === 0

	// Initialising MerkleProofs slice with correct dimentions
	proofs := make([][]frontend.Variable, batchSize)
	for i := 0; i < int(batchSize); i++ {
		proofs[i] = make([]frontend.Variable, treeDepth)
	}

	deletion := DeletionMbuCircuit{
		DeletionIndices: make([]frontend.Variable, batchSize),
		IdComms: make([]frontend.Variable, batchSize),
		MerkleProofs: proofs,

		BatchSize: int(batchSize),
		Depth: int(treeDepth),
	}

	insertion := InsertionMbuCircuit{
		IdComms: make([]frontend.Variable, batchSize),
		MerkleProofs: proofs,

		BatchSize: int(batchSize),
		Depth: int(treeDepth),
	}

	return extractor.ExtractCircuits("SemaphoreMTB", ecc.BN254, &deletion, &insertion)
}