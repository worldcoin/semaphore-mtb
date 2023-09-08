package prover

import (
	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/reilabs/gnark-lean-extractor/extractor"
)

// type InsertDelete struct {
// 	DeletionIndices []frontend.Variable

// 	StartIndex frontend.Variable
	
// 	PreRoot    frontend.Variable
// 	IdComms    []frontend.Variable

// 	MerkleProofs [][]frontend.Variable

// 	BatchSize int
// 	Depth     int
// }

func ExtractDeletion(treeDepth uint32, batchSize uint32) (string, error) {
	// Not checking for batchSize === 0 or treeDepth === 0

	// Initialising MerkleProofs slice with correct dimentions
	proofs := make([][]frontend.Variable, batchSize)
	for i := 0; i < int(batchSize); i++ {
		proofs[i] = make([]frontend.Variable, treeDepth)
	}

	assignment := DeletionProof{
		DeletionIndices: make([]frontend.Variable, batchSize),
		IdComms: make([]frontend.Variable, batchSize),

		MerkleProofs: proofs,

		BatchSize: int(batchSize),
		Depth: int(treeDepth),
	}
	return extractor.GadgetToLeanWithName(&assignment, ecc.BN254, "SemaphoreMTB")
}

func ExtractInsertion(treeDepth uint32, batchSize uint32) (string, error) {
	// Not checking for batchSize === 0 or treeDepth === 0

	// Initialising MerkleProofs slice with correct dimentions
	proofs := make([][]frontend.Variable, batchSize)
	for i := 0; i < int(batchSize); i++ {
		proofs[i] = make([]frontend.Variable, treeDepth)
	}

	assignment := InsertionProof{
		IdComms: make([]frontend.Variable, batchSize),

		MerkleProofs: proofs,

		BatchSize: int(batchSize),
		Depth: int(treeDepth),
	}
	return extractor.GadgetToLeanWithName(&assignment, ecc.BN254, "SemaphoreMTB")
}