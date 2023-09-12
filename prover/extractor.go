package prover

import (
	"worldcoin/gnark-mbu/prover/keccak"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/reilabs/gnark-lean-extractor/extractor"
)

func ExtractLean(treeDepth uint32, batchSize uint32) (string, error) {
	// Not checking for batchSize === 0 or treeDepth === 0

	// Initialising MerkleProofs slice with correct dimentions
	proofs := make([][]frontend.Variable, batchSize)
	for i := 0; i < int(batchSize); i++ {
		proofs[i] = make([]frontend.Variable, treeDepth)
	}

	insert := InsertionProof{
		IdComms: make([]frontend.Variable, batchSize),

		MerkleProofs: proofs,

		BatchSize: int(batchSize),
		Depth: int(treeDepth),
	}

	delete := DeletionProof{
		DeletionIndices: make([]frontend.Variable, batchSize),
		IdComms: make([]frontend.Variable, batchSize),

		MerkleProofs: proofs,

		BatchSize: int(batchSize),
		Depth: int(treeDepth),
	}

	assignment_1 := ToReducedBigEndianGadget{Size: 32}
	assignment_2 := ToReducedBigEndianGadget{Size: 256}
	assignment_3 := FromBinaryBigEndianGadget{Variable: make([]frontend.Variable, 256)}

	const laneSize = 64
	const stateSize = 5
	keccak := keccak.KeccakGadget{
		InputSize: int(batchSize)*32+2*256,
		InputData: make([]frontend.Variable, 1056),
		OutputSize: 256,
		Rounds: 24,
		BlockSize: 1088,     
		RotationOffsets: keccak.R,
		RoundConstants: keccak.RC,
		Domain: 0x01,
	}

	return extractor.ExtractGadgets("SemaphoreMTB", ecc.BN254, &insert, &delete, &assignment_1, &assignment_2, &assignment_3, &keccak)
}