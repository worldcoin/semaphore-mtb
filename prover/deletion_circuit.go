package prover

import (
	"fmt"
	"worldcoin/gnark-mbu/prover/keccak"

	"github.com/consensys/gnark/frontend"
	"github.com/reilabs/gnark-lean-extractor/abstractor"
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
	kh := keccak.NewKeccak256(api, circuit.BatchSize*32+2*256)

	var bits []frontend.Variable
	var err error

	for i := 0; i < circuit.BatchSize; i++ {
		bits, err = ToReducedBinaryBigEndian(circuit.DeletionIndices[i], 32, api)
		if err != nil {
			return err
		}
		kh.Write(bits...)
	}

	bits, err = ToReducedBinaryBigEndian(circuit.PreRoot, 256, api)
	if err != nil {
		return err
	}
	kh.Write(bits...)

	bits, err = ToReducedBinaryBigEndian(circuit.PostRoot, 256, api)
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

	prevRoot := circuit.PreRoot

	// Individual insertions.
	for i := 0; i < circuit.BatchSize; i += 1 {
		currentPath := api.ToBinary(circuit.DeletionIndices[i], circuit.Depth+1)
		// Treating indices with the one-too-high bit set as a skip flag. This allows
		// us to pad batches with meaningless ops to commit something even if there
		// isn't enough deletions happening to fill a batch.
		skipFlag := currentPath[circuit.Depth]
		currentPath = currentPath[:circuit.Depth]

		// Verify proof for idComm.
		rootPreDeletion := abstractor.CallGadget(api, VerifyProof{append([]frontend.Variable{circuit.IdComms[i]}, circuit.MerkleProofs[i][:]...), currentPath})[0]

		// Verify proof for empty leaf.
		rootPostDeletion := abstractor.CallGadget(api, VerifyProof{append([]frontend.Variable{emptyLeaf}, circuit.MerkleProofs[i][:]...), currentPath})[0]

		preRootCorrect := api.IsZero(api.Sub(rootPreDeletion, prevRoot))
		preRootCorrectOrSkip := api.Or(preRootCorrect, skipFlag)
		api.AssertIsEqual(preRootCorrectOrSkip, 1)

		// Set root for next iteration.
		prevRoot = api.Select(skipFlag, prevRoot, rootPostDeletion) // If skipFlag is set, we don't update the root.
	}

	// Final root needs to match.
	api.AssertIsEqual(prevRoot, circuit.PostRoot)

	return nil
}
