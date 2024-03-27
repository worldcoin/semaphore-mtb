package prover

import (
	"fmt"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/reilabs/gnark-lean-extractor/v2/abstractor"

	"worldcoin/gnark-mbu/prover/keccak"
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

	hash, err := keccak.Keccak256(api, circuit.BatchSize*32+2*256, bits...)
	if err != nil {
		return err
	}
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

func ImportDeletionSetup(treeDepth uint32, batchSize uint32, pkPath string, vkPath string) (*ProvingSystem, error) {
	proofs := make([][]frontend.Variable, batchSize)
	for i := 0; i < int(batchSize); i++ {
		proofs[i] = make([]frontend.Variable, treeDepth)
	}
	circuit := DeletionMbuCircuit{
		Depth:           int(treeDepth),
		BatchSize:       int(batchSize),
		DeletionIndices: make([]frontend.Variable, batchSize),
		IdComms:         make([]frontend.Variable, batchSize),
		MerkleProofs:    proofs,
	}
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
	if err != nil {
		return nil, err
	}

	pk, err := LoadProvingKey(pkPath)

	if err != nil {
		return nil, err
	}

	vk, err := LoadVerifyingKey(vkPath)

	if err != nil {
		return nil, err
	}

	return &ProvingSystem{treeDepth, batchSize, pk, vk, ccs}, nil
}
