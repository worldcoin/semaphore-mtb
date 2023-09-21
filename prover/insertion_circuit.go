package prover

import (
	"worldcoin/gnark-mbu/prover/keccak"

	"github.com/consensys/gnark/frontend"
	"github.com/reilabs/gnark-lean-extractor/abstractor"
	"github.com/reilabs/gnark-lean-extractor/extractor"
)

type InsertionMbuCircuit struct {
	// single public input
	InputHash frontend.Variable `gnark:",public"`

	// private inputs, but used as public inputs
	StartIndex frontend.Variable   `gnark:"input"`
	PreRoot    frontend.Variable   `gnark:"input"`
	PostRoot   frontend.Variable   `gnark:"input"`
	IdComms    []frontend.Variable `gnark:"input"`

	// private inputs
	MerkleProofs [][]frontend.Variable `gnark:"input"`

	BatchSize int
	Depth     int
}

func (circuit *InsertionMbuCircuit) AbsDefine(api abstractor.API) error {
	// Hash private inputs.
	// We keccak hash all input to save verification gas. Inputs are arranged as follows:
	// StartIndex || PreRoot || PostRoot || IdComms[0] || IdComms[1] || ... || IdComms[batchSize-1]
	//     32	  ||   256   ||   256    ||    256     ||    256     || ... ||     256 bits
	var bits []frontend.Variable
	var err error

	// We convert all the inputs to the keccak hash to use big-endian (network) byte
	// ordering so that it agrees with Solidity. This ensures that we don't have to
	// perform the conversion inside the contract and hence save on gas.
	bits_start, err := ToReducedBinaryBigEndian(circuit.StartIndex, 32, api)
	if err != nil {
		return err
	}
	bits = append(bits, bits_start...)

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

	for i := 0; i < circuit.BatchSize; i++ {
		bits_id, err := ToReducedBinaryBigEndian(circuit.IdComms[i], 256, api)
		if err != nil {
			return err
		}
		bits = append(bits, bits_id...)
	}

	hash := keccak.NewKeccak256(api, (circuit.BatchSize+2)*256+32, bits...)
	sum, err := FromBinaryBigEndian(hash, api)
	if err != nil {
		return err
	}

	// The same endianness conversion has been performed in the hash generation
	// externally, so we can safely assert their equality here.
	api.AssertIsEqual(circuit.InputHash, sum)

	// Actual batch merkle proof verification.
	root := extractor.Call(api, InsertionProof{
		StartIndex: circuit.StartIndex,
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

func (circuit InsertionMbuCircuit) Define(api frontend.API) error {
	return abstractor.Concretize(api, &circuit)
}