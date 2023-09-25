package prover

import (
	"worldcoin/gnark-mbu/prover/keccak"

	"github.com/consensys/gnark/frontend"
	"github.com/reilabs/gnark-lean-extractor/v2/abstractor"
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

func (circuit *InsertionMbuCircuit) Define(api frontend.API) error {
	// Hash private inputs.
	// We keccak hash all input to save verification gas. Inputs are arranged as follows:
	// StartIndex || PreRoot || PostRoot || IdComms[0] || IdComms[1] || ... || IdComms[batchSize-1]
	//     32	  ||   256   ||   256    ||    256     ||    256     || ... ||     256 bits
	var bits []frontend.Variable

	// We convert all the inputs to the keccak hash to use big-endian (network) byte
	// ordering so that it agrees with Solidity. This ensures that we don't have to
	// perform the conversion inside the contract and hence save on gas.
	bits_start := abstractor.Call1(api, ToReducedBigEndian{Variable: circuit.StartIndex, Size: 32})
	bits = append(bits, bits_start...)

	bits_pre := abstractor.Call1(api, ToReducedBigEndian{Variable: circuit.PreRoot, Size: 256})
	bits = append(bits, bits_pre...)

	bits_post := abstractor.Call1(api, ToReducedBigEndian{Variable: circuit.PostRoot, Size: 256})
	bits = append(bits, bits_post...)

	for i := 0; i < circuit.BatchSize; i++ {
		bits_id := abstractor.Call1(api, ToReducedBigEndian{Variable: circuit.IdComms[i], Size: 256})
		bits = append(bits, bits_id...)
	}

	hash := keccak.NewKeccak256(api, (circuit.BatchSize+2)*256+32, bits...)
	sum := abstractor.Call(api, FromBinaryBigEndian{Variable: hash})

	// The same endianness conversion has been performed in the hash generation
	// externally, so we can safely assert their equality here.
	api.AssertIsEqual(circuit.InputHash, sum)

	// Actual batch merkle proof verification.
	root := abstractor.Call(api, InsertionProof{
		StartIndex: circuit.StartIndex,
		PreRoot:    circuit.PreRoot,
		IdComms:    circuit.IdComms,

		MerkleProofs: circuit.MerkleProofs,

		BatchSize: circuit.BatchSize,
		Depth:     circuit.Depth,
	})

	// Final root needs to match.
	api.AssertIsEqual(root, circuit.PostRoot)

	return nil
}
