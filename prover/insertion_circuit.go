package prover

import (
	"worldcoin/gnark-mbu/prover/keccak"

	"github.com/consensys/gnark/frontend"
	"github.com/reilabs/gnark-lean-extractor/abstractor"
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

	kh := keccak.NewKeccak256(api, (circuit.BatchSize+2)*256+32)

	var bits []frontend.Variable
	var err error

	// We convert all the inputs to the keccak hash to use big-endian (network) byte
	// ordering so that it agrees with Solidity. This ensures that we don't have to
	// perform the conversion inside the contract and hence save on gas.
	bits, err = ToReducedBinaryBigEndian(circuit.StartIndex, 32, api)
	if err != nil {
		return err
	}
	kh.Write(bits...)

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

	for i := 0; i < circuit.BatchSize; i++ {
		bits, err = ToReducedBinaryBigEndian(circuit.IdComms[i], 256, api)
		if err != nil {
			return err
		}
		kh.Write(bits...)
	}

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

	prevRoot := circuit.PreRoot

	// Individual insertions.
	for i := 0; i < circuit.BatchSize; i += 1 {
		currentIndex := api.Add(circuit.StartIndex, i)
		currentPath := api.ToBinary(currentIndex, circuit.Depth)

		// Verify proof for empty leaf.
		root = abstractor.CallGadget(api, VerifyProof{append([]frontend.Variable{emptyLeaf}, circuit.MerkleProofs[i][:]...), currentPath})[0]
		api.AssertIsEqual(root, prevRoot)

		// Verify proof for idComm.
		root = abstractor.CallGadget(api, VerifyProof{append([]frontend.Variable{circuit.IdComms[i]}, circuit.MerkleProofs[i][:]...), currentPath})[0]

		// Set root for next iteration.
		prevRoot = root
	}

	// Final root needs to match.
	api.AssertIsEqual(root, circuit.PostRoot)

	return nil
}
