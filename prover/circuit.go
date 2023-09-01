package prover

import (
	"strconv"
	"worldcoin/gnark-mbu/prover/keccak"
	"worldcoin/gnark-mbu/prover/poseidon"

	"github.com/consensys/gnark/frontend"
	"github.com/reilabs/gnark-lean-extractor/abstractor"
)

const emptyLeaf = 0

type MbuCircuit struct {
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

type bitPatternLengthError struct {
	actualLength int
}

func (e *bitPatternLengthError) Error() string {
	return "Bit pattern length was " + strconv.Itoa(e.actualLength) + " not a total number of bytes"
}

type VerifyProof struct {
	Proof []frontend.Variable
	Path  []frontend.Variable
}

func (gadget VerifyProof) DefineGadget(api abstractor.API) []frontend.Variable {
	sum := gadget.Proof[0]
	for i := 1; i < len(gadget.Proof); i++ {
		api.AssertIsBoolean(gadget.Path[i-1])
		d1 := api.Select(gadget.Path[i-1], gadget.Proof[i], sum)
		d2 := api.Select(gadget.Path[i-1], sum, gadget.Proof[i])
		sum = api.Call(poseidon.Poseidon2{In1: d1, In2: d2})[0]
	}
	return []frontend.Variable{sum}
}

// SwapBitArrayEndianness Swaps the endianness of the bit pattern in bits,
// returning the result in newBits.
//
// It does not introduce any new circuit constraints as it simply moves the
// variables (that will later be instantiated to bits) around in the slice to
// change the byte ordering. It has been verified to be a constraint-neutral
// operation, so please maintain this invariant when modifying it.
//
// Raises a bitPatternLengthError if the length of bits is not a multiple of a
// number of bytes.
func SwapBitArrayEndianness(bits []frontend.Variable) (newBits []frontend.Variable, err error) {
	bitPatternLength := len(bits)

	if bitPatternLength%8 != 0 {
		return nil, &bitPatternLengthError{bitPatternLength}
	}

	for i := bitPatternLength - 8; i >= 0; i -= 8 {
		currentBytes := bits[i : i+8]
		newBits = append(newBits, currentBytes...)
	}

	if bitPatternLength != len(newBits) {
		return nil, &bitPatternLengthError{len(newBits)}
	}

	return newBits, nil
}

// ToBinaryBigEndian converts the provided variable to the corresponding bit
// pattern using big-endian byte ordering.
//
// Raises a bitPatternLengthError if the number of bits in variable is not a
// whole number of bytes.
func ToBinaryBigEndian(variable frontend.Variable, size int, api frontend.API) (bitsBigEndian []frontend.Variable, err error) {
	bitsLittleEndian := api.ToBinary(variable, size)
	return SwapBitArrayEndianness(bitsLittleEndian)
}

// FromBinaryBigEndian converts the provided bit pattern that uses big-endian
// byte ordering to a variable that uses little-endian byte ordering.
//
// Raises a bitPatternLengthError if the number of bits in `bitsBigEndian` is not
// a whole number of bytes.
func FromBinaryBigEndian(bitsBigEndian []frontend.Variable, api frontend.API) (variable frontend.Variable, err error) {
	bitsLittleEndian, err := SwapBitArrayEndianness(bitsBigEndian)
	if err != nil {
		return nil, err
	}

	return api.FromBinary(bitsLittleEndian...), nil
}

func (circuit *MbuCircuit) Define(api frontend.API) error {
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
	bits, err = ToBinaryBigEndian(circuit.StartIndex, 32, api)
	if err != nil {
		return err
	}
	kh.Write(bits...)

	bits, err = ToBinaryBigEndian(circuit.PreRoot, 256, api)
	if err != nil {
		return err
	}
	kh.Write(bits...)

	bits, err = ToBinaryBigEndian(circuit.PostRoot, 256, api)
	if err != nil {
		return err
	}
	kh.Write(bits...)

	for i := 0; i < circuit.BatchSize; i++ {
		bits, err = ToBinaryBigEndian(circuit.IdComms[i], 256, api)
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
		proof := append([]frontend.Variable{emptyLeaf}, circuit.MerkleProofs[i][:]...)
		root = abstractor.CallGadget(api, VerifyProof{Proof: proof, Path: currentPath})[0]
		api.AssertIsEqual(root, prevRoot)

		// Verify proof for idComm.
		proof = append([]frontend.Variable{circuit.IdComms[i]}, circuit.MerkleProofs[i][:]...)
		root = abstractor.CallGadget(api, VerifyProof{Proof: proof, Path: currentPath})[0]

		// Set root for next iteration.
		prevRoot = root
	}

	// Final root needs to match.
	api.AssertIsEqual(root, circuit.PostRoot)

	return nil
}
