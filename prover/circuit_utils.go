package prover

import (
	"io"
	"strconv"
	"worldcoin/gnark-mbu/prover/poseidon"

	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/frontend"
	"github.com/reilabs/gnark-lean-extractor/abstractor"
	"github.com/reilabs/gnark-lean-extractor/extractor"
)

type Proof struct {
	Proof groth16.Proof
}

type ProvingSystem struct {
	TreeDepth        uint32
	BatchSize        uint32
	ProvingKey       groth16.ProvingKey
	VerifyingKey     groth16.VerifyingKey
	ConstraintSystem constraint.ConstraintSystem
}

const emptyLeaf = 0

type bitPatternLengthError struct {
	actualLength int
}

func (e *bitPatternLengthError) Error() string {
	return "Bit pattern length was " + strconv.Itoa(e.actualLength) + " not a total number of bytes"
}

// ProofRound gadget generates the ParentHash
type ProofRound struct {
	Direction frontend.Variable
	Hash      frontend.Variable
	Sibling   frontend.Variable
}

func (gadget ProofRound) DefineGadget(api abstractor.API) interface{} {
	api.AssertIsBoolean(gadget.Direction)
	d1 := api.Select(gadget.Direction, gadget.Hash, gadget.Sibling)
	d2 := api.Select(gadget.Direction, gadget.Sibling, gadget.Hash)
	sum := extractor.Call(api, poseidon.Poseidon2{In1: d1, In2: d2})
	return sum
}

// VerifyProof recovers the Merkle Tree using Proof[] and Path[] and returns the tree Root
// Proof[0] corresponds to the Leaf which is why len(Proof) === len(Path) + 1
type VerifyProof struct {
	Proof []frontend.Variable
	Path  []frontend.Variable
}

func (gadget VerifyProof) DefineGadget(api abstractor.API) interface{} {
	sum := gadget.Proof[0]
	for i := 1; i < len(gadget.Proof); i++ {
		sum = extractor.Call(api, ProofRound{Direction: gadget.Path[i-1], Hash: gadget.Proof[i], Sibling: sum})
	}
	return sum
}

type InsertionRound struct {
	Index    frontend.Variable
	Item     frontend.Variable
	PrevRoot frontend.Variable
	Proof    []frontend.Variable

	Depth int
}

func (gadget InsertionRound) DefineGadget(api abstractor.API) interface{} {
	currentPath := api.ToBinary(gadget.Index, gadget.Depth)

	// len(circuit.MerkleProofs) === circuit.BatchSize
	// len(circuit.MerkleProofs[i]) === circuit.Depth
	// len(circuit.IdComms) === circuit.BatchSize
	// Verify proof for empty leaf.
	proof := append([]frontend.Variable{emptyLeaf}, gadget.Proof[:]...)
	root := extractor.Call(api, VerifyProof{Proof: proof, Path: currentPath})
	api.AssertIsEqual(root, gadget.PrevRoot)

	// Verify proof for idComm.
	proof = append([]frontend.Variable{gadget.Item}, gadget.Proof[:]...)
	root = extractor.Call(api, VerifyProof{Proof: proof, Path: currentPath})

	return root
}

type InsertionProof struct {
	StartIndex frontend.Variable
	PreRoot    frontend.Variable
	IdComms    []frontend.Variable

	MerkleProofs [][]frontend.Variable

	BatchSize int
	Depth     int
}

func (gadget InsertionProof) DefineGadget(api abstractor.API) interface{} {
	prevRoot := gadget.PreRoot

	// Individual insertions.
	for i := 0; i < gadget.BatchSize; i += 1 {
		currentIndex := api.Add(gadget.StartIndex, i)
		prevRoot = extractor.Call(api, InsertionRound{
			Index: currentIndex,
			Item: gadget.IdComms[i],
			PrevRoot: prevRoot,
			Proof: gadget.MerkleProofs[i],
			Depth: gadget.Depth,
		})
	}

	return prevRoot
}

type DeletionRound struct {
	Root          frontend.Variable
	Index         frontend.Variable
	Item          frontend.Variable
	MerkleProofs  []frontend.Variable

	Depth         int
}

func (gadget DeletionRound) DefineGadget(api abstractor.API) interface{} {
	// We verify that the Leaf belongs to the Merkle Tree by verifying that the computed root
	// matches gadget.Root. Then, we return the root computed with Leaf being empty.
	currentPath := api.ToBinary(gadget.Index, gadget.Depth+1)
	// Treating indices with the one-too-high bit set as a skip flag. This allows
	// us to pad batches with meaningless ops to commit something even if there
	// isn't enough deletions happening to fill a batch.
	skipFlag := currentPath[gadget.Depth]
	currentPath = currentPath[:gadget.Depth]

	// Verify proof for Item.
	rootPreDeletion := extractor.Call(api, VerifyProof{append([]frontend.Variable{gadget.Item}, gadget.MerkleProofs[:]...), currentPath})

	// Verify proof for empty leaf.
	rootPostDeletion := extractor.Call(api, VerifyProof{append([]frontend.Variable{emptyLeaf}, gadget.MerkleProofs[:]...), currentPath})

	preRootCorrect := api.IsZero(api.Sub(rootPreDeletion, gadget.Root))
	preRootCorrectOrSkip := api.Or(preRootCorrect, skipFlag)
	api.AssertIsEqual(preRootCorrectOrSkip, 1)

	// Set root for next iteration.
	root := api.Select(skipFlag, gadget.Root, rootPostDeletion) // If skipFlag is set, we don't update the root.
	return root
}

type DeletionProof struct {
	DeletionIndices []frontend.Variable
	PreRoot         frontend.Variable
	IdComms         []frontend.Variable
	MerkleProofs    [][]frontend.Variable

	BatchSize int
	Depth     int
}

func (gadget DeletionProof) DefineGadget(api abstractor.API) interface{} {
	// Actual batch merkle proof verification.
	root := gadget.PreRoot

	// Individual deletions.
	for i := 0; i < gadget.BatchSize; i += 1 {
		// Set root for next iteration.
		root = extractor.Call(api, DeletionRound{
			Root: root,
			Index: gadget.DeletionIndices[i],
			Item: gadget.IdComms[i],
			MerkleProofs: gadget.MerkleProofs[i],
			Depth: gadget.Depth,
		})
	}

	return root
}

type CheckBitOne struct {
	Failed frontend.Variable
	Succeeded frontend.Variable
	Input frontend.Variable
}

func (g CheckBitOne) DefineGadget(api abstractor.API) interface{} {
	api.AssertIsBoolean(g.Input)
	bitNeg := api.Sub(1, g.Input)
	// if number isn't already > R, a 0 in this position means it's < R
	g.Succeeded = api.Select(g.Failed, 0, api.Or(bitNeg, g.Succeeded))
	return []frontend.Variable{g.Failed, g.Succeeded}
}

type CheckBitZero struct {
	Failed frontend.Variable
	Succeeded frontend.Variable
	Input frontend.Variable
}

func (g CheckBitZero) DefineGadget(api abstractor.API) interface{} {
	api.AssertIsBoolean(g.Input)
	// if number is not already < R, a 1 in this position means it's > R
	g.Failed = api.Select(g.Succeeded, 0, api.Or(g.Input, g.Failed))
	return []frontend.Variable{g.Failed, g.Succeeded}
}

// ReducedModRCheck Checks a little-endian array of bits asserting that it represents a number that
// is less than the field modulus R.
type ReducedModRCheck struct {
	Input []frontend.Variable
}

func (r ReducedModRCheck) DefineGadget(api abstractor.API) interface{} {
	field := api.Compiler().Field()
	if len(r.Input) < field.BitLen() {
		// input is shorter than the field, so it's definitely reduced
		return []frontend.Variable{}
	}
	var failed frontend.Variable = 0    // we already know number is > R
	var succeeded frontend.Variable = 0 // we already know number is < R
	for i := len(r.Input) - 1; i >= 0; i-- {
		var check_bit []frontend.Variable
		if field.Bit(i) == 0 {
			check_bit = extractor.Call1(api, CheckBitZero{failed, succeeded, r.Input[i]})
		} else {
			check_bit = extractor.Call1(api, CheckBitOne{failed, succeeded, r.Input[i]})
		}
		failed = check_bit[0]
		succeeded = check_bit[1]
	}
	api.AssertIsEqual(succeeded, 1)
	return []frontend.Variable{}
}

// ToReducedBinaryBigEndian converts the provided variable to the corresponding bit
// pattern using big-endian byte ordering. It also makes sure to pick the smallest
// binary representation (i.e. one that is reduced modulo scalar field order).
type ToReducedBigEndian struct {
	Variable frontend.Variable

	Size int
}

func (gadget ToReducedBigEndian) DefineGadget(api abstractor.API) interface{} {
	bitsLittleEndian := api.ToBinary(gadget.Variable, gadget.Size)
	extractor.CallVoid(api, ReducedModRCheck{Input: bitsLittleEndian})

	// Swapping Endianness
	// It does not introduce any new circuit constraints as it simply moves the
	// variables (that will later be instantiated to bits) around in the slice to
	// change the byte ordering. It has been verified to be a constraint-neutral
	// operation, so please maintain this invariant when modifying it.
	var newBits []frontend.Variable
	for i := len(bitsLittleEndian) - 8; i >= 0; i -= 8 {
		currentBytes := bitsLittleEndian[i : i+8]
		newBits = append(newBits, currentBytes...)
	}
	return newBits
}

// FromBinaryBigEndian converts the provided bit pattern that uses big-endian
// byte ordering to a variable that uses little-endian byte ordering.
type FromBinaryBigEndian struct {
	Variable []frontend.Variable
}

func (gadget FromBinaryBigEndian) DefineGadget(api abstractor.API) interface{} {
	// Swapping Endianness
	// It does not introduce any new circuit constraints as it simply moves the
	// variables (that will later be instantiated to bits) around in the slice to
	// change the byte ordering. It has been verified to be a constraint-neutral
	// operation, so please maintain this invariant when modifying it.
	var newBits []frontend.Variable
	for i := len(gadget.Variable) - 8; i >= 0; i -= 8 {
		currentBytes := gadget.Variable[i : i+8]
		newBits = append(newBits, currentBytes...)
	}
	return api.FromBinary(newBits...)
}

func toBytesLE(b []byte) []byte {
	for i := 0; i < len(b)/2; i++ {
		b[i], b[len(b)-i-1] = b[len(b)-i-1], b[i]
	}
	return b
}

func (ps *ProvingSystem) ExportSolidity(writer io.Writer) error {
	return ps.VerifyingKey.ExportSolidity(writer)
}
