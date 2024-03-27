package keccak

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

type TestKeccakCircuit1 struct {
	Input [8]frontend.Variable `gnark:"input"`
	Hash  frontend.Variable    `gnark:",public"`
}

func (circuit *TestKeccakCircuit1) Define(api frontend.API) error {
	hash, err := Keccak256(api, len(circuit.Input), circuit.Input[:]...)
	if err != nil {
		return err
	}
	sum := api.FromBinary(hash...)
	api.AssertIsEqual(circuit.Hash, sum)
	return nil
}

type TestKeccakCircuit2 struct {
	Input [0]frontend.Variable `gnark:"input"`
	Hash  frontend.Variable    `gnark:",public"`
}

func (circuit *TestKeccakCircuit2) Define(api frontend.API) error {
	hash, err := Keccak256(api, 0)
	if err != nil {
		return err
	}
	sum := api.FromBinary(hash...)
	api.AssertIsEqual(circuit.Hash, sum)
	return nil
}

type TestKeccakCircuitBlockSize struct {
	Input [blockSize]frontend.Variable `gnark:"input"`
	Hash  frontend.Variable            `gnark:",public"`
}

func (circuit *TestKeccakCircuitBlockSize) Define(api frontend.API) error {
	hash, err := Keccak256(api, len(circuit.Input), circuit.Input[:]...)
	if err != nil {
		return err
	}
	sum := api.FromBinary(hash...)
	api.AssertIsEqual(circuit.Hash, sum)
	return nil
}

type TestSHACircuit struct {
	Input [0]frontend.Variable `gnark:"input"`
	Hash  frontend.Variable    `gnark:",public"`
}

func (circuit *TestSHACircuit) Define(api frontend.API) error {
	hash := NewSHA3_256(api, 0)
	sum := api.FromBinary(hash...)
	api.AssertIsEqual(circuit.Hash, sum)
	return nil
}

func TestKeccak(t *testing.T) {
	assert := test.NewAssert(t)

	// Keccak: hash zero byte
	var circuit1 TestKeccakCircuit1
	assert.ProverSucceeded(&circuit1, &TestKeccakCircuit1{
		Input: [8]frontend.Variable{0, 0, 0, 0, 0, 0, 0, 0},
		Hash:  bigIntLE("0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a"),
	}, test.WithBackends(backend.GROTH16), test.WithCurves(ecc.BN254))

	// Keccak: hash empty input
	var circuit2 TestKeccakCircuit2
	assert.ProverSucceeded(&circuit2, &TestKeccakCircuit2{
		Input: [0]frontend.Variable{},
		Hash:  bigIntLE("0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"),
	}, test.WithBackends(backend.GROTH16), test.WithCurves(ecc.BN254))

	// Keccak: input equal block size
	var circuit3 TestKeccakCircuitBlockSize
	var inputArray [1088]frontend.Variable
	fillArray(1, inputArray[:])
	assert.ProverSucceeded(
		&circuit3, &TestKeccakCircuitBlockSize{
			Input: inputArray,
			Hash:  bigIntLE("0x2d417340362cd4144efbf52adc1bfb7a4b40254f55f3b0f09efa6a1ef299b51a"),
		}, test.WithBackends(backend.GROTH16), test.WithCurves(ecc.BN254),
	)

	// SHA3: hash empty input
	var circuit4 TestSHACircuit
	assert.ProverSucceeded(&circuit4, &TestSHACircuit{
		Input: [0]frontend.Variable{},
		Hash:  bigIntLE("0xa7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"),
	}, test.WithBackends(backend.GROTH16), test.WithCurves(ecc.BN254))

}

// we need to feed in the hash in little endian
func bigIntLE(s string) big.Int {
	var bi big.Int
	bi.SetString(s, 0)

	b := bi.Bytes()
	for i := 0; i < len(b)/2; i++ {
		b[i], b[len(b)-i-1] = b[len(b)-i-1], b[i]
	}

	bi.SetBytes(b)

	// Reduce the number by BN254 group order, because the circuit does the same
	modulus, ok := new(big.Int).SetString(
		"21888242871839275222246405745257275088548364400416034343698204186575808495617", 10,
	)
	if !ok {
		panic("can't set big int to BN254 group order")
	}
	bi.Mod(&bi, modulus)

	return bi
}

// Fill an array with a specific value.
func fillArray(value int, inputArray []frontend.Variable) {
	for i := range inputArray {
		inputArray[i] = value
	}
}
