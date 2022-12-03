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
	h := NewKeccak256(api, len(circuit.Input))
	h.Write(circuit.Input[:]...)
	sum := api.FromBinary(h.Sum()...)
	api.AssertIsEqual(circuit.Hash, sum)
	return nil
}

type TestKeccakCircuit2 struct {
	Input [0]frontend.Variable `gnark:"input"`
	Hash  frontend.Variable    `gnark:",public"`
}

func (circuit *TestKeccakCircuit2) Define(api frontend.API) error {
	h := NewKeccak256(api, 0)
	sum := api.FromBinary(h.Sum()...)
	api.AssertIsEqual(circuit.Hash, sum)
	return nil
}

type TestSHACircuit struct {
	Input [0]frontend.Variable `gnark:"input"`
	Hash  frontend.Variable    `gnark:",public"`
}

func (circuit *TestSHACircuit) Define(api frontend.API) error {
	h := NewSHA3_256(api, 0)
	sum := api.FromBinary(h.Sum()...)
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

	// SHA3: hash empty input
	var circuit3 TestSHACircuit
	assert.ProverSucceeded(&circuit3, &TestSHACircuit{
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
	return bi
}
