package keccak

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

type TestKeccakCircuit struct {
	Input []frontend.Variable `gnark:"input"`
	// Hash  [256]frontend.Variable `gnark:",public"`
}

func (circuit *TestKeccakCircuit) Define(api frontend.API) error {
	h := Keccak(api, circuit.Input)
	// api.AssertIsEqual(h, circuit.Hash)
	for i := 0; i < 8; i++ {
		h[i] = 0
	}
	// x := api.FromBinary(h[:]...)
	// api.Println(x)
	return nil
}

// TODO: tests obvsly still broken
func TestKeccak(t *testing.T) {
	assert := test.NewAssert(t)

	var circuit1 TestKeccakCircuit
	assert.ProverSucceeded(&circuit1, &TestKeccakCircuit{
		Input: []frontend.Variable{},
		// Hash:  out,
	}, test.WithBackends(backend.GROTH16), test.WithCurves(ecc.BN254))
}

func hex(s string) big.Int {
	var bi big.Int
	bi.SetString(s, 0)
	return bi
}
