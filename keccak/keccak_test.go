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
	Input frontend.Variable `gnark:"input"`
	Hash  frontend.Variable `gnark:",public"`
}

func (circuit *TestKeccakCircuit) Define(api frontend.API) error {
	return nil
}

// TODO: tests obvsly still broken
func TestPoseidon(t *testing.T) {
	assert := test.NewAssert(t)

	var circuit1 TestKeccakCircuit
	assert.ProverSucceeded(&circuit1, &TestKeccakCircuit{
		Input: 0,
		Hash:  hex("xxx"),
	}, test.WithBackends(backend.GROTH16), test.WithCurves(ecc.BN254))
}

func hex(s string) big.Int {
	var bi big.Int
	bi.SetString(s, 0)
	return bi
}
