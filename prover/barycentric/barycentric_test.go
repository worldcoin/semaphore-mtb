package barycentric

import (
	"math"
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/math/emulated"
	"github.com/consensys/gnark/test"
)

type BarycentricCircuit[T emulated.FieldParams] struct {
	Omega            big.Int // ω
	PolynomialDegree int

	// Inputs (private)
	YNodes      []emulated.Element[T] // len(YNodes) == PolynomialDegree
	TargetPoint emulated.Element[T]

	// Output
	InterpolatedPoint emulated.Element[T] `gnark:",public"`
}

func (circuit *BarycentricCircuit[T]) Define(api frontend.API) error {
	field, err := emulated.NewField[T](api)
	if err != nil {
		return err
	}

	api.AssertIsEqual(len(circuit.YNodes), circuit.PolynomialDegree)

	omegasToI := make([]emulated.Element[T], circuit.PolynomialDegree)
	omegaToI := big.NewInt(1)
	for i := range circuit.PolynomialDegree {
		omegasToI[i] = emulated.ValueOf[T](omegaToI)
		omegaToI.Mul(omegaToI, &circuit.Omega)
	}

	// Method under test
	interpolatedPointCalculated := CalculateBarycentricFormula[T](field, omegasToI, circuit.YNodes, circuit.TargetPoint)

	field.AssertIsEqual(&circuit.InterpolatedPoint, &interpolatedPointCalculated)

	return nil
}

func setupTestEnvironment(polynomialDegree int) (*big.Int, *big.Int) {
	// The test assumes BLS12381Fr field and a certain polynomial degree
	modulus, _ := new(big.Int).SetString(
		"52435875175126190479447740508185965837690552500527637822603658699938581184513", 10,
	)

	// For polynomial degree d = 4096 = 2^12:
	// ω^(2^32) = ω^(2^20 * 2^12)
	// Calculate ω^20 starting with root of unity of 2^32 degree
	omega, _ := new(big.Int).SetString(
		"10238227357739495823651030575849232062558860180284477541189508159991286009131", 10,
	)
	polynomialDegreeExp := int(math.Log2(float64(polynomialDegree)))
	omegaExpExp := 32 // ω^(2^32)
	for range omegaExpExp - polynomialDegreeExp {
		omega.Mul(omega, omega)
		omega.Mod(omega, modulus)
	}

	return omega, modulus
}

func TestCalculateBarycentricFormula(t *testing.T) {
	type Fr = emulated.BLS12381Fr
	const polynomialDegree = 4096
	omega, modulus := setupTestEnvironment(polynomialDegree)

	// Test cases
	type PolynomialTestCase[T emulated.FieldParams] struct {
		Name              string
		CalculateYNodes   func(omega *big.Int, modulus *big.Int, polynomialDegree int) []emulated.Element[T]
		TargetPoint       int64
		InterpolatedPoint int64
	}
	tests := []PolynomialTestCase[Fr]{
		{
			Name: "f(x) = x^3",
			CalculateYNodes: func(omega *big.Int, modulus *big.Int, polynomialDegree int) []emulated.Element[Fr] {
				y := make([]emulated.Element[Fr], polynomialDegree)
				for i := range y {
					res := new(big.Int).Exp(omega, big.NewInt(int64(i*3)), modulus)
					y[i] = emulated.ValueOf[Fr](res)
				}
				return y
			},
			TargetPoint:       3,
			InterpolatedPoint: 27,
		},
		{
			Name: "f(x) = 3x^7 + 2x^4 + 4x + 20",
			CalculateYNodes: func(omega *big.Int, modulus *big.Int, polynomialDegree int) []emulated.Element[Fr] {
				y := make([]emulated.Element[Fr], polynomialDegree)
				for i := range y {
					a := new(big.Int).Exp(omega, big.NewInt(int64(i*7)), modulus)
					a.Mul(a, big.NewInt(3))

					b := new(big.Int).Exp(omega, big.NewInt(int64(i*4)), modulus)
					b.Mul(b, big.NewInt(2))

					c := new(big.Int).Exp(omega, big.NewInt(int64(i)), modulus)
					c.Mul(c, big.NewInt(4))

					res := new(big.Int).Add(a, b)
					res.Add(res, c)
					res.Add(res, big.NewInt(20))
					res.Mod(res, modulus)

					y[i] = emulated.ValueOf[Fr](res)
				}
				return y
			},
			TargetPoint:       3,
			InterpolatedPoint: 6755,
		},
	}

	for _, tc := range tests {
		assert := test.NewAssert(t)
		assert.Run(
			func(a *test.Assert) {
				circuit := BarycentricCircuit[Fr]{
					Omega:            *omega,
					PolynomialDegree: polynomialDegree,
					YNodes:           make([]emulated.Element[Fr], polynomialDegree),
				}

				assignment := BarycentricCircuit[Fr]{
					YNodes:            tc.CalculateYNodes(omega, modulus, polynomialDegree),
					TargetPoint:       emulated.ValueOf[Fr](tc.TargetPoint),
					InterpolatedPoint: emulated.ValueOf[Fr](tc.InterpolatedPoint),
				}

				assert.CheckCircuit(
					&circuit, test.WithBackends(backend.GROTH16), test.WithCurves(ecc.BN254),
					test.WithValidAssignment(&assignment),
				)
			}, tc.Name,
		)
	}
}
