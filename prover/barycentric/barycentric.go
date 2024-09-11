package barycentric

import (
	"github.com/consensys/gnark/std/math/emulated"

	"worldcoin/gnark-mbu/prover/field_utils"
)

// CalculateBarycentricFormula implements the evaluation of a polynomial in evaluation form at a point outside the
// domain, using barycentric interpolation. This function follows the formulation by Dankrad Feist, as described
// in his blog post: https://dankradfeist.de/ethereum/2021/06/18/pcs-multiproofs.html.
//
// The formula used for calculation is: ((z^d - 1) / d) * Σ((f_i * ω^i) / (z - ω^i)) for i=0 to d-1,
// where z is the target evaluation point, d is the degree of the polynomial, f_i are the polynomial coefficients,
// and ω^i are the domain elements.
//
// field - reference to the emulated field operations structure, used for arithmetic operations within the specified
// field.
// omegasToI - slice containing the powers of the primitive root of unity ω, raised to the power of index i,
// representing the domain elements.
// yNodes - slice containing the polynomial coefficients or the values of the polynomial at the domain elements.
// targetPoint - point outside the domain at which the polynomial is to be evaluated.
func CalculateBarycentricFormula[T emulated.FieldParams](
	field *emulated.Field[T], omegasToI, yNodes []emulated.Element[T], targetPoint emulated.Element[T],
) emulated.Element[T] {

	polynomialDegree := len(yNodes)

	// First term: (z^d - 1) / d
	zToD := field_utils.Exp(field, &targetPoint, polynomialDegree)
	firstTerm := *field.Sub(zToD, field.One())
	d := emulated.ValueOf[T](polynomialDegree)
	firstTerm = *field.Div(&firstTerm, &d)

	// Second term: Σ(f_i * ω^i)/(z - ω^i) from i=0 to d-1
	secondTerm := field.Zero()
	for i := range polynomialDegree {
		numerator := *field.Mul(&yNodes[i], &omegasToI[i])
		denominator := *field.Sub(&targetPoint, &omegasToI[i])
		term := *field.Div(&numerator, &denominator)
		secondTerm = field.Add(secondTerm, &term)
	}

	return *field.Mul(&firstTerm, secondTerm)
}
