package field_utils

import "github.com/consensys/gnark/std/math/emulated"

// Exp raises base to the exponent in the given prime field.
//
// field - given prime field where base and the result belong.
// base - the number in the field to be risen to the given exponent.
// exponent - an integer to rise base to.
func Exp[T emulated.FieldParams](
	field *emulated.Field[T], base *emulated.Element[T], exponent int,
) *emulated.Element[T] {
	res := field.One()
	for exponent > 0 {
		if exponent%2 == 1 {
			res = field.Mul(res, base)
		}
		base = field.Mul(base, base)
		exponent /= 2
	}
	return res
}
