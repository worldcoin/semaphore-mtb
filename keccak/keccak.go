package keccak

import "github.com/consensys/gnark/frontend"

// Implemention of the Keccak in gnark following the specification of the Keccak team
// https://keccak.team/keccak_specs_summary.html

const laneSize = 64
const stateSize = 5

func keccakf(api frontend.API, A [stateSize][stateSize][laneSize]frontend.Variable) [stateSize][stateSize][laneSize]frontend.Variable {
	for i := 0; i < 24; i += 1 {
		A = round(api, A, RC[i])
	}
	return A
}

func round(api frontend.API, A [stateSize][stateSize][laneSize]frontend.Variable, RC [laneSize]frontend.Variable) [stateSize][stateSize][laneSize]frontend.Variable {
	// C[x] = A[x,0] xor A[x,1] xor A[x,2] xor A[x,3] xor A[x,4], for x in 0…4
	var C [stateSize][laneSize]frontend.Variable
	for x := 0; x < stateSize; x += 1 {
		C[x] = xor(api, A[x][0], A[x][1])
		C[x] = xor(api, C[x], A[x][2])
		C[x] = xor(api, C[x], A[x][3])
		C[x] = xor(api, C[x], A[x][4])
	}

	// D[x] = C[x-1] xor rot(C[x+1],1), for x in 0…4
	var D [stateSize][laneSize]frontend.Variable
	for x := 0; x < stateSize; x += 1 {
		tmp := rot(api, C[x+1], 1)
		D[x] = xor(api, C[x-1], tmp)
	}

	// A[x,y] = A[x,y] xor D[x], for x in 0…4 and y in 0…4
	for x := 0; x < stateSize; x += 1 {
		for y := 0; y < stateSize; y += 1 {
			A[x][y] = xor(api, A[x][y], D[x])
		}
	}

	// B[y,2*x+3*y] = rot(A[x,y], r[x,y]), for (x,y) in (0…4,0…4)
	var B [stateSize][5 * stateSize][laneSize]frontend.Variable
	for x := 0; x < stateSize; x += 1 {
		for y := 0; y < stateSize; y += 1 {
			B[y][2*x+3*y] = rot(api, A[x][y], R[x][y])
		}
	}

	// A[x,y] = B[x,y] xor ((not B[x+1,y]) and B[x+2,y]), for x in 0…4 and y in 0…4
	for x := 0; x < stateSize; x += 1 {
		for y := 0; y < stateSize; y += 1 {
			tmp := and(api, not(api, B[x+1][y]), B[x+2][y])
			A[x][y] = xor(api, B[x][y], tmp)
		}
	}

	// A[0,0] = A[0,0] xor RC
	A[0][0] = xor(api, A[0][0], RC)

	return A
}

// TODO: rest of keccak
// ...

///////////////////////////////////////////////////////////////////////////////////////////
/// Helpers for various binary operations
///////////////////////////////////////////////////////////////////////////////////////////

func xor(api frontend.API, a, b [laneSize]frontend.Variable) [laneSize]frontend.Variable {
	var c [laneSize]frontend.Variable
	for i := 0; i < laneSize; i += 1 {
		c[i] = api.Xor(a[i], b[i])
	}
	return c
}

func rot(api frontend.API, a [laneSize]frontend.Variable, r int) [laneSize]frontend.Variable {
	var c [laneSize]frontend.Variable
	for i := 0; i < laneSize; i += 1 {
		c[i] = a[(i+r)%laneSize]
	}
	return c
}

func and(api frontend.API, a, b [laneSize]frontend.Variable) [laneSize]frontend.Variable {
	var c [laneSize]frontend.Variable
	for i := 0; i < laneSize; i += 1 {
		c[i] = api.And(a[i], b[i])
	}
	return c
}

func not(api frontend.API, a [laneSize]frontend.Variable) [laneSize]frontend.Variable {
	var c [laneSize]frontend.Variable
	for i := 0; i < laneSize; i += 1 {
		c[i] = api.Neg(a[i])
	}
	return c
}
