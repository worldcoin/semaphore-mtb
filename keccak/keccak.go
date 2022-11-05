package keccak

import (
	"github.com/consensys/gnark/frontend"
)

// Implemention of the Keccak in gnark following the specification of the Keccak team
// https://keccak.team/keccak_specs_summary.html

const laneSize = 64
const stateSize = 5
const blockSize = 1088
const d = 0x01
const outSize = 256

func rev(a []frontend.Variable) []frontend.Variable {
	numbers := make([]frontend.Variable, len(a))
	copy(numbers, a)
	for i, j := 0, len(numbers)-1; i < j; i, j = i+1, j-1 {
		numbers[i], numbers[j] = numbers[j], numbers[i]
	}
	return numbers
}

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
		tmp := rot(api, C[(x+1)%stateSize], 1)
		D[x] = xor(api, C[(x+4)%stateSize], tmp)
	}

	// A[x,y] = A[x,y] xor D[x], for x in 0…4 and y in 0…4
	for x := 0; x < stateSize; x += 1 {
		for y := 0; y < stateSize; y += 1 {
			A[x][y] = xor(api, A[x][y], D[x])
		}
	}

	// B[y,2*x+3*y] = rot(A[x,y], r[x,y]), for (x,y) in (0…4,0…4)
	var B [stateSize][stateSize][laneSize]frontend.Variable
	for x := 0; x < stateSize; x += 1 {
		for y := 0; y < stateSize; y += 1 {
			B[y][(2*x+3*y)%stateSize] = rot(api, A[x][y], R[x][y])
		}
	}

	// A[x,y] = B[x,y] xor ((not B[x+1,y]) and B[x+2,y]), for x in 0…4 and y in 0…4
	for x := 0; x < stateSize; x += 1 {
		for y := 0; y < stateSize; y += 1 {
			tmp := and(api, not(api, B[(x+1)%stateSize][y]), B[(x+2)%stateSize][y])
			A[x][y] = xor(api, B[x][y], tmp)
		}
	}

	// A[0,0] = A[0,0] xor RC
	A[0][0] = xor(api, A[0][0], RC)

	return A
}

func Keccak(api frontend.API, inputBits []frontend.Variable) [outSize]frontend.Variable {
	// Padding
	// api.Println(len(inputBits))
	P := make([]frontend.Variable, blockSize)
	P[0] = 0
	P[1] = 0
	P[2] = 0
	P[3] = 0
	P[4] = 0
	P[5] = 0
	P[6] = 0
	P[7] = 0

	// for i := 0; i < len(inputBits); i += 1 {
	// 	P[i] = inputBits[i]
	// }

	// if len(inputBits)%blockSize != 0 {
	for i := 8; i < len(P); i += 1 {
		P[i] = 0
	}
	P[8] = 1
	// }

	tmp := make([]frontend.Variable, len(P))
	for i := 0; i < len(P); i += 1 {
		tmp[i] = 0
	}
	tmp[len(P)-1] = 1

	for i := 0; i < len(P); i += 1 {
		P[i] = api.Xor(P[i], tmp[i])
	}

	// Initialization
	var S [stateSize][stateSize][laneSize]frontend.Variable
	for i := 0; i < stateSize; i += 1 {
		for j := 0; j < stateSize; j += 1 {
			for k := 0; k < laneSize; k += 1 {
				S[i][j][k] = 0
			}
		}
	}

	// Absorbing phase
	for i := 0; i < len(P); i += blockSize {
		for x := 0; x < stateSize; x += 1 {
			for y := 0; y < stateSize; y += 1 {
				if x+5*y < blockSize/laneSize {
					var Pi [laneSize]frontend.Variable
					for k := i + (x+5*y)*laneSize; k < i+(x+5*y+1)*laneSize; k += 1 {
						Pi[k-(i+(x+5*y)*laneSize)] = P[k]
					}
					S[x][y] = xor(api, S[x][y], Pi)
				}
			}
		}
		// api.Println(S[1][3][:]...)
		S = keccakf(api, S)
	}

	// Squeezing phase
	var Z [outSize]frontend.Variable
	i := 0
	for i < outSize {
		for x := 0; x < stateSize; x += 1 {
			for y := 0; y < stateSize; y += 1 {
				if i < outSize && x+5*y < blockSize/laneSize {
					copy(Z[i:], S[y][x][:])
					i += laneSize
				}
			}
		}
	}
	api.Println(rev(Z[:])...)
	return Z
}

///////////////////////////////////////////////////////////////////////////////////////////
/// Helpers for various binary operations
///////////////////////////////////////////////////////////////////////////////////////////

func xor(api frontend.API, a, b [laneSize]frontend.Variable) [laneSize]frontend.Variable {
	var c [laneSize]frontend.Variable
	for i := 0; i < len(a); i += 1 {
		c[i] = api.Xor(a[i], b[i])
	}
	return c
}

func rot(api frontend.API, a [laneSize]frontend.Variable, r int) [laneSize]frontend.Variable {
	var c [laneSize]frontend.Variable
	for i := 0; i < len(a); i += 1 {
		c[i] = a[(i+(laneSize-r))%len(a)]
	}
	return c
}

func and(api frontend.API, a, b [laneSize]frontend.Variable) [laneSize]frontend.Variable {
	var c [laneSize]frontend.Variable
	for i := 0; i < len(a); i += 1 {
		c[i] = api.And(a[i], b[i])
	}
	return c
}

func not(api frontend.API, a [laneSize]frontend.Variable) [laneSize]frontend.Variable {
	var c [laneSize]frontend.Variable
	for i := 0; i < len(a); i += 1 {
		c[i] = api.Sub(1, a[i])
	}
	return c
}
