package keccak

import (
	"math"

	"github.com/consensys/gnark/frontend"
)

// Implemention of the Keccak in gnark following the specification of the Keccak team
// https://keccak.team/keccak_specs_summary.html

const laneSize = 64
const stateSize = 5

type Keccak struct {
	inputSize       int
	inputData       []frontend.Variable
	outputSize      int
	nRounds         int
	blockSize       int
	api             frontend.API
	rotationOffsets [5][5]int
	roundConstants  [24][64]frontend.Variable
	domain          int
}

func NewKeccak256(api frontend.API, inputSize int) Keccak {
	return Keccak{
		inputSize:       inputSize,
		inputData:       []frontend.Variable{},
		outputSize:      256,
		nRounds:         24,
		blockSize:       1088,
		api:             api,
		rotationOffsets: R,
		roundConstants:  RC,
		domain:          0x01,
	}
}

func NewSHA3_256(api frontend.API, inputSize int) Keccak {
	return Keccak{
		inputSize:       inputSize,
		inputData:       []frontend.Variable{},
		outputSize:      256,
		nRounds:         24,
		blockSize:       1088,
		api:             api,
		rotationOffsets: R,
		roundConstants:  RC,
		domain:          0x06,
	}
}

func (h *Keccak) keccakf(A [stateSize][stateSize][laneSize]frontend.Variable) [stateSize][stateSize][laneSize]frontend.Variable {
	for i := 0; i < h.nRounds; i += 1 {
		A = h.round(A, h.roundConstants[i])
	}
	return A
}

func (h *Keccak) round(A [stateSize][stateSize][laneSize]frontend.Variable, RC [laneSize]frontend.Variable) [stateSize][stateSize][laneSize]frontend.Variable {
	// C[x] = A[x,0] xor A[x,1] xor A[x,2] xor A[x,3] xor A[x,4], for x in 0…4
	var C [stateSize][laneSize]frontend.Variable
	for x := 0; x < stateSize; x += 1 {
		C[x] = xor(h.api, A[x][0], A[x][1])
		C[x] = xor(h.api, C[x], A[x][2])
		C[x] = xor(h.api, C[x], A[x][3])
		C[x] = xor(h.api, C[x], A[x][4])
	}

	// D[x] = C[x-1] xor rot(C[x+1],1), for x in 0…4
	var D [stateSize][laneSize]frontend.Variable
	for x := 0; x < stateSize; x += 1 {
		tmp := rot(h.api, C[(x+1)%stateSize], 1)
		D[x] = xor(h.api, C[(x+4)%stateSize], tmp)
	}

	// A[x,y] = A[x,y] xor D[x], for x in 0…4 and y in 0…4
	for x := 0; x < stateSize; x += 1 {
		for y := 0; y < stateSize; y += 1 {
			A[x][y] = xor(h.api, A[x][y], D[x])
		}
	}

	// B[y,2*x+3*y] = rot(A[x,y], r[x,y]), for (x,y) in (0…4,0…4)
	var B [stateSize][stateSize][laneSize]frontend.Variable
	for x := 0; x < stateSize; x += 1 {
		for y := 0; y < stateSize; y += 1 {
			B[y][(2*x+3*y)%stateSize] = rot(h.api, A[x][y], h.rotationOffsets[x][y])
		}
	}

	// A[x,y] = B[x,y] xor ((not B[x+1,y]) and B[x+2,y]), for x in 0…4 and y in 0…4
	for x := 0; x < stateSize; x += 1 {
		for y := 0; y < stateSize; y += 1 {
			tmp := and(h.api, not(h.api, B[(x+1)%stateSize][y]), B[(x+2)%stateSize][y])
			A[x][y] = xor(h.api, B[x][y], tmp)
		}
	}

	// A[0,0] = A[0,0] xor RC
	A[0][0] = xor(h.api, A[0][0], RC)

	return A
}

func (h *Keccak) Sum() []frontend.Variable {
	// Padding
	paddingSize := int(math.Ceil(float64(h.inputSize)/float64(h.blockSize))) * h.blockSize
	if len(h.inputData) == 0 {
		paddingSize = h.blockSize
	}

	P := make([]frontend.Variable, paddingSize)
	for i := 0; i < len(h.inputData); i += 1 {
		P[i] = h.inputData[i]
	}

	// write domain separator
	for i := 0; i < 8; i += 1 {
		P[i+len(h.inputData)] = (h.domain >> i) & 1
	}

	// fill with zero bytes
	for i := len(h.inputData) + 8; i < len(P); i += 1 {
		P[i] = 0
	}

	tmp := make([]frontend.Variable, len(P))
	for i := 0; i < len(P)-1; i += 1 {
		tmp[i] = 0
	}
	// set last byte to 0x80
	tmp[len(P)-1] = 1

	for i := 0; i < len(P); i += 1 {
		P[i] = h.api.Xor(P[i], tmp[i])
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
	for i := 0; i < len(P); i += h.blockSize {
		for x := 0; x < stateSize; x += 1 {
			for y := 0; y < stateSize; y += 1 {
				if x+5*y < h.blockSize/laneSize {
					var Pi [laneSize]frontend.Variable
					copy(Pi[:], P[i+(x+5*y)*laneSize:i+(x+5*y+1)*laneSize])
					S[x][y] = xor(h.api, S[x][y], Pi)
				}
			}
		}
		S = h.keccakf(S)
	}

	// Squeezing phase
	var Z []frontend.Variable
	i := 0
	for i < h.outputSize {
		for x := 0; x < stateSize; x += 1 {
			for y := 0; y < stateSize; y += 1 {
				if i < h.outputSize && x+5*y < h.blockSize/laneSize {
					Z = append(Z, S[y][x][:]...)
					i += laneSize
				}
			}
		}
		if i < h.outputSize-laneSize {
			S = h.keccakf(S)
		}
	}

	return Z
}

func (h *Keccak) Write(data ...frontend.Variable) {
	h.inputData = append(h.inputData, data...)
}

func (h *Keccak) Reset() {
	h.inputData = []frontend.Variable{0}
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
