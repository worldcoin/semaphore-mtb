package keccak

import (
	"math"

	"github.com/consensys/gnark/frontend"
	"github.com/reilabs/gnark-lean-extractor/v3/abstractor"
)

// Implemention of the Keccak in gnark following the specification of the Keccak team
// https://keccak.team/keccak_specs_summary.html

const laneSize = 64
const stateSize = 5
const blockSize = 1088
const domainSeparatorSize = 8

func NewKeccak256(api frontend.API, inputSize int, data ...frontend.Variable) []frontend.Variable {
	hash := abstractor.Call1(api, KeccakGadget{
		InputSize:       inputSize,
		InputData:       data,
		OutputSize:      256,
		Rounds:          24,
		BlockSize:       blockSize,
		RotationOffsets: R,
		RoundConstants:  RC,
		Domain:          0x01,
	})
	return hash
}

func NewSHA3_256(api frontend.API, inputSize int, data ...frontend.Variable) []frontend.Variable {
	hash := abstractor.Call1(api, KeccakGadget{
		InputSize:       inputSize,
		InputData:       data,
		OutputSize:      256,
		Rounds:          24,
		BlockSize:       blockSize,
		RotationOffsets: R,
		RoundConstants:  RC,
		Domain:          0x06,
	})
	return hash
}

func allZeroes(v []frontend.Variable) bool {
	for _, v := range v {
		if v != 0 {
			return false
		}
	}
	return true
}

type KeccakRound struct {
	A               [][][]frontend.Variable
	RC              [laneSize]frontend.Variable
	RotationOffsets [5][5]int
}

func (g KeccakRound) DefineGadget(api frontend.API) interface{} {
	// C[x] = A[x,0] xor A[x,1] xor A[x,2] xor A[x,3] xor A[x,4], for x in 0…4
	C := make([][]frontend.Variable, stateSize)
	for i := 0; i < int(stateSize); i++ {
		C[i] = make([]frontend.Variable, laneSize)
	}

	for x := 0; x < stateSize; x += 1 {
		C[x] = abstractor.Call1(api, Xor5{g.A[x][0], g.A[x][1], g.A[x][2], g.A[x][3], g.A[x][4]})
	}

	// D[x] = C[x-1] xor rot(C[x+1],1), for x in 0…4
	D := make([][]frontend.Variable, stateSize)
	for i := 0; i < int(stateSize); i++ {
		D[i] = make([]frontend.Variable, laneSize)
	}
	for x := 0; x < stateSize; x += 1 {
		tmp := abstractor.Call1(api, Rot{C[(x+1)%stateSize], 1})
		D[x] = abstractor.Call1(api, Xor{C[(x+4)%stateSize], tmp})
	}

	// A[x,y] = A[x,y] xor D[x], for x in 0…4 and y in 0…4
	for x := 0; x < stateSize; x += 1 {
		for y := 0; y < stateSize; y += 1 {
			g.A[x][y] = abstractor.Call1(api, Xor{g.A[x][y], D[x]})
		}
	}

	// B[y,2*x+3*y] = rot(A[x,y], r[x,y]), for (x,y) in (0…4,0…4)
	B := make([][][]frontend.Variable, stateSize)
	for x := 0; x < int(stateSize); x++ {
		B[x] = make([][]frontend.Variable, stateSize)
		for y := 0; y < int(stateSize); y++ {
			B[x][y] = make([]frontend.Variable, laneSize)
		}
	}
	for x := 0; x < stateSize; x += 1 {
		for y := 0; y < stateSize; y += 1 {
			B[y][(2*x+3*y)%stateSize] = abstractor.Call1(api, Rot{g.A[x][y], g.RotationOffsets[x][y]})
		}
	}

	// A[x,y] = B[x,y] xor ((not B[x+1,y]) and B[x+2,y]), for x in 0…4 and y in 0…4
	for x := 0; x < stateSize; x += 1 {
		for y := 0; y < stateSize; y += 1 {
			left := abstractor.Call1(api, Not{B[(x+1)%stateSize][y]})
			right := B[(x+2)%stateSize][y]
			tmp := abstractor.Call1(api, And{left, right})
			g.A[x][y] = abstractor.Call1(api, Xor{B[x][y], tmp})
		}
	}

	// A[0,0] = A[0,0] xor RC
	g.A[0][0] = abstractor.Call1(api, Xor{g.A[0][0], g.RC[:]})

	return g.A
}

type KeccakF struct {
	A               [][][]frontend.Variable
	Rounds          int
	RotationOffsets [5][5]int
	RoundConstants  [24][64]frontend.Variable
}

func (g KeccakF) DefineGadget(api frontend.API) interface{} {
	for i := 0; i < g.Rounds; i += 1 {
		g.A = abstractor.Call3(api, KeccakRound{
			A:               g.A,
			RC:              g.RoundConstants[i],
			RotationOffsets: g.RotationOffsets,
		})
	}
	return g.A
}

type KeccakGadget struct {
	InputSize       int
	InputData       []frontend.Variable
	OutputSize      int
	Rounds          int
	BlockSize       int
	RotationOffsets [5][5]int
	RoundConstants  [24][64]frontend.Variable
	Domain          int
}

func (g KeccakGadget) DefineGadget(api frontend.API) interface{} {
	// Padding
	paddedSize := int(math.Ceil(float64(g.InputSize+domainSeparatorSize)/float64(g.BlockSize))) * g.BlockSize
	if len(g.InputData) == 0 {
		paddedSize = g.BlockSize
	}

	P := make([]frontend.Variable, paddedSize)
	for i := 0; i < len(g.InputData); i += 1 {
		P[i] = g.InputData[i]
	}

	// write domain separator
	for i := 0; i < domainSeparatorSize; i += 1 {
		P[i+len(g.InputData)] = (g.Domain >> i) & 1
	}

	// fill with zero bytes
	for i := len(g.InputData) + domainSeparatorSize; i < len(P); i += 1 {
		P[i] = 0
	}

	tmp := make([]frontend.Variable, len(P))
	for i := 0; i < len(P)-1; i += 1 {
		tmp[i] = 0
	}
	// set last byte to 0x80
	tmp[len(P)-1] = 1

	for i := 0; i < len(P); i += 1 {
		if tmp[i] != 0 {
			P[i] = api.Xor(P[i], tmp[i])
		}
	}

	// Initialization
	S := make([][][]frontend.Variable, stateSize)
	for x := 0; x < int(stateSize); x++ {
		S[x] = make([][]frontend.Variable, stateSize)
		for y := 0; y < int(stateSize); y++ {
			S[x][y] = make([]frontend.Variable, laneSize)
		}
	}

	for i := 0; i < stateSize; i += 1 {
		for j := 0; j < stateSize; j += 1 {
			for k := 0; k < laneSize; k += 1 {
				S[i][j][k] = 0
			}
		}
	}

	// Absorbing phase
	for i := 0; i < len(P); i += g.BlockSize {
		for x := 0; x < stateSize; x += 1 {
			for y := 0; y < stateSize; y += 1 {
				if x+5*y < g.BlockSize/laneSize {
					//var Pi [laneSize]frontend.Variable
					Pi := make([]frontend.Variable, laneSize)
					copy(Pi[:], P[i+(x+5*y)*laneSize:i+(x+5*y+1)*laneSize])
					if allZeroes(S[x][y]) {
						S[x][y] = Pi
						continue
					}
					if allZeroes(Pi) {
						continue
					}
					S[x][y] = abstractor.Call1(api, Xor{S[x][y], Pi})
				}
			}
		}
		S = abstractor.Call3(api, KeccakF{
			A:               S,
			Rounds:          g.Rounds,
			RotationOffsets: g.RotationOffsets,
			RoundConstants:  g.RoundConstants,
		})
	}

	// Squeezing phase
	var Z []frontend.Variable
	i := 0
	for i < g.OutputSize {
		for x := 0; x < stateSize; x += 1 {
			for y := 0; y < stateSize; y += 1 {
				if i < g.OutputSize && x+5*y < g.BlockSize/laneSize {
					Z = append(Z, S[y][x][:]...)
					i += laneSize
				}
			}
		}
		if i < g.OutputSize-laneSize {
			S = abstractor.Call3(api, KeccakF{
				A:               S,
				Rounds:          g.Rounds,
				RotationOffsets: g.RotationOffsets,
				RoundConstants:  g.RoundConstants,
			})
		}
	}

	return Z
}

///////////////////////////////////////////////////////////////////////////////////////////
/// Helpers for various binary operations
///////////////////////////////////////////////////////////////////////////////////////////

type Xor5Round struct {
	A frontend.Variable
	B frontend.Variable
	C frontend.Variable
	D frontend.Variable
	E frontend.Variable
}

func (g Xor5Round) DefineGadget(api frontend.API) interface{} {
	tmp_ab := api.Xor(g.A, g.B)
	tmp_abc := api.Xor(g.C, tmp_ab)
	tmp_abcd := api.Xor(g.D, tmp_abc)
	xor := api.Xor(g.E, tmp_abcd)
	return xor
}

type Xor5 struct {
	A []frontend.Variable
	B []frontend.Variable
	C []frontend.Variable
	D []frontend.Variable
	E []frontend.Variable
}

func (g Xor5) DefineGadget(api frontend.API) interface{} {
	var c [laneSize]frontend.Variable
	for i := 0; i < len(g.A); i += 1 {
		c[i] = abstractor.Call(api, Xor5Round{g.A[i], g.B[i], g.C[i], g.D[i], g.E[i]})
	}
	return c[:]
}

type Xor struct {
	A []frontend.Variable
	B []frontend.Variable
}

func (g Xor) DefineGadget(api frontend.API) interface{} {
	var c [laneSize]frontend.Variable
	for i := 0; i < len(g.A); i += 1 {
		c[i] = api.Xor(g.A[i], g.B[i])
	}
	return c[:]
}

type Rot struct {
	A []frontend.Variable
	R int
}

func (g Rot) DefineGadget(api frontend.API) interface{} {
	var c [laneSize]frontend.Variable
	for i := 0; i < len(g.A); i += 1 {
		c[i] = g.A[(i+(laneSize-g.R))%len(g.A)]
	}
	return c[:]
}

type And struct {
	A []frontend.Variable
	B []frontend.Variable
}

func (g And) DefineGadget(api frontend.API) interface{} {
	var c [laneSize]frontend.Variable
	for i := 0; i < len(g.A); i += 1 {
		c[i] = api.And(g.A[i], g.B[i])
	}
	return c[:]
}

type Not struct {
	A []frontend.Variable
}

func (g Not) DefineGadget(api frontend.API) interface{} {
	var c [laneSize]frontend.Variable
	for i := 0; i < len(g.A); i += 1 {
		c[i] = api.Sub(1, g.A[i])
	}
	return c[:]
}
