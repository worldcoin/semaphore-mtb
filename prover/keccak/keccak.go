package keccak

import (
	"fmt"
	"math"

	"github.com/consensys/gnark/frontend"
	"github.com/reilabs/gnark-lean-extractor/abstractor"
)

// Implemention of the Keccak in gnark following the specification of the Keccak team
// https://keccak.team/keccak_specs_summary.html

const laneSize = 64
const stateSize = 5

func NewKeccak256(api abstractor.API, inputSize int, data ...frontend.Variable) []frontend.Variable {
	hash := api.Call(KeccakGadget{
		InputSize: inputSize,
		InputData: data,
		OutputSize: 256,
		Rounds: 24,
		BlockSize: 1088,     
		RotationOffsets: R,
		RoundConstants: RC,
		Domain: 0x01,
	})
	return hash
}

func NewSHA3_256(api abstractor.API, inputSize int, data ...frontend.Variable) []frontend.Variable {
	hash := api.Call(KeccakGadget{
		InputSize: inputSize,
		InputData: data,
		OutputSize: 256,
		Rounds: 24,
		BlockSize: 1088,     
		RotationOffsets: R,
		RoundConstants: RC,
		Domain: 0x06,
	})
	return hash
}

func get3DFlatIndex(x int, y int, z int) int {
	// https://stackoverflow.com/a/20266350
	zMax := laneSize
	yMax := stateSize
	return (x * zMax * yMax) + (y * zMax) + z;
}

func get2DFlatIndex(y int, z int) int {
	// https://stackoverflow.com/a/20266350
	zMax := laneSize
	return (y * zMax) + z;
}

func blockCopy(fromIndex int, dst []frontend.Variable, src []frontend.Variable) {
	toIndex := fromIndex + len(src)
	copy(dst[fromIndex:toIndex], src)
}

type Step1 struct {
	A               []frontend.Variable
}

func (g Step1) DefineGadget(api abstractor.API) []frontend.Variable {
	// C[x] = A[x,0] xor A[x,1] xor A[x,2] xor A[x,3] xor A[x,4], for x in 0…4
	C := make([]frontend.Variable, stateSize*laneSize)
	for x := 0; x < stateSize; x += 1 {
		blockCopy(get2DFlatIndex(x,0), C, api.Call(Xor5{
			A: g.A[get3DFlatIndex(x,0,0):get3DFlatIndex(x,0,64)],
			B: g.A[get3DFlatIndex(x,1,0):get3DFlatIndex(x,1,64)],
			C: g.A[get3DFlatIndex(x,2,0):get3DFlatIndex(x,2,64)],
			D: g.A[get3DFlatIndex(x,3,0):get3DFlatIndex(x,3,64)],
			E: g.A[get3DFlatIndex(x,4,0):get3DFlatIndex(x,4,64)],
		}))
	}

	return C;
}

type Step2Round struct {
	X int
	C               []frontend.Variable
}

func (g Step2Round) DefineGadget(api abstractor.API) []frontend.Variable {
	index_c := (g.X+1)%stateSize
	tmp := api.Call(Rot{g.C[get2DFlatIndex(index_c,0):get2DFlatIndex(index_c,64)], 1})

	index_c = (g.X+4)%stateSize
	return api.Call(Xor{g.C[get2DFlatIndex(index_c,0):get2DFlatIndex(index_c,64)], tmp[:]})
}

type Step2 struct {
	C               []frontend.Variable
}

func (g Step2) DefineGadget(api abstractor.API) []frontend.Variable {
	// D[x] = C[x-1] xor rot(C[x+1],1), for x in 0…4
	D := make([]frontend.Variable, stateSize*laneSize)
	for x := 0; x < stateSize; x += 1 {
		blockCopy(get2DFlatIndex(x,0), D, api.Call(Step2Round{
			X: x,
			C: g.C,
		}))
	}
	return D
}

type Step3Inner struct {
	X               int
	A               []frontend.Variable
	D               []frontend.Variable
}

func (g Step3Inner) DefineGadget(api abstractor.API) []frontend.Variable {
	// A[x,y] = A[x,y] xor D[x], for x in 0…4 and y in 0…4
	for y := 0; y < stateSize; y += 1 {
		blockCopy(get3DFlatIndex(g.X,y,0), g.A, api.Call(Xor{g.A[get3DFlatIndex(g.X,y,0):get3DFlatIndex(g.X,y,64)], g.D[get2DFlatIndex(g.X,0):get2DFlatIndex(g.X,64)]}))
	}
	return g.A
}

type Step3 struct {
	A               []frontend.Variable
	D               []frontend.Variable
}

func (g Step3) DefineGadget(api abstractor.API) []frontend.Variable {
	// A[x,y] = A[x,y] xor D[x], for x in 0…4 and y in 0…4
	for x := 0; x < stateSize; x += 1 {
		g.A = api.Call(Step3Inner{
			X: x,
			A: g.A,
			D: g.D,
		})
	}
	return g.A
}

type Step4 struct {
	A               []frontend.Variable
	RotationOffsets [5][5]int
}

func (g Step4) DefineGadget(api abstractor.API) []frontend.Variable {
	// B[y,2*x+3*y] = rot(A[x,y], r[x,y]), for (x,y) in (0…4,0…4)
	B := make([]frontend.Variable, stateSize*stateSize*laneSize)
	for x := 0; x < stateSize; x += 1 {
		for y := 0; y < stateSize; y += 1 {
			blockCopy(get3DFlatIndex(y,(2*x+3*y)%stateSize,0), B, api.Call(Rot{g.A[get3DFlatIndex(x,y,0):get3DFlatIndex(x,y,64)], g.RotationOffsets[x][y]}))
		}
	}
	return B
}

type Step5Round struct {
	X int
	Y int
	A               []frontend.Variable
	B               []frontend.Variable
}

func (g Step5Round) DefineGadget(api abstractor.API) []frontend.Variable {
	not_b := api.Call(Not{g.B[get3DFlatIndex((g.X+1)%stateSize,g.Y,0):get3DFlatIndex((g.X+1)%stateSize,g.Y,64)]})
	tmp := api.Call(And{not_b, g.B[get3DFlatIndex((g.X+2)%stateSize,g.Y,0):get3DFlatIndex((g.X+2)%stateSize,g.Y,64)]})
	blockCopy(get3DFlatIndex(g.X,g.Y,0), g.A, api.Call(Xor{g.B[get3DFlatIndex(g.X,g.Y,0):get3DFlatIndex(g.X,g.Y,64)], tmp}))
	return g.A
}

type Step5 struct {
	A               []frontend.Variable
	B               []frontend.Variable
}

func (g Step5) DefineGadget(api abstractor.API) []frontend.Variable {
	// A[x,y] = B[x,y] xor ((not B[x+1,y]) and B[x+2,y]), for x in 0…4 and y in 0…4
	for x := 0; x < stateSize; x += 1 {
		for y := 0; y < stateSize; y += 1 {
			g.A = api.Call(Step5Round{
				X: x,
				Y: y,
				A: g.A,
				B: g.B,
			})
		}
	}
	return g.A
}

type KeccakRound struct {
	A               []frontend.Variable
	RC              [laneSize]frontend.Variable
	RotationOffsets [5][5]int
}

func (g KeccakRound) DefineGadget(api abstractor.API) []frontend.Variable {
	C := api.Call(Step1{A: g.A})
	D := api.Call(Step2{C: C})
	g.A = api.Call(Step3{g.A, D})
	B := api.Call(Step4{g.A, g.RotationOffsets})
	g.A = api.Call(Step5{A: g.A, B: B})

	// A[0,0] = A[0,0] xor RC
	blockCopy(get3DFlatIndex(0,0,0), g.A, api.Call(Xor{g.A[get3DFlatIndex(0,0,0):get3DFlatIndex(0,0,64)], g.RC[:]}))

	return g.A
}

type KeccakF struct {
	A               []frontend.Variable
	Rounds int
	RotationOffsets [5][5]int
	RoundConstants [24][64]frontend.Variable
}

func (g KeccakF) DefineGadget(api abstractor.API) []frontend.Variable {
	for i := 0; i < g.Rounds; i += 1 {
		g.A = api.Call(KeccakRound{
			A: g.A,
			RC: g.RoundConstants[i],
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

func (g KeccakGadget) DefineGadget(api abstractor.API) []frontend.Variable {
	// Padding
	paddingSize := int(math.Ceil(float64(g.InputSize)/float64(g.BlockSize))) * g.BlockSize
	if len(g.InputData) == 0 {
		paddingSize = g.BlockSize
	}

	P := make([]frontend.Variable, paddingSize)
	for i := 0; i < len(g.InputData); i += 1 {
		P[i] = g.InputData[i]
	}

	// write domain separator
	for i := 0; i < 8; i += 1 {
		P[i+len(g.InputData)] = (g.Domain >> i) & 1
	}

	// fill with zero bytes
	for i := len(g.InputData) + 8; i < len(P); i += 1 {
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
	S := make([]frontend.Variable, stateSize*stateSize*laneSize)
	for i := 0; i < stateSize; i += 1 {
		for j := 0; j < stateSize; j += 1 {
			for k := 0; k < laneSize; k += 1 {
				S[get3DFlatIndex(i,j,k)] = 0
			}
		}
	}

	// Absorbing phase
	for i := 0; i < len(P); i += g.BlockSize {
		for x := 0; x < stateSize; x += 1 {
			for y := 0; y < stateSize; y += 1 {
				if x+5*y < g.BlockSize/laneSize {
					var Pi [laneSize]frontend.Variable
					copy(Pi[:], P[i+(x+5*y)*laneSize:i+(x+5*y+1)*laneSize])
					blockCopy(get3DFlatIndex(x,y,0), S, api.Call(Xor{S[get3DFlatIndex(x,y,0):get3DFlatIndex(x,y,64)], Pi[:]}))
				}
			}
		}
		S = api.Call(KeccakF{
			A: S,
			Rounds: g.Rounds,
			RotationOffsets: g.RotationOffsets,
			RoundConstants: g.RoundConstants,
		})
	}

	// Squeezing phase
	var Z []frontend.Variable
	i := 0
	for i < g.OutputSize {
		for x := 0; x < stateSize; x += 1 {
			for y := 0; y < stateSize; y += 1 {
				if i < g.OutputSize && x+5*y < g.BlockSize/laneSize {
					Z = append(Z, S[get3DFlatIndex(y,x,0):get3DFlatIndex(y,x,64)]...)
					i += laneSize
				}
			}
		}
		if i < g.OutputSize-laneSize {
			S = api.Call(KeccakF{
				A: S,
				Rounds: g.Rounds,
				RotationOffsets: g.RotationOffsets,
				RoundConstants: g.RoundConstants,
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

func (g Xor5Round) DefineGadget(api abstractor.API) []frontend.Variable {
	tmp_ab := api.Xor(g.A, g.B)
	tmp_abc := api.Xor(g.C, tmp_ab)
	tmp_abcd := api.Xor(g.D, tmp_abc)
	xor := api.Xor(g.E, tmp_abcd)
	return []frontend.Variable{xor}
}

type Xor5 struct {
	A []frontend.Variable
	B []frontend.Variable
	C []frontend.Variable
	D []frontend.Variable
	E []frontend.Variable
}

func (g Xor5) DefineGadget(api abstractor.API) []frontend.Variable {
	var c [laneSize]frontend.Variable
	for i := 0; i < len(g.A); i += 1 {
		c[i] = api.Call(Xor5Round{g.A[i], g.B[i], g.C[i], g.D[i], g.E[i]})[0]
	}
	return c[:]
}

type Xor struct {
	A []frontend.Variable
	B []frontend.Variable
}

func (g Xor) DefineGadget(api abstractor.API) []frontend.Variable {
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

func (g Rot) DefineGadget(api abstractor.API) []frontend.Variable {
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

func (g And) DefineGadget(api abstractor.API) []frontend.Variable {
	var c [laneSize]frontend.Variable
	for i := 0; i < len(g.A); i += 1 {
		c[i] = api.And(g.A[i], g.B[i])
	}
	return c[:]
}

type Not struct {
	A []frontend.Variable
}

func (g Not) DefineGadget(api abstractor.API) []frontend.Variable {
	var c [laneSize]frontend.Variable
	for i := 0; i < len(g.A); i += 1 {
		c[i] = api.Sub(1, g.A[i])
	}
	return c[:]
}