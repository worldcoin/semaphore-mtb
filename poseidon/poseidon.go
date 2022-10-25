package poseidon

import (
	"github.com/consensys/gnark/frontend"
)

type Poseidon struct {
	nTotalRounds int
	nFullRounds  int
	data         []frontend.Variable
	api          frontend.API
	constants    [][]frontend.Variable
	mds          [][]frontend.Variable
}

func sbox(api frontend.API, v frontend.Variable) frontend.Variable {
	v2 := api.Mul(v, v)
	v4 := api.Mul(v2, v2)
	return api.Mul(v, v4)
}

func (h *Poseidon) applyMDS(api frontend.API, state []frontend.Variable) []frontend.Variable {
	if len(state) != len(h.mds) {
		panic("state and MDS size do not match")
	}

	var mds []frontend.Variable
	for i := 0; i < len(h.mds); i += 1 {
		var sum frontend.Variable = 0
		for j := 0; j < len(h.mds[i]); j += 1 {
			sum = api.Add(sum, api.Mul(state[j], h.mds[i][j]))
		}
		mds = append(mds, sum)
	}
	return mds
}

func (h *Poseidon) halfRound(api frontend.API, round int, state []frontend.Variable) []frontend.Variable {
	if len(state) != len(h.constants[round]) {
		panic("state and round constants size do not match")
	}

	for i := 0; i < len(state); i += 1 {
		state[i] = api.Add(state[i], h.constants[round][i])
	}

	state[0] = sbox(api, state[0])

	return h.applyMDS(api, state)
}

func (h *Poseidon) fullRound(api frontend.API, round int, state []frontend.Variable) []frontend.Variable {
	if len(state) != len(h.constants[round]) {
		panic("state and round constants size do not match")
	}

	for i := 0; i < len(state); i += 1 {
		state[i] = api.Add(state[i], h.constants[round][i])
	}

	for i := 0; i < len(state); i += 1 {
		state[i] = sbox(api, state[i])
	}

	return h.applyMDS(api, state)
}

func NewPoseidon1(api frontend.API) Poseidon {
	return Poseidon{
		nFullRounds:  4,
		nTotalRounds: 63,
		data:         []frontend.Variable{0},
		api:          api,
		constants:    CONSTANTS1,
		mds:          MDS1,
	}
}

func NewPoseidon2(api frontend.API) Poseidon {
	return Poseidon{
		nFullRounds:  4,
		nTotalRounds: 64,
		data:         []frontend.Variable{0},
		api:          api,
		constants:    CONSTANTS,
		mds:          MDS,
	}
}

func (h *Poseidon) Write(data ...frontend.Variable) {
	h.data = append(h.data, data...)
}

func (h *Poseidon) Reset() {
	h.data = []frontend.Variable{0}
}

func (h *Poseidon) Sum() frontend.Variable {
	state := h.data
	for i := 0; i < h.nTotalRounds+1; i += 1 {
		if i < h.nFullRounds || i > (h.nTotalRounds-h.nFullRounds) {
			state = h.fullRound(h.api, i, state)
		} else {
			state = h.halfRound(h.api, i, state)
		}
	}
	return state[0]
}
