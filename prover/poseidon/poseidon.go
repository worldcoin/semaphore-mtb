package poseidon

import (
	"github.com/consensys/gnark/frontend"
	"github.com/reilabs/gnark-lean-extractor/abstractor"
	"github.com/reilabs/gnark-lean-extractor/extractor"
)

type cfg struct {
	RF        int
	RP        int
	constants [][]frontend.Variable
	mds       [][]frontend.Variable
}

var CFG_3 = cfg{
	RF:        8,
	RP:        57,
	constants: CONSTANTS_3,
	mds:       MDS_3,
}

var CFG_2 = cfg{
	RF:        8,
	RP:        56,
	constants: CONSTANTS_2,
	mds:       MDS_2,
}

func cfgFor(t int) *cfg {
	switch t {
	case 2:
		return &CFG_2
	case 3:
		return &CFG_3
	}
	panic("Poseidon: unsupported arg count")
}

type Poseidon1 struct {
	In frontend.Variable
}

func (g Poseidon1) DefineGadget(api abstractor.API) interface{} {
	inp := []frontend.Variable{0, g.In}
	return extractor.Call1(api, poseidon{inp})[0]
}

type Poseidon2 struct {
	In1, In2 frontend.Variable
}

func (g Poseidon2) DefineGadget(api abstractor.API) interface{} {
	inp := []frontend.Variable{0, g.In1, g.In2}
	return extractor.Call1(api, poseidon{inp})[0]
}

type poseidon struct {
	Inputs []frontend.Variable
}

func (g poseidon) DefineGadget(api abstractor.API) interface{} {
	state := g.Inputs
	cfg := cfgFor(len(state))
	for i := 0; i < cfg.RF/2; i += 1 {
		state = extractor.Call1(api, fullRound{state, cfg.constants[i]})
	}
	for i := 0; i < cfg.RP; i += 1 {
		state = extractor.Call1(api, halfRound{state, cfg.constants[cfg.RF/2+i]})
	}
	for i := 0; i < cfg.RF/2; i += 1 {
		state = extractor.Call1(api, fullRound{state, cfg.constants[cfg.RF/2+cfg.RP+i]})
	}
	return state
}

type sbox struct {
	Inp frontend.Variable
}

func (s sbox) DefineGadget(api abstractor.API) interface{} {
	v2 := api.Mul(s.Inp, s.Inp)
	v4 := api.Mul(v2, v2)
	r := api.Mul(s.Inp, v4)
	return r
}

type mds struct {
	Inp []frontend.Variable
}

func (m mds) DefineGadget(api abstractor.API) interface{} {
	var mds = make([]frontend.Variable, len(m.Inp))
	cfg := cfgFor(len(m.Inp))
	for i := 0; i < len(m.Inp); i += 1 {
		var sum frontend.Variable = 0
		for j := 0; j < len(m.Inp); j += 1 {
			sum = api.Add(sum, api.Mul(m.Inp[j], cfg.mds[i][j]))
		}
		mds[i] = sum
	}
	return mds
}

type halfRound struct {
	Inp    []frontend.Variable
	Consts []frontend.Variable
}

func (h halfRound) DefineGadget(api abstractor.API) interface{} {
	for i := 0; i < len(h.Inp); i += 1 {
		h.Inp[i] = api.Add(h.Inp[i], h.Consts[i])
	}
	h.Inp[0] = extractor.Call(api, sbox{h.Inp[0]})
	return extractor.Call1(api, mds{h.Inp})
}

type fullRound struct {
	Inp    []frontend.Variable
	Consts []frontend.Variable
}

func (h fullRound) DefineGadget(api abstractor.API) interface{} {
	for i := 0; i < len(h.Inp); i += 1 {
		h.Inp[i] = api.Add(h.Inp[i], h.Consts[i])
	}
	for i := 0; i < len(h.Inp); i += 1 {
		h.Inp[i] = extractor.Call(api, sbox{h.Inp[i]})
	}
	return extractor.Call1(api, mds{h.Inp})
}
