package keccak

import (
	"github.com/consensys/gnark/frontend"
)

var RC = [24][64]frontend.Variable{
	toBits(0x0000000000000001),
	toBits(0x0000000000008082),
	toBits(0x800000000000808A),
	toBits(0x8000000080008000),
	toBits(0x000000000000808B),
	toBits(0x0000000080000001),
	toBits(0x8000000080008081),
	toBits(0x8000000000008009),
	toBits(0x000000000000008A),
	toBits(0x0000000000000088),
	toBits(0x0000000080008009),
	toBits(0x000000008000000A),
	toBits(0x000000008000808B),
	toBits(0x800000000000008B),
	toBits(0x8000000000008089),
	toBits(0x8000000000008003),
	toBits(0x8000000000008002),
	toBits(0x8000000000000080),
	toBits(0x000000000000800A),
	toBits(0x800000008000000A),
	toBits(0x8000000080008081),
	toBits(0x8000000000008080),
	toBits(0x0000000080000001),
	toBits(0x8000000080008008),
}

var R = [5][5]int{
	{0, 36, 3, 41, 18},
	{1, 44, 10, 45, 2},
	{62, 6, 43, 15, 61},
	{28, 55, 25, 21, 56},
	{27, 20, 39, 8, 14},
}

func toBits(a uint64) [64]frontend.Variable {
	var b [64]frontend.Variable
	for i := 0; i < 64; i += 1 {
		b[i] = (a >> i) & 1
	}
	return b
}
