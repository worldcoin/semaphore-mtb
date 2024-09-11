package keccak

import (
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/hash/sha3"
	"github.com/consensys/gnark/std/math/uints"
)

func Keccak256(api frontend.API, data []frontend.Variable) (hash []frontend.Variable, err error) {
	// Pad bits with frontend.Variable(0) until len(data) is a multiple of 8
	if len(data) % 8 != 0 {
		padSize := 8 - (len(data) % 8)
		data = append(data, make([]frontend.Variable, padSize)...)
	}

	// Convert bits to slice of uint8
	var input []uints.U8
	for i := 0; i < len(data); i += 8 {
		byteSlice := data[i : i+8]
		byteFv := api.FromBinary(byteSlice...)
		byteU8 := uints.U8{Val: byteFv}
		input = append(input, byteU8)
	}

	h, err := sha3.NewLegacyKeccak256(api)
	if err != nil {
		return nil, err
	}
	h.Write(input)

	// Convert slice of uint8 to one variable
	for _, sumByte := range h.Sum() {
		sumBits := api.ToBinary(sumByte.Val, 8)
		hash = append(hash, sumBits...)
	}

	return hash, nil
}
