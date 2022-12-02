package main

import (
	"math/big"
)
import "github.com/iden3/go-iden3-crypto/poseidon"

type PoseidonTree struct {
	Depth     int
	LeafCount int
	Contents  []big.Int
}

func NewTree(depth int) PoseidonTree {
	leafCount := 1 << depth
	contents := make([]big.Int, 2*leafCount)
	rehashSubtree(contents, 1)
	return PoseidonTree{depth, leafCount, contents}
}

func (t *PoseidonTree) Update(index int, value big.Int) []big.Int {
	t.Contents[t.LeafCount+index] = value
	var proof []big.Int
	for index > 0 {
		if index%2 == 0 {
			proof = append(proof, t.Contents[index+1])
		} else {
			proof = append(proof, t.Contents[index-1])
		}
		index /= 2
		if index > 0 {
			left := t.Contents[2*index]
			right := t.Contents[2*index+1]
			out, _ := poseidon.Hash([]*big.Int{&left, &right})
			t.Contents[index] = *out
		}
	}
	for i, j := 0, len(proof)-1; i < j; i, j = i+1, j-1 {
		proof[i], proof[j] = proof[j], proof[i]
	}
	return proof
}

func rehashSubtree(contents []big.Int, index int) big.Int {
	if index >= len(contents)/2 {
		return contents[index]
	}
	left := rehashSubtree(contents, 2*index)
	right := rehashSubtree(contents, 2*index+1)
	out, _ := poseidon.Hash([]*big.Int{&left, &right})
	contents[index] = *out
	return *out
}
