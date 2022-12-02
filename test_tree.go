package main

import (
	"math/big"
)
import "github.com/iden3/go-iden3-crypto/poseidon"

type PoseidonTree struct {
	LeafCount int
	Contents  []big.Int
}

func NewTree(depth int) PoseidonTree {
	leafCount := 1 << depth
	contents := make([]big.Int, 2*leafCount)
	rehashSubtree(contents, 1)
	return PoseidonTree{leafCount, contents}
}

func (t *PoseidonTree) Root() big.Int {
	return t.Contents[1]
}

func (t *PoseidonTree) Update(index int, value big.Int) []big.Int {
	index += t.LeafCount
	t.Contents[index] = value
	var proof []big.Int
	for index > 1 {
		if index%2 == 0 {
			proof = append(proof, t.Contents[index+1])
		} else {
			proof = append(proof, t.Contents[index-1])
		}
		index /= 2
		left := t.Contents[2*index]
		right := t.Contents[2*index+1]
		out, _ := poseidon.Hash([]*big.Int{&left, &right})
		t.Contents[index] = *out

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
