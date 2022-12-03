package main

import (
	"github.com/iden3/go-iden3-crypto/poseidon"
	"math/big"
)

type PoseidonTree struct {
	LeafCount int
	Contents  []big.Int
}

func NewTree(depth int) PoseidonTree {
	leafCount := 1 << depth
	contents := make([]big.Int, 2*leafCount)
	initHashes := make([]big.Int, depth+1)
	for i := depth - 1; i >= 0; i-- {
		val, _ := poseidon.Hash([]*big.Int{&initHashes[i+1], &initHashes[i+1]})
		initHashes[i] = *val
	}
	initSubtree(contents, 1, 0, initHashes)
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

func initSubtree(contents []big.Int, index int, depth int, hashes []big.Int) {
	if index >= len(contents)/2 {
		return
	}
	initSubtree(contents, 2*index, depth+1, hashes)
	initSubtree(contents, 2*index+1, depth+1, hashes)
	contents[index] = hashes[depth]
}
