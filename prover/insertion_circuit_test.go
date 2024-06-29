package prover

import (
	"crypto/rand"
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	bn254fr "github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
	gokzg4844 "github.com/crate-crypto/go-kzg-4844"
	"github.com/stretchr/testify/require"

	poseidon "worldcoin/gnark-mbu/poseidon_native"
)

const (
	numGoRoutines      = 0
	existingUsersCount = 1500
	batchSize          = 20
	depth              = 20
)

func TestInsertionCircuit(t *testing.T) {
	incomingIds := generateRandomIdentities(batchSize)
	smallTree := poseidon.NewTree(treeDepth(polynomialDegree))
	idComms := make([]frontend.Variable, batchSize)
	for i, id := range incomingIds {
		idComms[i] = id
		smallTree.Update(i, id)
	}
	incomingIdsTreeRoot := smallTree.Root()
	incomingIdsTreeRoot = *bytesToBn254BigInt(incomingIdsTreeRoot.Bytes())

	ctx, err := gokzg4844.NewContext4096Secure()
	require.NoError(t, err)
	blob := identitiesToBlob(incomingIds)
	commitment, err := ctx.BlobToKZGCommitment(blob, numGoRoutines)
	require.NoError(t, err)
	commitment4844 := *bytesToBn254BigInt(commitment[:])

	challenge := bigIntsToChallenge([]big.Int{incomingIdsTreeRoot, commitment4844})
	proof, evaluation, err := ctx.ComputeKZGProof(blob, challenge, numGoRoutines)
	require.NoError(t, err)
	err = ctx.VerifyKZGProof(commitment, challenge, evaluation, proof)
	require.NoError(t, err)

	existingIds := generateRandomIdentities(existingUsersCount)
	bigTree := poseidon.NewTree(depth)
	for i, id := range existingIds {
		bigTree.Update(i, id)
	}
	preRoot := bigTree.Root()
	merkleProofs := make([][]frontend.Variable, batchSize)
	for i, id := range incomingIds {
		mp := bigTree.Update(i+existingUsersCount, id)
		merkleProofs[i] = make([]frontend.Variable, len(mp))
		for j, v := range mp {
			merkleProofs[i][j] = v
		}
	}
	postRoot := bigTree.Root()

	circuit := InsertionMbuCircuit{
		IdComms:      make([]frontend.Variable, batchSize),
		MerkleProofs: make([][]frontend.Variable, batchSize),
		BatchSize:    batchSize,
		Depth:        depth,
	}
	for i := range merkleProofs {
		circuit.MerkleProofs[i] = make([]frontend.Variable, depth)
	}

	assignment := InsertionMbuCircuit{
		InputHash:          incomingIdsTreeRoot,
		ExpectedEvaluation: evaluation[:],
		Commitment4844:     commitment4844,
		StartIndex:         existingUsersCount,
		PreRoot:            preRoot,
		PostRoot:           postRoot,
		IdComms:            idComms,
		MerkleProofs:       merkleProofs,
		BatchSize:          batchSize,
		Depth:              depth,
	}

	assert := test.NewAssert(t)
	assert.CheckCircuit(
		&circuit, test.WithBackends(backend.GROTH16), test.WithCurves(ecc.BN254),
		test.WithValidAssignment(&assignment),
	)
}

// generateRandomIdentities generates a slice of random big integers reduced modulo BN254 FR.
func generateRandomIdentities(count int) []big.Int {
	ids := make([]big.Int, count)
	for i := range ids {
		n, _ := rand.Int(rand.Reader, bn254fr.Modulus())
		ids[i] = *n
	}
	return ids
}
