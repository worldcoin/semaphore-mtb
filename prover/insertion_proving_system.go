package prover

import (
	"fmt"
	"math/big"

	gokzg4844 "github.com/crate-crypto/go-kzg-4844"

	"worldcoin/gnark-mbu/logging"
	poseidon "worldcoin/gnark-mbu/poseidon_native"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

type InsertionParameters struct {
	StartIndex   uint32
	PreRoot      big.Int
	PostRoot     big.Int
	IdComms      []big.Int
	MerkleProofs [][]big.Int
}

type InsertionResponse struct {
	InputHash          big.Int
	ExpectedEvaluation gokzg4844.Scalar
	Commitment4844     gokzg4844.KZGCommitment
	Proof              Proof
	KzgProof           gokzg4844.KZGProof
}

func (p *InsertionParameters) ValidateShape(treeDepth uint32, batchSize uint32) error {
	if len(p.IdComms) != int(batchSize) {
		return fmt.Errorf("wrong number of identity commitments: %d", len(p.IdComms))
	}
	if len(p.MerkleProofs) != int(batchSize) {
		return fmt.Errorf("wrong number of merkle proofs: %d", len(p.MerkleProofs))
	}
	for i, proof := range p.MerkleProofs {
		if len(proof) != int(treeDepth) {
			return fmt.Errorf("wrong size of merkle proof for proof %d: %d", i, len(proof))
		}
	}
	return nil
}

func BuildR1CSInsertion(treeDepth uint32, batchSize uint32) (constraint.ConstraintSystem, error) {
	proofs := make([][]frontend.Variable, batchSize)
	for i := 0; i < int(batchSize); i++ {
		proofs[i] = make([]frontend.Variable, treeDepth)
	}
	circuit := InsertionMbuCircuit{
		Depth:        int(treeDepth),
		BatchSize:    int(batchSize),
		IdComms:      make([]frontend.Variable, batchSize),
		MerkleProofs: proofs,
	}
	return frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
}

func SetupInsertion(treeDepth uint32, batchSize uint32) (*ProvingSystem, error) {
	ccs, err := BuildR1CSInsertion(treeDepth, batchSize)
	if err != nil {
		return nil, err
	}
	pk, vk, err := groth16.Setup(ccs)
	if err != nil {
		return nil, err
	}
	return &ProvingSystem{treeDepth, batchSize, pk, vk, ccs}, nil
}

func (ps *ProvingSystem) ProveInsertion(params *InsertionParameters) (*InsertionResponse, error) {
	if err := params.ValidateShape(ps.TreeDepth, ps.BatchSize); err != nil {
		return nil, err
	}

	idCommsTree := poseidon.NewTree(treeDepth(polynomialDegree))
	idComms := make([]frontend.Variable, ps.BatchSize)
	for i := 0; i < int(ps.BatchSize); i++ {
		idComms[i] = params.IdComms[i]
		idCommsTree.Update(i, params.IdComms[i])
	}
	incomingIdsTreeRoot := idCommsTree.Root()
	incomingIdsTreeRoot = *BytesToBn254BigInt(incomingIdsTreeRoot.Bytes())

	proofs := make([][]frontend.Variable, ps.BatchSize)
	for i := 0; i < int(ps.BatchSize); i++ {
		proofs[i] = make([]frontend.Variable, ps.TreeDepth)
		for j := 0; j < int(ps.TreeDepth); j++ {
			proofs[i][j] = params.MerkleProofs[i][j]
		}
	}

	ctx, err := gokzg4844.NewContext4096Secure()
	if err != nil {
		return nil, err
	}

	const numGoRoutines = 0
	blob := identitiesToBlob(params.IdComms)
	commitment, err := ctx.BlobToKZGCommitment(blob, numGoRoutines)
	if err != nil {
		return nil, err
	}
	versionedKzgHash := KzgToVersionedHash(commitment)
	versionedKzgHashReduced := *BytesToBn254BigInt(versionedKzgHash[:])

	challenge := bigIntsToChallenge([]big.Int{incomingIdsTreeRoot, versionedKzgHashReduced})
	kzgProof, evaluation, err := ctx.ComputeKZGProof(blob, challenge, numGoRoutines)
	if err != nil {
		return nil, err
	}

	err = ctx.VerifyKZGProof(commitment, challenge, evaluation, kzgProof)
	if err != nil {
		return nil, err
	}

	assignment := InsertionMbuCircuit{
		InputHash:          incomingIdsTreeRoot,
		ExpectedEvaluation: *BytesToBn254BigInt(evaluation[:]),
		Commitment4844:     versionedKzgHashReduced,
		StartIndex:         params.StartIndex,
		PreRoot:            params.PreRoot,
		PostRoot:           params.PostRoot,
		IdComms:            idComms,
		MerkleProofs:       proofs,
	}

	witness, err := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	if err != nil {
		return nil, err
	}
	logging.Logger().Info().Msg("generating proof")
	proof, err := groth16.Prove(ps.ConstraintSystem, ps.ProvingKey, witness)
	if err != nil {
		return nil, err
	}

	logging.Logger().Info().Msg("proof generated successfully")
	return &InsertionResponse{
		InputHash:          incomingIdsTreeRoot,
		ExpectedEvaluation: evaluation,
		Commitment4844:     commitment,
		Proof:              Proof{proof},
		KzgProof:           kzgProof,
	}, nil
}

func (ps *ProvingSystem) VerifyInsertion(inputHash big.Int, proof *Proof) error {
	publicAssignment := InsertionMbuCircuit{
		InputHash: inputHash,
		IdComms:   make([]frontend.Variable, ps.BatchSize),
	}
	witness, err := frontend.NewWitness(&publicAssignment, ecc.BN254.ScalarField(), frontend.PublicOnly())
	if err != nil {
		return err
	}
	return groth16.Verify(proof.Proof, ps.VerifyingKey, witness)
}
