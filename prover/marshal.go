package prover

import (
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"math/big"
	"os"

	curve "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fp"

	"worldcoin/gnark-mbu/logging"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend/groth16"
	bn254 "github.com/consensys/gnark/backend/groth16/bn254"
)

func fromHex(i *big.Int, s string) error {
	_, ok := i.SetString(s, 0)
	if !ok {
		return fmt.Errorf("invalid number: %s", s)
	}
	return nil
}

func toHexElement(i fp.Element) string {
	return fmt.Sprintf("0x%s", i.Text(16))
}

func toHex(i *big.Int) string {
	return fmt.Sprintf("0x%s", i.Text(16))
}

type InsertionResponseJSON struct {
	InputHash          string `json:"inputHash"`
	ExpectedEvaluation string `json:"expectedEvaluation"`
	Commitment4844     string `json:"commitment4844"`
	Proof              Proof  `json:"proof"`
	KzgProof           string `json:"kzgProof"`
}

func (r *InsertionResponse) MarshalJSON() ([]byte, error) {
	return json.Marshal(
		&InsertionResponseJSON{
			InputHash:          toHex(&r.InputHash),
			ExpectedEvaluation: hex.EncodeToString(r.ExpectedEvaluation[:]),
			Commitment4844:     hex.EncodeToString(r.Commitment4844[:]),
			Proof:              r.Proof,
			KzgProof:           hex.EncodeToString(r.KzgProof[:]),
		},
	)
}

func (r *InsertionResponse) UnmarshalJSON(data []byte) error {
	aux := &InsertionResponseJSON{}
	if err := json.Unmarshal(data, &aux); err != nil {
		return err
	}

	if err := fromHex(&r.InputHash, aux.InputHash); err != nil {
		return err
	}

	expectedEvaluation, err := hex.DecodeString(aux.ExpectedEvaluation)
	if err != nil || len(expectedEvaluation) != 32 {
		return fmt.Errorf("invalid ExpectedEvaluation: %s", aux.ExpectedEvaluation)
	}
	copy(r.ExpectedEvaluation[:], expectedEvaluation)

	commitment4844, err := hex.DecodeString(aux.Commitment4844)
	if err != nil || len(commitment4844) != 48 {
		return fmt.Errorf("invalid Commitment4844: %s", aux.Commitment4844)
	}
	copy(r.Commitment4844[:], commitment4844)

	r.Proof = aux.Proof

	kzgProof, err := hex.DecodeString(aux.KzgProof)
	if err != nil || len(kzgProof) != 48 {
		return fmt.Errorf("invalid KzgProof: %s", aux.KzgProof)
	}
	copy(r.KzgProof[:], kzgProof)

	return nil
}

type InsertionParametersJSON struct {
	StartIndex   uint32     `json:"startIndex"`
	PreRoot      string     `json:"preRoot"`
	PostRoot     string     `json:"postRoot"`
	IdComms      []string   `json:"identityCommitments"`
	MerkleProofs [][]string `json:"merkleProofs"`
}

type DeletionParametersJSON struct {
	InputHash       string     `json:"inputHash"`
	DeletionIndices []uint32   `json:"deletionIndices"`
	PreRoot         string     `json:"preRoot"`
	PostRoot        string     `json:"postRoot"`
	IdComms         []string   `json:"identityCommitments"`
	MerkleProofs    [][]string `json:"merkleProofs"`
}

func (p *InsertionParameters) MarshalJSON() ([]byte, error) {
	paramsJson := InsertionParametersJSON{}
	paramsJson.StartIndex = p.StartIndex
	paramsJson.PreRoot = toHex(&p.PreRoot)
	paramsJson.PostRoot = toHex(&p.PostRoot)
	paramsJson.IdComms = make([]string, len(p.IdComms))
	for i := 0; i < len(p.IdComms); i++ {
		paramsJson.IdComms[i] = toHex(&p.IdComms[i])
	}
	paramsJson.MerkleProofs = make([][]string, len(p.MerkleProofs))
	for i := 0; i < len(p.MerkleProofs); i++ {
		paramsJson.MerkleProofs[i] = make([]string, len(p.MerkleProofs[i]))
		for j := 0; j < len(p.MerkleProofs[i]); j++ {
			paramsJson.MerkleProofs[i][j] = toHex(&p.MerkleProofs[i][j])
		}
	}
	return json.Marshal(paramsJson)
}

func (p *InsertionParameters) UnmarshalJSON(data []byte) error {

	var params InsertionParametersJSON

	err := json.Unmarshal(data, &params)
	if err != nil {
		return err
	}

	p.StartIndex = params.StartIndex

	err = fromHex(&p.PreRoot, params.PreRoot)
	if err != nil {
		return err
	}

	err = fromHex(&p.PostRoot, params.PostRoot)
	if err != nil {
		return err
	}

	p.IdComms = make([]big.Int, len(params.IdComms))
	for i := 0; i < len(params.IdComms); i++ {
		err = fromHex(&p.IdComms[i], params.IdComms[i])
		if err != nil {
			return err
		}
	}

	p.MerkleProofs = make([][]big.Int, len(params.MerkleProofs))
	for i := 0; i < len(params.MerkleProofs); i++ {
		p.MerkleProofs[i] = make([]big.Int, len(params.MerkleProofs[i]))
		for j := 0; j < len(params.MerkleProofs[i]); j++ {
			err = fromHex(&p.MerkleProofs[i][j], params.MerkleProofs[i][j])
			if err != nil {
				return err
			}
		}
	}

	return nil
}

func (p *DeletionParameters) MarshalJSON() ([]byte, error) {
	paramsJson := DeletionParametersJSON{}
	paramsJson.InputHash = toHex(&p.InputHash)
	paramsJson.DeletionIndices = p.DeletionIndices
	paramsJson.PreRoot = toHex(&p.PreRoot)
	paramsJson.PostRoot = toHex(&p.PostRoot)
	paramsJson.IdComms = make([]string, len(p.IdComms))
	for i := 0; i < len(p.IdComms); i++ {
		paramsJson.IdComms[i] = toHex(&p.IdComms[i])
	}
	paramsJson.MerkleProofs = make([][]string, len(p.MerkleProofs))
	for i := 0; i < len(p.MerkleProofs); i++ {
		paramsJson.MerkleProofs[i] = make([]string, len(p.MerkleProofs[i]))
		for j := 0; j < len(p.MerkleProofs[i]); j++ {
			paramsJson.MerkleProofs[i][j] = toHex(&p.MerkleProofs[i][j])
		}
	}
	return json.Marshal(paramsJson)
}

func (p *DeletionParameters) UnmarshalJSON(data []byte) error {

	var params DeletionParametersJSON

	err := json.Unmarshal(data, &params)
	if err != nil {
		return err
	}

	err = fromHex(&p.InputHash, params.InputHash)
	if err != nil {
		return err
	}

	p.DeletionIndices = params.DeletionIndices

	err = fromHex(&p.PreRoot, params.PreRoot)
	if err != nil {
		return err
	}

	err = fromHex(&p.PostRoot, params.PostRoot)
	if err != nil {
		return err
	}

	p.IdComms = make([]big.Int, len(params.IdComms))
	for i := 0; i < len(params.IdComms); i++ {
		err = fromHex(&p.IdComms[i], params.IdComms[i])
		if err != nil {
			return err
		}
	}

	p.MerkleProofs = make([][]big.Int, len(params.MerkleProofs))
	for i := 0; i < len(params.MerkleProofs); i++ {
		p.MerkleProofs[i] = make([]big.Int, len(params.MerkleProofs[i]))
		for j := 0; j < len(params.MerkleProofs[i]); j++ {
			err = fromHex(&p.MerkleProofs[i][j], params.MerkleProofs[i][j])
			if err != nil {
				return err
			}
		}
	}

	return nil
}

type ProofJSON struct {
	Ar            [2]string    `json:"ar"`
	Bs            [2][2]string `json:"bs"`
	Krs           [2]string    `json:"krs"`
	Commitments   [][2]string  `json:"commitments"`
	CommitmentPok [2]string    `json:"commitmentPok"`
}

func (p *Proof) MarshalJSON() ([]byte, error) {
	proof, ok := p.Proof.(*bn254.Proof)
	if !ok {
		return nil, fmt.Errorf("invalid proof type, should be bn254.Proof, got %T", p.Proof)
	}

	proofJson := ProofJSON{}

	proofJson.Ar[0] = toHexElement(proof.Ar.X)
	proofJson.Ar[1] = toHexElement(proof.Ar.Y)

	proofJson.Bs[0][0] = toHexElement(proof.Bs.X.A1)
	proofJson.Bs[0][1] = toHexElement(proof.Bs.X.A0)
	proofJson.Bs[1][0] = toHexElement(proof.Bs.Y.A1)
	proofJson.Bs[1][1] = toHexElement(proof.Bs.Y.A0)

	proofJson.Krs[0] = toHexElement(proof.Krs.X)
	proofJson.Krs[1] = toHexElement(proof.Krs.Y)

	for _, c := range proof.Commitments {
		commitment := [2]string{
			toHexElement(c.X),
			toHexElement(c.Y),
		}
		proofJson.Commitments = append(proofJson.Commitments, commitment)
	}

	proofJson.CommitmentPok[0] = toHexElement(proof.CommitmentPok.X)
	proofJson.CommitmentPok[1] = toHexElement(proof.CommitmentPok.Y)

	return json.Marshal(proofJson)
}

func (p *Proof) UnmarshalJSON(data []byte) error {
	var proofJson ProofJSON
	err := json.Unmarshal(data, &proofJson)
	if err != nil {
		return err
	}

	proof := new(bn254.Proof)

	if _, err = proof.Ar.X.SetString(proofJson.Ar[0]); err != nil {
		return err
	}
	if _, err = proof.Ar.Y.SetString(proofJson.Ar[1]); err != nil {
		return err
	}

	if _, err = proof.Bs.X.A1.SetString(proofJson.Bs[0][0]); err != nil {
		return err
	}
	if _, err = proof.Bs.X.A0.SetString(proofJson.Bs[0][1]); err != nil {
		return err
	}
	if _, err = proof.Bs.Y.A1.SetString(proofJson.Bs[1][0]); err != nil {
		return err
	}
	if _, err = proof.Bs.Y.A0.SetString(proofJson.Bs[1][1]); err != nil {
		return err
	}

	if _, err = proof.Krs.X.SetString(proofJson.Krs[0]); err != nil {
		return err
	}
	if _, err = proof.Krs.Y.SetString(proofJson.Krs[1]); err != nil {
		return err
	}

	proof.Commitments= make([]curve.G1Affine, len(proofJson.Commitments))
	for i, c := range proofJson.Commitments {
		if _, err = proof.Commitments[i].X.SetString(c[0]); err != nil {
			return err
		}
		if _, err = proof.Commitments[i].Y.SetString(c[1]); err != nil {
			return err
		}
	}

	if _, err = proof.CommitmentPok.X.SetString(proofJson.CommitmentPok[0]); err != nil {
		return err
	}
	if _, err = proof.CommitmentPok.Y.SetString(proofJson.CommitmentPok[1]); err != nil {
		return err
	}

	p.Proof = proof

	return nil
}

func (ps *ProvingSystem) WriteTo(w io.Writer) (int64, error) {
	var totalWritten int64 = 0
	var intBuf [4]byte

	binary.BigEndian.PutUint32(intBuf[:], ps.TreeDepth)
	written, err := w.Write(intBuf[:])
	totalWritten += int64(written)
	if err != nil {
		return totalWritten, err
	}

	binary.BigEndian.PutUint32(intBuf[:], ps.BatchSize)
	written, err = w.Write(intBuf[:])
	totalWritten += int64(written)
	if err != nil {
		return totalWritten, err
	}

	keyWritten, err := ps.ProvingKey.WriteTo(w)
	totalWritten += keyWritten
	if err != nil {
		return totalWritten, err
	}

	keyWritten, err = ps.VerifyingKey.WriteTo(w)
	totalWritten += keyWritten
	if err != nil {
		return totalWritten, err
	}

	keyWritten, err = ps.ConstraintSystem.WriteTo(w)
	totalWritten += keyWritten
	if err != nil {
		return totalWritten, err
	}

	return totalWritten, nil
}

func (ps *ProvingSystem) UnsafeReadFrom(r io.Reader) (int64, error) {
	var totalRead int64 = 0
	var intBuf [4]byte

	logging.Logger().Debug().Msg("Reading tree depth")
	read, err := io.ReadFull(r, intBuf[:])
	totalRead += int64(read)
	if err != nil {
		return totalRead, err
	}
	ps.TreeDepth = binary.BigEndian.Uint32(intBuf[:])

	logging.Logger().Debug().Msg("Reading batch size")
	read, err = io.ReadFull(r, intBuf[:])
	totalRead += int64(read)
	if err != nil {
		return totalRead, err
	}
	ps.BatchSize = binary.BigEndian.Uint32(intBuf[:])

	logging.Logger().Debug().Msg("Reading proving key")
	ps.ProvingKey = groth16.NewProvingKey(ecc.BN254)
	keyRead, err := ps.ProvingKey.UnsafeReadFrom(r)
	totalRead += keyRead
	if err != nil {
		return totalRead, err
	}

	logging.Logger().Debug().Msg("Reading verifying key")
	ps.VerifyingKey = groth16.NewVerifyingKey(ecc.BN254)
	keyRead, err = ps.VerifyingKey.UnsafeReadFrom(r)
	totalRead += keyRead
	if err != nil {
		return totalRead, err
	}

	logging.Logger().Debug().Msg("Reading constraint system")
	ps.ConstraintSystem = groth16.NewCS(ecc.BN254)
	keyRead, err = ps.ConstraintSystem.ReadFrom(r)
	totalRead += keyRead
	if err != nil {
		return totalRead, err
	}

	return totalRead, nil
}

func ReadSystemFromFile(path string) (ps *ProvingSystem, err error) {
	ps = new(ProvingSystem)
	file, err := os.Open(path)
	if err != nil {
		return
	}

	defer func() {
		closeErr := file.Close()
		if closeErr != nil && err == nil {
			err = closeErr
		}
	}()

	_, err = ps.UnsafeReadFrom(file)
	if err != nil {
		return
	}
	return
}
