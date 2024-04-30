package prover

import (
	"bytes"
	"encoding/binary"
	"encoding/json"
	"fmt"
	"io"
	"math/big"
	"os"
	"worldcoin/gnark-mbu/logging"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend/groth16"
)

func fromHex(i *big.Int, s string) error {
	_, ok := i.SetString(s, 0)
	if !ok {
		return fmt.Errorf("invalid number: %s", s)
	}
	return nil
}

func toHex(i *big.Int) string {
	return fmt.Sprintf("0x%s", i.Text(16))
}

type InsertionParametersJSON struct {
	InputHash    string     `json:"inputHash"`
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
	paramsJson.InputHash = toHex(&p.InputHash)
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

	err = fromHex(&p.InputHash, params.InputHash)
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
	Ar  [2]string    `json:"ar"`
	Bs  [2][2]string `json:"bs"`
	Krs [2]string    `json:"krs"`
}

func (p *Proof) MarshalJSON() ([]byte, error) {
	const fpSize = 32
	var buf bytes.Buffer
	_, err := p.Proof.WriteRawTo(&buf)
	if err != nil {
		return nil, err
	}
	proofBytes := buf.Bytes()
	proofJson := ProofJSON{}
	proofHexNumbers := [8]string{}
	for i := 0; i < 8; i++ {
		proofHexNumbers[i] = toHex(new(big.Int).SetBytes(proofBytes[i*fpSize : (i+1)*fpSize]))
	}

	proofJson.Ar = [2]string{proofHexNumbers[0], proofHexNumbers[1]}
	proofJson.Bs = [2][2]string{
		{proofHexNumbers[2], proofHexNumbers[3]},
		{proofHexNumbers[4], proofHexNumbers[5]},
	}
	proofJson.Krs = [2]string{proofHexNumbers[6], proofHexNumbers[7]}

	return json.Marshal(proofJson)
}

func (p *Proof) UnmarshalJSON(data []byte) error {
	var proofJson ProofJSON
	err := json.Unmarshal(data, &proofJson)
	if err != nil {
		return err
	}
	proofHexNumbers := [8]string{
		proofJson.Ar[0],
		proofJson.Ar[1],
		proofJson.Bs[0][0],
		proofJson.Bs[0][1],
		proofJson.Bs[1][0],
		proofJson.Bs[1][1],
		proofJson.Krs[0],
		proofJson.Krs[1],
	}
	proofInts := [8]big.Int{}
	for i := 0; i < 8; i++ {
		err = fromHex(&proofInts[i], proofHexNumbers[i])
		if err != nil {
			return err
		}
	}
	const fpSize = 32
	proofBytes := make([]byte, 8*fpSize)
	for i := 0; i < 8; i++ {
		copy(proofBytes[i*fpSize:(i+1)*fpSize], proofInts[i].Bytes())
	}

	p.Proof = groth16.NewProof(ecc.BN254)

	_, err = p.Proof.ReadFrom(bytes.NewReader(proofBytes))
	if err != nil {
		return err
	}
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
