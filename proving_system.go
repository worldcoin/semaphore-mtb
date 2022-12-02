package main

import (
	"bytes"
	"encoding/binary"
	"encoding/json"
	"fmt"
	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/iden3/go-iden3-crypto/keccak256"
	"io"
	"math/big"
	"os"
)

type Parameters struct {
	InputHash    big.Int
	StartIndex   uint32
	PreRoot      big.Int
	PostRoot     big.Int
	IdComms      []big.Int
	MerkleProofs [][]big.Int
}

func (p *Parameters) ValidateShape(treeDepth uint32, batchSize uint32) error {
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

type ParametersJSON struct {
	InputHash    string     `json:"inputHash"`
	StartIndex   uint32     `json:"startIndex"`
	PreRoot      string     `json:"preRoot"`
	PostRoot     string     `json:"postRoot"`
	IdComms      []string   `json:"identityCommitments"`
	MerkleProofs [][]string `json:"merkleProofs"`
}

func toBytesLE(b []byte) []byte {
	for i := 0; i < len(b)/2; i++ {
		b[i], b[len(b)-i-1] = b[len(b)-i-1], b[i]
	}
	return b
}

func (p *Parameters) ComputeInputHash() {
	var data []byte
	buf := new(bytes.Buffer)
	binary.Write(buf, binary.LittleEndian, p.StartIndex)
	data = append(data, buf.Bytes()...)
	data = append(data, toBytesLE(p.PreRoot.Bytes())...)
	data = append(data, toBytesLE(p.PostRoot.Bytes())...)
	// TODO Errors and val reuse
	for _, v := range p.IdComms {
		tmp := toBytesLE(v.Bytes())
		// extend to 32 bytes if necessary
		if len(v.Bytes()) < 32 {
			tmp = append(tmp, make([]byte, 32-len(v.Bytes()))...)
		}
		data = append(data, tmp...)
	}
	hashBytes := toBytesLE(keccak256.Hash(data))
	p.InputHash.SetBytes(hashBytes)
}

func (p *Parameters) MarshalJSON() ([]byte, error) {
	paramsJson := ParametersJSON{}
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

func (p *Parameters) UnmarshalJSON(data []byte) error {

	var params ParametersJSON

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

//func (params *ParametersJSON) ToParameters() (*Parameters, error) {
//	var p = Parameters{}
//	p.InputHash = big.Int{}
//	_, success = p.InputHash.SetString(params.InputHash, 0)
//	if !success {
//		return nil, fmt.Errorf("invalid number: %s", params.InputHash)
//	}
//	p.StartIndex = params.StartIndex
//	p.PreRoot, err = big.NewInt(0).SetString(params.PreRoot, 10)
//	if err != nil {
//		return p, err
//	}
//	p.PostRoot, err = big.NewInt(0).SetString(params.PostRoot, 10)
//	if err != nil {
//		return p, err
//	}
//}

type Proof struct {
	Proof groth16.Proof
}

func (p *Proof) MarshalJSON() ([]byte, error) {
	type ProofJSON struct {
		Ar  [2]string    `json:"ar"`
		Bs  [2][2]string `json:"bs"`
		Krs [2]string    `json:"krs"`
	}

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

type ProvingSystem struct {
	TreeDepth        uint32
	BatchSize        uint32
	ProvingKey       groth16.ProvingKey
	VerifyingKey     groth16.VerifyingKey
	ConstraintSystem frontend.CompiledConstraintSystem
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

func Setup(treeDepth uint32, batchSize uint32) (*ProvingSystem, error) {
	proofs := make([][]frontend.Variable, batchSize)
	for i := 0; i < int(batchSize); i++ {
		proofs[i] = make([]frontend.Variable, treeDepth)
	}
	circuit := MbuCircuit{
		Depth:        int(treeDepth),
		BatchSize:    int(batchSize),
		IdComms:      make([]frontend.Variable, batchSize),
		MerkleProofs: proofs,
	}
	ccs, err := frontend.Compile(ecc.BN254, r1cs.NewBuilder, &circuit)
	if err != nil {
		return nil, err
	}
	pk, vk, err := groth16.Setup(ccs)
	if err != nil {
		return nil, err
	}
	return &ProvingSystem{treeDepth, batchSize, pk, vk, ccs}, nil
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

	read, err := io.ReadFull(r, intBuf[:])
	totalRead += int64(read)
	if err != nil {
		return totalRead, err
	}
	ps.TreeDepth = binary.BigEndian.Uint32(intBuf[:])

	read, err = io.ReadFull(r, intBuf[:])
	totalRead += int64(read)
	if err != nil {
		return totalRead, err
	}
	ps.BatchSize = binary.BigEndian.Uint32(intBuf[:])

	ps.ProvingKey = groth16.NewProvingKey(ecc.BN254)
	keyRead, err := ps.ProvingKey.UnsafeReadFrom(r)
	totalRead += keyRead
	if err != nil {
		return totalRead, err
	}

	ps.VerifyingKey = groth16.NewVerifyingKey(ecc.BN254)
	keyRead, err = ps.VerifyingKey.UnsafeReadFrom(r)
	totalRead += keyRead
	if err != nil {
		return totalRead, err
	}

	ps.ConstraintSystem = groth16.NewCS(ecc.BN254)
	keyRead, err = ps.ConstraintSystem.ReadFrom(r)
	totalRead += keyRead
	if err != nil {
		return totalRead, err
	}

	return totalRead, nil
}

func (ps *ProvingSystem) ExportSolidity(writer io.Writer) error {
	return ps.VerifyingKey.ExportSolidity(writer)
}

func (ps *ProvingSystem) Prove(params *Parameters) (*Proof, error) {
	if err := params.ValidateShape(ps.TreeDepth, ps.BatchSize); err != nil {
		return nil, err
	}
	idComms := make([]frontend.Variable, ps.BatchSize)
	for i := 0; i < int(ps.BatchSize); i++ {
		idComms[i] = params.IdComms[i]
	}
	proofs := make([][]frontend.Variable, ps.BatchSize)
	for i := 0; i < int(ps.BatchSize); i++ {
		proofs[i] = make([]frontend.Variable, ps.TreeDepth)
		for j := 0; j < int(ps.TreeDepth); j++ {
			proofs[i][j] = params.MerkleProofs[i][j]
		}
	}
	assignment := MbuCircuit{
		InputHash:    params.InputHash,
		StartIndex:   params.StartIndex,
		PreRoot:      params.PreRoot,
		PostRoot:     params.PostRoot,
		IdComms:      idComms,
		MerkleProofs: proofs,
	}
	witness, err := frontend.NewWitness(&assignment, ecc.BN254)
	if err != nil {
		return nil, err
	}
	Logger().Info().Msg("generating proof")
	proof, err := groth16.Prove(ps.ConstraintSystem, ps.ProvingKey, witness)
	if err != nil {
		return nil, err
	}
	Logger().Info().Msg("proof generated successfully")
	return &Proof{proof}, nil
}
