package prover

import (
	"bytes"
	"encoding/json"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/stretchr/testify/assert"
)

var proofBytes = []byte{
	0x2e, 0xfd, 0xc3, 0x48, 0x35, 0xcf, 0x3e, 0xf4, 0x0b, 0x28, 0xaf, 0x89, 0x69, 0x55, 0xf7, 0x5b,
	0xe3, 0x90, 0xf0, 0x24, 0x04, 0x75, 0x6a, 0x64, 0xf3, 0x0e, 0x8f, 0xf0, 0x16, 0x96, 0xf9, 0x50, 0x06, 0xd9,
	0xe6, 0x10, 0x00, 0x71, 0x8e, 0x6f, 0xfd, 0xca, 0x6d, 0x1c, 0x56, 0x5e, 0x85, 0x6f, 0xf1, 0x7b, 0xc3, 0x60,
	0xb9, 0x4a, 0xa8, 0xaf, 0xa5, 0x5b, 0x99, 0xbc, 0xa3, 0x61, 0x61, 0xee, 0x16, 0x6b, 0x7d, 0x44, 0x35, 0x36,
	0x48, 0x1e, 0x13, 0x81, 0x35, 0x30, 0x17, 0x34, 0xc8, 0x21, 0x3b, 0xa3, 0xc0, 0x94, 0x31, 0x76, 0xb1, 0x3c,
	0xfa, 0x42, 0x9c, 0x8c, 0x5d, 0xb9, 0xe8, 0xd9, 0x0b, 0x66, 0xf5, 0x20, 0x73, 0xdf, 0xfd, 0xd8, 0xa0, 0x8b,
	0x3a, 0xcd, 0x09, 0xca, 0x29, 0xec, 0xe9, 0x04, 0xa9, 0x8a, 0x66, 0x54, 0x8b, 0xcb, 0x76, 0xcd, 0x7f, 0xc0,
	0x04, 0xff, 0x8f, 0x67, 0x27, 0xbb, 0x10, 0xf8, 0xde, 0xad, 0x45, 0x70, 0x4d, 0x4d, 0xc9, 0xcf, 0xd7, 0xfc,
	0xf6, 0xb1, 0x6f, 0x9e, 0x9a, 0x2d, 0xf7, 0xe0, 0xdd, 0x32, 0x62, 0x36, 0x43, 0xa7, 0x50, 0xc2, 0xec, 0xd2,
	0x22, 0x86, 0x7e, 0x55, 0x52, 0x1d, 0x62, 0x9a, 0xfc, 0x9d, 0x9b, 0xd2, 0xfd, 0x20, 0x73, 0x1b, 0x37, 0xba,
	0x72, 0xb2, 0x28, 0x02, 0x35, 0x7e, 0x3d, 0x18, 0x91, 0x6c, 0x0d, 0x44, 0x9c, 0x0c, 0x23, 0xe6, 0xe0, 0x90,
	0x89, 0xf2, 0xf2, 0xde, 0x2a, 0xc6, 0x55, 0x53, 0xff, 0xec, 0xd0, 0x94, 0x71, 0xa5, 0xfc, 0x9a, 0xfc, 0x0c,
	0x16, 0xb7, 0xaa, 0x2e, 0x0b, 0x58, 0xa4, 0x08, 0xed, 0x8a, 0x19, 0x0f, 0xf7, 0x4e, 0x0a, 0x7b, 0x54, 0xff,
	0x8f, 0x35, 0x61, 0x0a, 0xdb, 0xf6, 0x07, 0x8a, 0xe3, 0xc8, 0x2c, 0xc3, 0x06, 0x8c, 0x82, 0x2d, 0x86, 0x36,
	0x11, 0x2a, 0xf5, 0x77, 0x3f, 0x08, 0x00, 0x00, 0x00, 0x01, 0x1a, 0x4d, 0x86, 0x2a, 0x56, 0xa3, 0x40, 0x65,
	0x20, 0x48, 0xd0, 0x57, 0x3e, 0x71, 0x01, 0x12, 0x2c, 0xe3, 0x44, 0xf5, 0x80, 0x41, 0x0c, 0x9d, 0x22, 0xda,
	0x6b, 0x8d, 0x30, 0x92, 0xa3, 0xfc, 0x0f, 0x36, 0x47, 0xb9, 0xc7, 0xc7, 0x8b, 0x43, 0xe3, 0x5f, 0x1e, 0x93,
	0x6e, 0xcf, 0x8f, 0x21, 0xfe, 0xfc, 0x9c, 0x53, 0xb4, 0x75, 0xe8, 0xc8, 0xb4, 0xe3, 0xa5, 0xc8, 0x47, 0x7c,
	0x5d, 0xf6, 0x26, 0xab, 0x61, 0x45, 0xbe, 0x94, 0xfe, 0x62, 0xf0, 0x29, 0x52, 0xb4, 0x1b, 0x48, 0x88, 0x00,
	0x1a, 0x33, 0x0b, 0x3e, 0xda, 0x7e, 0x1d, 0xd5, 0x83, 0x26, 0x13, 0x0b, 0x12, 0x05, 0x07, 0x8b, 0x03, 0x09,
	0x07, 0xe0, 0x13, 0x44, 0xa2, 0xb3, 0x41, 0xa1, 0x85, 0xaf, 0x9f, 0x96, 0xdb, 0x92, 0xc1, 0x10, 0x95, 0xf0,
	0xeb, 0x6f, 0x39, 0x2a, 0xf3, 0x8b, 0x5e, 0x53, 0xe2, 0x59, 0x88, 0xc6,
}

const proofJsonString =
	`{"ar":[` +
	`"0x2efdc34835cf3ef40b28af896955f75be390f02404756a64f30e8ff01696f950",` +
	`"0x6d9e61000718e6ffdca6d1c565e856ff17bc360b94aa8afa55b99bca36161ee"],` +
	`"bs":[[` +
	`"0x166b7d443536481e138135301734c8213ba3c0943176b13cfa429c8c5db9e8d9",` +
	`"0xb66f52073dffdd8a08b3acd09ca29ece904a98a66548bcb76cd7fc004ff8f67"],[` +
	`"0x27bb10f8dead45704d4dc9cfd7fcf6b16f9e9a2df7e0dd32623643a750c2ecd2",` +
	`"0x22867e55521d629afc9d9bd2fd20731b37ba72b22802357e3d18916c0d449c0c"]],` +
	`"krs":[` +
	`"0x23e6e09089f2f2de2ac65553ffecd09471a5fc9afc0c16b7aa2e0b58a408ed8a",` +
	`"0x190ff74e0a7b54ff8f35610adbf6078ae3c82cc3068c822d8636112af5773f08"],` +
	`"commitments":[[` +
	`"0x1a4d862a56a340652048d0573e7101122ce344f580410c9d22da6b8d3092a3fc",` +
	`"0xf3647b9c7c78b43e35f1e936ecf8f21fefc9c53b475e8c8b4e3a5c8477c5df6"]],` +
	`"commitmentPok":[` +
	`"0x26ab6145be94fe62f02952b41b4888001a330b3eda7e1dd58326130b1205078b",` +
	`"0x30907e01344a2b341a185af9f96db92c11095f0eb6f392af38b5e53e25988c6"]}`


func TestProof_MarshalJSON(t *testing.T) {
	var proof Proof
	proof.Proof = groth16.NewProof(ecc.BN254)
	_, err:= proof.Proof.ReadFrom(bytes.NewReader(proofBytes))
	if err != nil {t.Fatal(err)}

	marshalled, err := json.Marshal(&proof)
	if err != nil {t.Fatal(err)}

	assert.Equal(t, proofJsonString, string(marshalled))
}

func TestProof_UnmarshalJSON(t *testing.T) {
	var proof Proof
	if err := json.Unmarshal([]byte(proofJsonString), &proof); err != nil {
		t.Fatal(err)
	}

	var buf bytes.Buffer
	_, err := proof.Proof.WriteRawTo(&buf)
	if err != nil {t.Fatal(err)}

	assert.Equal(t, proofBytes, buf.Bytes())

}
