package keccak

import (
	"encoding/hex"
	"fmt"
	"strings"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

type testCircuit struct {
	In       []frontend.Variable
	Expected []frontend.Variable
}

func (c *testCircuit) Define(api frontend.API) error {
	sum, err := Keccak256(api, c.In)
	if err != nil {
		return err
	}

	for i := range c.Expected {
		api.AssertIsEqual(c.Expected[i], sum[i])
	}
	return nil
}

func TestKeccak256(t *testing.T) {
	// Helper function to convert a hex string to []frontend.Variable, 1 bit per element
	hexToBits := func(hexStr string) ([]frontend.Variable, error) {
		bytes, err := hex.DecodeString(hexStr)
		if err != nil {
			return nil, err
		}
		vars := make([]frontend.Variable, len(bytes)*8)
		for i, b := range bytes {
			for j := 0; j < 8; j++ {
				vars[i*8+j] = frontend.Variable((b >> j) & 1)
			}
		}
		return vars, nil
	}

	// Helper function to generate hex string in the format of b repeated count times
	var repeatHex = func(b byte, count int) string {
		hexStr := fmt.Sprintf("%02x", b)
		return strings.Repeat(hexStr, count)
	}

	// Table driven test cases
	testCases := []struct {
		input    string
		expected string
	}{
		// Test vectors from https://bob.nem.ninja/test-vectors.html
		{"", "C5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470"},
		{"CC", "EEAD6DBFC7340A56CAEDC044696A168870549A6A7F6F56961E84A54BD9970B8A"},
		{"41FB", "A8EACEDA4D47B3281A795AD9E1EA2122B407BAF9AABCB9E18B5717B7873537D2"},
		{"1F877C", "627D7BC1491B2AB127282827B8DE2D276B13D7D70FB4C5957FDF20655BC7AC30"},
		{"C1ECFDFC", "B149E766D7612EAF7D55F74E1A4FDD63709A8115B14F61FCD22AA4ABC8B8E122"},
		{"9F2FCC7C90DE090D6B87CD7E9718C1EA6CB21118FC2D5DE9F97E5DB6AC1E9C10",
			"24DD2EE02482144F539F810D2CAA8A7B75D0FA33657E47932122D273C3F6F6D1"},

		// Other test vectors verified against https://emn178.github.io/online-tools/keccak_256.html
		{"00", "bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a"},
		{repeatHex(0x00, 8), "011b4d03dd8c01f1049143cf9c4c817e4b167f1d1b83e5c6f0f10d89ba1e7bce"},
		{repeatHex(0xaa, 50), "04b992b0fda7cc35cb6c2ae5423b463e8f519efd70d8bab8394c1cd42839c2e2"},
		{repeatHex(0xfd, 640), "e1eb3e4b14a80a72d3decb952300b2efe0616341e0e55d98f60669873eb43d4d"},
		{repeatHex(0xcb, 1088), "5d89305ddc9240e623acebd3050d80102a35e7be3023314aff13bb0be19c0653"},
	}

	for _, tc := range testCases {
		in, err := hexToBits(tc.input)
		if err != nil {
			t.Fatal(err)
		}

		expected, err := hexToBits(tc.expected)
		if err != nil {
			t.Fatal(err)
		}

		circuit := &testCircuit{
			In:       in,
			Expected: expected,
		}

		witness := &testCircuit{
			In:       in,
			Expected: expected,
		}

		if err := test.IsSolved(circuit, witness, ecc.BN254.ScalarField()); err != nil {
			t.Fatalf("Test case with input '%s' failed: %s", tc.input, err)
		}
	}
}