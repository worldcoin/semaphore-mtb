package main_test

import (
	"encoding/json"
	"io"
	"net/http"
	"strings"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/frontend"
	gnarkLogger "github.com/consensys/gnark/logger"

	"worldcoin/gnark-mbu/logging"
	"worldcoin/gnark-mbu/prover"
	"worldcoin/gnark-mbu/server"
)

const ProverAddress = "localhost:8080"
const MetricsAddress = "localhost:9999"

var mode string
var ps *prover.ProvingSystem

func TestMain(m *testing.M) {
	gnarkLogger.Set(*logging.Logger())
	logging.Logger().Info().Msg("Setting up the prover")
	var err error
	ps, err = prover.SetupInsertion(3, 2)
	if err != nil {
		panic(err)
	}
	cfg := server.Config{
		ProverAddress:  ProverAddress,
		MetricsAddress: MetricsAddress,
		Mode:           server.InsertionMode,
	}
	logging.Logger().Info().Msg("Starting the insertion server")
	instance := server.Run(&cfg, ps)
	logging.Logger().Info().Msg("Running the insertion tests")
	mode = server.InsertionMode
	m.Run()
	instance.RequestStop()
	instance.AwaitStop()
	cfg.Mode = server.DeletionMode
	ps, err = prover.SetupDeletion(3, 2)
	if err != nil {
		panic(err)
	}
	logging.Logger().Info().Msg("Starting the deletion server")
	instance = server.Run(&cfg, ps)
	logging.Logger().Info().Msg("Running the deletion tests")
	mode = server.DeletionMode
	m.Run()
	instance.RequestStop()
	instance.AwaitStop()
}

func TestWrongMethod(t *testing.T) {
	response, err := http.Get("http://localhost:8080/prove")
	if err != nil {
		t.Fatal(err)
	}
	if response.StatusCode != http.StatusMethodNotAllowed {
		t.Fatalf("Expected status code %d, got %d", http.StatusMethodNotAllowed, response.StatusCode)
	}
}

func TestInsertionHappyPath(t *testing.T) {
	if mode != server.InsertionMode {
		return
	}
	body := `{
		"startIndex":0,
		"preRoot":"0x18f43331537ee2af2e3d758d50f72106467c6eea50371dd528d57eb2b856d238",
		"postRoot":"0x2267bee7aae8ed55eb9aecff101145335ed1dd0a5a276a2b7eb3ae7d20e232d8",
		"identityCommitments":["0x1","0x2"],
		"merkleProofs": [
			["0x0","0x2098f5fb9e239eab3ceac3f27b81e481dc3124d55ffed523a839ee8446b64864","0x1069673dcdb12263df301a6ff584a7ec261a44cb9dc68df067a4774460b1f1e1"],
			["0x1","0x2098f5fb9e239eab3ceac3f27b81e481dc3124d55ffed523a839ee8446b64864","0x1069673dcdb12263df301a6ff584a7ec261a44cb9dc68df067a4774460b1f1e1"]
		]}`
	response, err := http.Post("http://localhost:8080/prove", "application/json", strings.NewReader(body))
	if err != nil {
		t.Fatal(err)
	}
	if response.StatusCode != http.StatusOK {
		t.Fatalf("Expected status code %d, got %d", http.StatusOK, response.StatusCode)
	}

	responseBody, err := io.ReadAll(response.Body)
	if err != nil {
		t.Fatal(err)
	}

	var ir prover.InsertionResponse
	if err = json.Unmarshal(responseBody, &ir); err != nil {
		t.Fatal(err)
	}

	var params prover.InsertionParameters
	if err = json.Unmarshal([]byte(body), &params); err != nil {
		t.Fatal(err)
	}

	versionedKzgHash := prover.KzgToVersionedHash(ir.Commitment4844)
	publicWitness, err := frontend.NewWitness(&prover.InsertionMbuCircuit{
		InputHash:          ir.InputHash,
		ExpectedEvaluation: *prover.BytesToBn254BigInt(ir.ExpectedEvaluation[:]),
		Commitment4844:     *prover.BytesToBn254BigInt(versionedKzgHash[:]),
		StartIndex:         params.StartIndex,
		PreRoot:            params.PreRoot,
		PostRoot:           params.PostRoot,
	}, ecc.BN254.ScalarField(), frontend.PublicOnly())
	if err != nil {
		t.Fatal(err)
	}

	if err = groth16.Verify(ir.Proof.Proof, ps.VerifyingKey, publicWitness); err != nil {
		t.Fatal(err)
	}
}

func TestDeletionHappyPath(t *testing.T) {
	if mode != server.DeletionMode {
		return
	}
	body := `{
		"inputHash":"0xdcd389a94b549222fadc9e335c358a3fe4d534155182f46927f82ea8491c7480",
		"deletionIndices":[0,2],
		"preRoot":"0xd11eefe87b985333c0d327b0cdd39a9641b5ac32c35c2bda84301ef3231a8ac",
		"postRoot":"0x1912415186579e1d9ff6282b76d081f0acd527d8549ea803385b1382d9498f35",
		"identityCommitments":["0x1","0x3"],
		"merkleProofs":[
			["0x2","0x20a3af0435914ccd84b806164531b0cd36e37d4efb93efab76913a93e1f30996","0x1069673dcdb12263df301a6ff584a7ec261a44cb9dc68df067a4774460b1f1e1"],
			["0x4","0x65e2c6cc08a36c4a943286bc91c216054a1981eb4f7570f67394ef8937a21b8","0x1069673dcdb12263df301a6ff584a7ec261a44cb9dc68df067a4774460b1f1e1"]
		]}`
	response, err := http.Post("http://localhost:8080/prove", "application/json", strings.NewReader(body))
	if err != nil {
		t.Fatal(err)
	}
	if response.StatusCode != http.StatusOK {
		t.Fatalf("Expected status code %d, got %d", http.StatusOK, response.StatusCode)
	}
}

func TestInsertionWrongInput(t *testing.T) {
	if mode != server.InsertionMode {
		return
	}
	body := `{
		"inputHash":"0x5057a31740d54d42ac70c05e0768fb770c682cb2c559bdd03fe4099f7e584e4f",
		"startIndex":0,
		"preRoot":"0x18f43331537ee2af2e3d758d50f72106467c6eea50371dd528d57eb2b856d238",
		"postRoot":"0x2267bee7aae8ed55eb9aecff101145335ed1dd0a5a276a2b7eb3ae7d20e232d8",
		"identityCommitments":["0x1","0x2"],
		"merkleProofs": [
			["0x0","0x0","0x0"],
			["0x1","0x0","0x0"]
		]}`
	response, err := http.Post("http://localhost:8080/prove", "application/json", strings.NewReader(body))
	if err != nil {
		t.Fatal(err)
	}
	if response.StatusCode != http.StatusBadRequest {
		t.Fatalf("Expected status code %d, got %d", http.StatusBadRequest, response.StatusCode)
	}
	responseBody, err := io.ReadAll(response.Body)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(responseBody), "proving_error") {
		t.Fatalf("Expected error message to be tagged with 'proving_error', got %s", string(responseBody))
	}

}

func TestDeletionWrongInput(t *testing.T) {
	if mode != server.DeletionMode {
		return
	}
	body := `{
		"inputHash":"0xdcd389a94b549222fadc9e335c358a3fe4d534155182f46927f82ea8491c7480",
		"deletionIndices":[0,2],
		"preRoot":"0xd11eefe87b985333c0d327b0cdd39a9641b5ac32c35c2bda84301ef3231a8ac",
		"postRoot":"0x1912415186579e1d9ff6282b76d081f0acd527d8549ea803385b1382d9498f35",
		"identityCommitments":["0x1","0x3"],
		"merkleProofs":[
			["0x2","0xD","0xD"],
			["0x4","0xD","0xD"]
		]}`
	response, err := http.Post("http://localhost:8080/prove", "application/json", strings.NewReader(body))
	if err != nil {
		t.Fatal(err)
	}
	if response.StatusCode != http.StatusBadRequest {
		t.Fatalf("Expected status code %d, got %d", http.StatusBadRequest, response.StatusCode)
	}
	responseBody, err := io.ReadAll(response.Body)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(responseBody), "proving_error") {
		t.Fatalf("Expected error message to be tagged with 'proving_error', got %s", string(responseBody))
	}
}

func TestDeletionBatchPadding(t *testing.T) {
	if mode != server.DeletionMode {
		return
	}
	body := `{
		"inputHash":"0x509d6e4ca8a621713cc5feb95de95cb4eed3c1127176d93da653fd3cc55db537",
		"deletionIndices":[0,8],
		"preRoot":"0xd11eefe87b985333c0d327b0cdd39a9641b5ac32c35c2bda84301ef3231a8ac",
		"postRoot":"0x22c58cf24838c2eb1701f2aa6e6a867e10237590dbdb423e4d3e053b121c44cb",
		"identityCommitments":["0x1","0x0"],
		"merkleProofs":[
			["0x2","0x20a3af0435914ccd84b806164531b0cd36e37d4efb93efab76913a93e1f30996","0x1069673dcdb12263df301a6ff584a7ec261a44cb9dc68df067a4774460b1f1e1"],
			["0x0","0x0","0x0"]
		]}`
	response, err := http.Post("http://localhost:8080/prove", "application/json", strings.NewReader(body))
	if err != nil {
		t.Fatal(err)
	}
	if response.StatusCode != http.StatusOK {
		t.Fatalf("Expected status code %d, got %d", http.StatusOK, response.StatusCode)
	}
}
