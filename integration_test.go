package main

import (
	"io"
	"net/http"
	"strings"
	"testing"
	"worldcoin/gnark-mbu/logging"
	"worldcoin/gnark-mbu/go-circuit"
	"worldcoin/gnark-mbu/server"
)

const ProverAddress = "localhost:8080"
const MetricsAddress = "localhost:9999"

func TestMain(m *testing.M) {
	logging.Logger().Info().Msg("Setting up the prover")
	ps, err := prover.Setup(3, 2)
	if err != nil {
		panic(err)
	}
	cfg := server.Config{
		ProverAddress:  ProverAddress,
		MetricsAddress: MetricsAddress,
	}
	logging.Logger().Info().Msg("Starting the server")
	instance := server.Run(&cfg, ps)
	logging.Logger().Info().Msg("Running the tests")
	defer func() {
		instance.RequestStop()
		instance.AwaitStop()
	}()
	m.Run()
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

func TestHappyPath(t *testing.T) {
	body := `{
		"inputHash":"0x5057a31740d54d42ac70c05e0768fb770c682cb2c559bdd03fe4099f7e584e4f",
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
}

func TestWrongInput(t *testing.T) {
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
