package server

import (
	"encoding/json"
	"io"
	"net/http"
	"worldcoin/gnark-mbu/logging"

	"github.com/prometheus/client_golang/prometheus/promhttp"
	"worldcoin/gnark-mbu/prover"
)

type Error struct {
	StatusCode int
	Code       string
	Message    string
}

func malformedBodyError(err error) *Error {
	return &Error{StatusCode: http.StatusBadRequest, Code: "malformed_body", Message: err.Error()}
}

func provingError(err error) *Error {
	return &Error{StatusCode: http.StatusBadRequest, Code: "proving_error", Message: err.Error()}
}

func unexpectedError(err error) *Error {
	return &Error{StatusCode: http.StatusInternalServerError, Code: "unexpected_error", Message: err.Error()}
}

func (error *Error) MarshalJSON() ([]byte, error) {
	return json.Marshal(map[string]string{
		"code":    error.Code,
		"message": error.Message,
	})
}

func (error *Error) send(w http.ResponseWriter) {
	w.WriteHeader(error.StatusCode)
	jsonBytes, err := error.MarshalJSON()
	if err != nil {
		jsonBytes = []byte(`{"code": "unexpected_error", "message": "failed to marshal error"}`)
	}
	length, err := w.Write(jsonBytes)
	if err != nil || length != len(jsonBytes) {
		logging.Logger().Error().Err(err).Msg("error writing response")
	}
}

type Config struct {
	ProverAddress  string
	MetricsAddress string
}

func Run(config *Config, provingSystem *prover.ProvingSystem) RunningJob {
	metricsMux := http.NewServeMux()
	metricsMux.Handle("/metrics", promhttp.Handler())
	metricsServer := &http.Server{Addr: config.MetricsAddress, Handler: metricsMux}
	metricsJob := spawnServerJob(metricsServer, "metrics server")
	logging.Logger().Info().Str("addr", config.MetricsAddress).Msg("metrics server started")

	proverMux := http.NewServeMux()
	proverMux.Handle("/prove", proveHandler{provingSystem: provingSystem})
	proverServer := &http.Server{Addr: config.ProverAddress, Handler: proverMux}
	proverJob := spawnServerJob(proverServer, "prover server")
	logging.Logger().Info().Str("addr", config.ProverAddress).Msg("app server started")

	return combineJobs(metricsJob, proverJob)
}

type proveHandler struct {
	provingSystem *prover.ProvingSystem
}

func (handler proveHandler) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		w.WriteHeader(http.StatusMethodNotAllowed)
		return
	}
	logging.Logger().Info().Msg("received prove request")
	buf, err := io.ReadAll(r.Body)
	if err != nil {
		malformedBodyError(err).send(w)
		return
	}
	var params prover.Parameters
	err = json.Unmarshal(buf, &params)
	if err != nil {
		malformedBodyError(err).send(w)
		return
	}
	proof, err := handler.provingSystem.Prove(&params)
	if err != nil {
		provingError(err).send(w)
		return
	}
	responseBytes, err := json.Marshal(&proof)
	if err != nil {
		unexpectedError(err).send(w)
		return
	}
	w.WriteHeader(http.StatusOK)
	_, err = w.Write(responseBytes)
}
