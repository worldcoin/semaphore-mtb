package server

import (
	"context"
	"encoding/json"
	"fmt"
	"github.com/prometheus/client_golang/prometheus"
	"github.com/prometheus/client_golang/prometheus/collectors"
	"io"
	"net/http"
	"worldcoin/gnark-mbu/logging"
	"worldcoin/gnark-mbu/server/wrapped_http"

	"worldcoin/gnark-mbu/prover"

	"github.com/prometheus/client_golang/prometheus/promhttp"
)

type Error struct {
	StatusCode int
	Code       string
	Message    string
}

const DeletionMode = "deletion"
const InsertionMode = "insertion"

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
	Mode           string
}

func spawnServerJob(server *http.Server, label string) RunningJob {
	start := func() {
		err := server.ListenAndServe()
		if err != nil && err != http.ErrServerClosed {
			panic(fmt.Sprintf("%s failed: %s", label, err))
		}
	}
	shutdown := func() {
		logging.Logger().Info().Msgf("shutting down %s", label)
		err := server.Shutdown(context.Background())
		if err != nil {
			logging.Logger().Error().Err(err).Msgf("error when shutting down %s", label)
		}
		logging.Logger().Info().Msgf("%s shut down", label)
	}
	return SpawnJob(start, shutdown)
}

func Run(config *Config, provingSystem *prover.ProvingSystem) RunningJob {
	// Create non-global registry.
	registry := prometheus.NewRegistry()

	// Add go runtime metrics and process collectors.
	registry.MustRegister(
		collectors.NewGoCollector(),
		collectors.NewProcessCollector(collectors.ProcessCollectorOpts{}),
	)

	metricsMux := http.NewServeMux()
	metricsMux.Handle("/metrics", promhttp.HandlerFor(registry, promhttp.HandlerOpts{}))
	metricsServer := &http.Server{Addr: config.MetricsAddress, Handler: metricsMux}
	metricsJob := spawnServerJob(metricsServer, "metrics server")
	logging.Logger().Info().Str("addr", config.MetricsAddress).Msg("metrics server started")

	proverMux := wrapped_http.NewWrappedServeMuxWithMetrics(registry, nil)
	proverMux.Handle(
		"/prove",
		proveHandler{provingSystem: provingSystem, mode: config.Mode},
	)
	proverServer := &http.Server{Addr: config.ProverAddress, Handler: proverMux}
	proverJob := spawnServerJob(proverServer, "prover server")
	logging.Logger().Info().Str("addr", config.ProverAddress).Msg("app server started")

	return CombineJobs(metricsJob, proverJob)
}

type proveHandler struct {
	mode          string
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

	var proof *prover.Proof
	if handler.mode == InsertionMode {
		var params prover.InsertionParameters

		err = json.Unmarshal(buf, &params)
		if err != nil {
			malformedBodyError(err).send(w)
			return
		}

		proof, err = handler.provingSystem.ProveInsertion(&params)
	} else if handler.mode == DeletionMode {
		var params prover.DeletionParameters

		err = json.Unmarshal(buf, &params)
		if err != nil {
			malformedBodyError(err).send(w)
			return
		}

		proof, err = handler.provingSystem.ProveDeletion(&params)
	}

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

	if err != nil {
		logging.Logger().Error().Err(err).Msg("error writing response")
	}
}
