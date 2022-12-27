package server

import (
	"context"
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

func Run(ps *prover.ProvingSystem) (chan struct{}, chan struct{}) {
	stop := make(chan struct{})
	stopMetrics := make(chan struct{})
	metricsClosed := make(chan struct{})
	stopProver := make(chan struct{})
	proverClosed := make(chan struct{})
	closed := make(chan struct{})
	go func() {
		<-stop
		close(stopMetrics)
		close(stopProver)
		<-metricsClosed
		<-proverClosed
		close(closed)
	}()

	metricsMux := http.NewServeMux()
	metricsMux.Handle("/metrics", promhttp.Handler())
	metricsServer := &http.Server{Addr: ":9999", Handler: metricsMux}
	go func() {
		metricsServer.ListenAndServe()
	}()
	go func() {
		<-stopMetrics
		logging.Logger().Info().Msg("shutting down metrics server")
		metricsServer.Shutdown(context.Background())
		logging.Logger().Info().Msg("metrics server shut down")
		close(metricsClosed)
	}()
	logging.Logger().Info().Str("addr", ":9999").Msg("metrics server started")

	proverMux := http.NewServeMux()

	proverMux.HandleFunc("/prove", func(w http.ResponseWriter, r *http.Request) {
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
		proof, err := ps.Prove(&params)
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
	})

	proverServer := &http.Server{Addr: ":3000", Handler: proverMux}
	go proverServer.ListenAndServe()
	logging.Logger().Info().Str("addr", ":3000").Msg("app server started")
	go func() {
		<-stopProver
		logging.Logger().Info().Msg("shutting down proof server")
		proverServer.Shutdown(context.Background())
		logging.Logger().Info().Msg("proof server shut down")
		close(proverClosed)
	}()

	return stop, closed
}
