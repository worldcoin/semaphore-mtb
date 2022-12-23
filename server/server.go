package server

import (
	"context"
	"net/http"
	"time"
	"worldcoin/gnark-mbu/logging"

	"github.com/prometheus/client_golang/prometheus/promhttp"
	"worldcoin/gnark-mbu/prover"
)

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
		if r.Method != http.MethodGet {
			w.WriteHeader(http.StatusMethodNotAllowed)
			return
		}

		logging.Logger().Info().Msg("received prove request")
		go func() {
			time.Sleep(10 * time.Second)
			w.Write([]byte("hello"))
		}()
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
