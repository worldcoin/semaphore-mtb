package server

import (
	"context"
	"fmt"
	"net/http"
	"worldcoin/gnark-mbu/logging"
)

type RunningJob struct {
	stop   chan struct{}
	closed chan struct{}
}

func (server *RunningJob) RequestStop() {
	close(server.stop)
}

func (server *RunningJob) AwaitStop() {
	<-server.closed
}

func spawnJob(start func(), shutdown func()) RunningJob {
	stop := make(chan struct{})
	closed := make(chan struct{})
	go func() {
		<-stop
		shutdown()
		close(closed)
	}()
	go start()
	return RunningJob{stop: stop, closed: closed}
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
	return spawnJob(start, shutdown)
}

func combineJobs(jobs ...RunningJob) RunningJob {
	start := func() {}
	shutdown := func() {
		for _, job := range jobs {
			job.RequestStop()
		}
		for _, job := range jobs {
			job.AwaitStop()
		}
	}
	return spawnJob(start, shutdown)
}
