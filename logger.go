package main

import (
	"github.com/rs/zerolog"
	"os"
)

var log = zerolog.New(zerolog.ConsoleWriter{Out: os.Stdout, TimeFormat: "15:04:05"}).With().Timestamp().Logger()

func Logger() *zerolog.Logger {
	return &log
}
