// Based on Prometheus example
// https://github.com/prometheus/client_golang/blob/main/examples/middleware/httpmiddleware/httpmiddleware.go
package wrapped_http

import (
	"net/http"

	"github.com/prometheus/client_golang/prometheus"
	"github.com/prometheus/client_golang/prometheus/promauto"
	"github.com/prometheus/client_golang/prometheus/promhttp"
)

type WrappedServeMux interface {
	http.Handler
	Handle(pattern string, handler http.Handler)
}

type serveMuxWithMetrics struct {
	server   *http.ServeMux
	buckets  []float64
	registry prometheus.Registerer
}

func (s *serveMuxWithMetrics) Handle(pattern string, handler http.Handler) {
	reg := prometheus.WrapRegistererWith(prometheus.Labels{"endpoint_pattern": pattern}, s.registry)

	requestsInFlight := promauto.With(reg).NewGauge(
		prometheus.GaugeOpts{
			Name: "http_requests_in_flight",
			Help: "Tracks the number of HTTP requests.",
		},
	)
	requestsTotal := promauto.With(reg).NewCounterVec(
		prometheus.CounterOpts{
			Name: "http_requests_total",
			Help: "Tracks the number of HTTP requests.",
		}, []string{"method", "code"},
	)
	requestDuration := promauto.With(reg).NewHistogramVec(
		prometheus.HistogramOpts{
			Name:    "http_request_duration_seconds",
			Help:    "Tracks the latencies for HTTP requests.",
			Buckets: s.buckets,
		},
		[]string{"method", "code"},
	)
	requestSize := promauto.With(reg).NewSummaryVec(
		prometheus.SummaryOpts{
			Name: "http_request_size_bytes",
			Help: "Tracks the size of HTTP requests.",
		},
		[]string{"method", "code"},
	)
	responseSize := promauto.With(reg).NewSummaryVec(
		prometheus.SummaryOpts{
			Name: "http_response_size_bytes",
			Help: "Tracks the size of HTTP responses.",
		},
		[]string{"method", "code"},
	)

	// Wraps the provided http.Handler to observe the request result with the provided metrics.
	wrappedHandler :=
		promhttp.InstrumentHandlerInFlight(
			requestsInFlight,
			promhttp.InstrumentHandlerCounter(
				requestsTotal,
				promhttp.InstrumentHandlerDuration(
					requestDuration,
					promhttp.InstrumentHandlerRequestSize(
						requestSize,
						promhttp.InstrumentHandlerResponseSize(
							responseSize,
							handler,
						),
					),
				),
			),
		)

	s.server.Handle(pattern, wrappedHandler)
}

func (s *serveMuxWithMetrics) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	s.server.ServeHTTP(w, r)
}

func NewWrappedServeMuxWithMetrics(registry prometheus.Registerer, buckets []float64) WrappedServeMux {
	if buckets == nil {
		buckets = prometheus.ExponentialBuckets(0.1, 1.5, 5)
	}

	return &serveMuxWithMetrics{
		server:   http.NewServeMux(),
		buckets:  buckets,
		registry: registry,
	}
}
