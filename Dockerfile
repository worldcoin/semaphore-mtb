FROM golang:1.20.3-alpine as builder

WORKDIR /app

COPY go.mod go.sum ./
RUN go mod download && go mod verify

COPY . .

ENV CGO_ENABLED=0
RUN go build -v -o /usr/local/bin/gnark-mbu .

FROM gcr.io/distroless/base-debian11:nonroot

COPY --from=builder /usr/local/bin/gnark-mbu /usr/local/bin/gnark-mbu
VOLUME /mtb

ENTRYPOINT [ "gnark-mbu" ]
CMD [ "start", "--keys-file", "/mtb/keys"]
