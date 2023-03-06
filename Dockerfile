FROM golang:1.20.1-alpine

WORKDIR /app

COPY go.mod go.sum ./
RUN go mod download && go mod verify

COPY . .
RUN go build -v -o /usr/local/bin/gnark-mbu .

VOLUME /mtb

ENTRYPOINT [ "gnark-mbu" ]
CMD [ "start", "--keys-file", "/mtb/keys"]
