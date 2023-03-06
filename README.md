# 📦 Semaphore Merkle Tree Batcher (SMTB)

SMTB is a service for batch processing of Merkle tree updates. It is designed to be used in conjunction with [Semaphore](https://github.com/semaphore-protocol/semaphore). It accepts Merkle tree updates and batches them together into a single one. This is useful for reducing the number of transactions that need to be submitted to the blockchain. The correctness of the batched Merkle tree update is assured through the generation of a SNARK (generated through [gnark](https://github.com/ConsenSys/gnark)).

## Features

- [x] Merkle tree batch update in gnark
- [x] Poseidon Hash in gnark
- [x] Keccak / sha3 in gnark (for aggregation of public inputs)
- [x] Full batch update circuit
- [ ] REST API
- [ ] Proving service
- [ ] Serialize circuit and proving key

## Benchmarks

Batch size: `100`
Tree depth: `20`
```
DBG prover done backend=groth16 curve=BN254 nbConstraints=6370011 took=11094.363542
```

## Running
```shell
go build .
gnark-mbu --keys-file path/to/keys/file
```

## Docker
```shell
docker build -t semaphore-mtb .

# /host/path/to/mtb should contain the keys file
docker run -it \
    --mount type=bind,source=host/path/to/mtb,target=/mtb \
    -p 3001:3001 \
    semaphore-mtb
```

Or in docker compose
```yaml
semaphore-mtb:
    # Path to the repo root directory
    build: ./semaphore-mtb
    volumes:
        - /host/path/to/mtb:/mtb
    ports:
        # Server
        - "3001:3001"
        # Metrics
        - "9998:9998"

docker compose build
docker compose up -d
```
