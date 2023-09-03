# 📦 Semaphore Merkle Tree Batcher (SMTB)

SMTB is a service for batch processing of Merkle tree updates. It is designed to be used in conjunction with [Semaphore](https://github.com/semaphore-protocol/semaphore). It accepts Merkle tree updates and batches them together into a single one. This is useful for reducing the number of transactions that need to be submitted to the blockchain. The correctness of the batched Merkle tree update is assured through the generation of a SNARK (generated through [gnark](https://github.com/ConsenSys/gnark)).

## Table of Contents
1. [Features](#features)
2. [Usage](#usage)
3. [Benchmarks](#benchmarks)
4. [Running](#running)
5. [Docker](#docker)
6. [Contributing](#contributing)

## Features

- [x] Merkle tree batch update in gnark
- [x] Poseidon Hash in gnark
- [x] Keccak / sha3 in gnark (for aggregation of public inputs)
- [x] Full batch update circuit
- [ ] REST API
- [ ] Proving service
- [ ] Serialize circuit and proving key

## Usage  
This part explains the existing cli commands.  
  
1. setup - builds a circuit with provided batch size and depth, compiles it and writes it to a file.  
    Flags:  
        1. output *file path* - A path used to output a file  
        2. tree-depth *n* - Merkle tree depth  
        3. batch-size *n* - Batch size for Merkle tree updates
2. export-solidity  - Reads a key file (generated from setup), and writes a solidity verifier contract.  
    Flags:  
        1. keys-file *file path*  
        2. Optional: output *file* - Outputs to a file, if not provided, it will output to stdandard output  
3. gen-test-params - Generates test params given the batch size and tree depth. 
    Flags:  
        1. tree-depth *n* - Depth of the mock merkle tree  
        2. batch-size *n* - Batch size for merkle tree updates  
4. start - starts a api server with /prove and /metrics endpoints  
    Flags:  
        1. keys-file *file path* - Proving system file  
        2. Optional: json-logging *0/1* - Enables json logging  
        3. Optional: prover-address *address* - Address for the prover server, defaults to localhost:3001  
        4. Optional: metrics-address *address* - Address for the metrics server, defaults to localhost:9998  
5. prove - Reads a prover system file, generates and returns proof based on prover parameters  
    Flags:  
        1. keys-file *file path* - Proving system file  
6. verify - Takes a hash of all public inputs and verifies it with a prover system  
    Flags:  
        1. keys-file *file path* - Proving system file  
        2. input-hash *hash* - Hash of all public inputs  
7. r1cs - Builds an r1cs and writes it to a file  
    Flags:  
        1. output *file path* - File to be writen to  
        2. tree-depth *n* - Depth of a tree  
        3. batch-size *n* - Batch size for Merkle tree updates
8. extract-circuit - Transpiles the circuit from gnark to Lean
    Flags:  
        1. output *file path* - File to be writen to
        2. tree-depth *n* - Merkle tree depth  
        3. batch-size *n* - Batch size for Merkle tree updates

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

## Contributing

We welcome your pull requests! But also consider the following:  

1. Fork this repo from `master` branch.  
2. If you added code that should be tested, please add tests.  
3. If you changed the CLI flags, please update this readme in your PR.  
4. Ensure that CI tests suite passes.  

When you submit code changes, your submissions are understood to be under the same MIT License that covers the project.  
Feel free to contact the maintainers if that's a concern.  

Report bugs using github issues. 