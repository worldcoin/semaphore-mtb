# 📦 Semaphore Merkle Tree Batcher (SMTB)

SMTB is a service for batch processing of Merkle tree updates. It is designed to be used in conjunction with [Semaphore](https://github.com/semaphore-protocol/semaphore). It accepts Merkle tree updates and batches them together into a single one. This is useful for reducing the number of transactions that need to be submitted to the blockchain. The correctness of the batched Merkle tree update is assured through the generation of a SNARK (generated through [gnark](https://github.com/ConsenSys/gnark)).

## Features

- [x] Merkle tree batch update in gnark
- [x] Poseidon Hash in gnark
- [x] Keccak / sha3 in gnark (for aggregation of public inputs)
- [ ] Full batch update circuit
- [ ] REST API
- [ ] Proving service