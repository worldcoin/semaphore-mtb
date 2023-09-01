import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle

import FormalVerification
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness

open VerifyProof (F Order)

variable [Fact (Nat.Prime Order)]

def poseidon₂ : Hash F 2 := fun a => (Poseidon.perm Constants.x5_254_3 vec![0, a.get 0, a.get 1]).get 0

lemma Poseidon2_uncps (a b : F) (k : F -> Prop) : VerifyProof.Poseidon2 a b k ↔ k (poseidon₂ vec![a, b]) := by
    simp [VerifyProof.Poseidon2, poseidon₂, poseidon_3_correct, getElem]
    rfl