import ProvenZk

import FormalVerification
import FormalVerification.Utils
import FormalVerification.Poseidon

open SemaphoreMTB (F Order)

abbrev D := 30
abbrev B := 4
open SemaphoreMTB renaming VerifyProof_31_30 → gVerifyProof

lemma ProofRound_uncps {direction: Bool} {hash: F} {sibling: F} {k: F -> Prop} :
    SemaphoreMTB.ProofRound direction.toZMod hash sibling k ↔
    k (match direction with
    | false => poseidon₂ vec![sibling, hash]
    | true => poseidon₂ vec![hash, sibling]) := by
    cases direction <;>
      simp [SemaphoreMTB.ProofRound, Gates.is_bool, Gates.select, Gates.is_bool, Poseidon2_uncps]

def proof_rounds (Siblings : Vector F (n+1)) (PathIndices : Vector F n) (k : F -> Prop) : Prop :=
  match n with
  | Nat.zero => k Siblings.head
  | Nat.succ _ => SemaphoreMTB.ProofRound PathIndices.head Siblings.tail.head Siblings.head fun next =>
    proof_rounds (next ::ᵥ Siblings.tail.tail) PathIndices.tail k

lemma proof_rounds_uncps
  {Leaf : F}
  {Siblings : Vector F n}
  {PathIndices : Vector Bool n}
  {k : F -> Prop}:
  proof_rounds (Leaf ::ᵥ Siblings) (Vector.map Bool.toZMod PathIndices) k ↔
  k (MerkleTree.recover poseidon₂ PathIndices.reverse Siblings.reverse Leaf) := by
  induction PathIndices, Siblings using Vector.inductionOn₂ generalizing Leaf with
  | nil =>
    simp [is_vector_binary]
    rfl
  | @cons n ix sib ixes sibs ih =>
    simp [proof_rounds, MerkleTree.recover_snoc, ProofRound_uncps, ih]
    rfl

lemma VerifyProof_looped (PathIndices: Vector F D) (Siblings: Vector F (D+1)) (k: F -> Prop):
    gVerifyProof Siblings PathIndices k =
      proof_rounds Siblings PathIndices k := by
    unfold gVerifyProof
    simp [proof_rounds]
    rw [←Vector.ofFn_get (v := PathIndices)]
    rw [←Vector.ofFn_get (v := Siblings)]
    rfl

lemma VerifyProof_uncps {PathIndices: Vector Bool D} {Siblings: Vector F D} {Item : F} {k : F -> Prop}:
    gVerifyProof (Item ::ᵥ Siblings) (Vector.map Bool.toZMod PathIndices) k ↔
    k (MerkleTree.recover poseidon₂ PathIndices.reverse Siblings.reverse Item) := by
    simp [VerifyProof_looped, proof_rounds_uncps]
