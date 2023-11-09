import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Misc

import FormalVerification
import FormalVerification.Utils
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness

open SemaphoreMTB (F Order)

abbrev D := 30 -- Tree depth
abbrev B := 4 -- Batch sizes
open SemaphoreMTB renaming VerifyProof_31_30 → gVerifyProof

instance : Fact (Nat.Prime SemaphoreMTB.Order) := Fact.mk (by apply bn256_Fr_prime)

-- Poseidon semantic equivalence
def poseidon₂ : Hash F 2 := fun a => (Poseidon.perm Constants.x5_254_3 vec![0, a.get 0, a.get 1]).get 0

lemma Poseidon2_uncps (a b : F) (k : F -> Prop) : SemaphoreMTB.Poseidon2 a b k ↔ k (poseidon₂ vec![a, b]) := by
    simp [SemaphoreMTB.Poseidon2, poseidon₂, poseidon_3_correct, getElem]
    rfl

-- Verify Proof semantic equivalence

lemma ProofRound_uncps {direction: F} {hash: F} {sibling: F} {k: F -> Prop} :
    SemaphoreMTB.ProofRound direction hash sibling k ↔
    is_bit direction ∧ k (match Dir.nat_to_dir direction.val with
    | Dir.left => poseidon₂ vec![sibling, hash]
    | Dir.right => poseidon₂ vec![hash, sibling]) := by
    simp [SemaphoreMTB.ProofRound, Gates.is_bool, Gates.select, Gates.is_bool]
    intro hb
    cases hb <;> {
        simp [*]
        simp [Dir.nat_to_dir, ZMod.val, Order]
        rw [Poseidon2_uncps]
    }


def proof_rounds (Siblings : Vector F (n+1)) (PathIndices : Vector F n) (k : F -> Prop) : Prop :=
  match n with
  | Nat.zero => k Siblings.head
  | Nat.succ _ => SemaphoreMTB.ProofRound PathIndices.head Siblings.tail.head Siblings.head fun next =>
    proof_rounds (next ::ᵥ Siblings.tail.tail) PathIndices.tail k

lemma proof_rounds_uncps
  {Leaf : F}
  {Siblings : Vector F n}
  {PathIndices : Vector F n}
  {k : F -> Prop}:
  proof_rounds (Leaf ::ᵥ Siblings) PathIndices k ↔
  is_vector_binary PathIndices ∧ k (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec PathIndices) Siblings Leaf) := by
  induction PathIndices, Siblings using Vector.inductionOn₂ generalizing Leaf with
  | nil =>
    simp [is_vector_binary]
    rfl
  | @cons n ix sib ixes sibs ih =>
    simp [MerkleTree.recover_tail_reverse_equals_recover, MerkleTree.recover_tail, proof_rounds]
    simp [ProofRound_uncps, is_vector_binary_cons, and_assoc, ih]
    intros
    rfl

lemma VerifyProof_looped (PathIndices: Vector F D) (Siblings: Vector F (D+1)) (k: F -> Prop):
    gVerifyProof Siblings PathIndices k =
      proof_rounds Siblings PathIndices k := by
    unfold gVerifyProof
    simp [proof_rounds]
    rw [←Vector.ofFn_get (v := PathIndices)]
    rw [←Vector.ofFn_get (v := Siblings)]
    rfl

lemma VerifyProof_uncps {PathIndices: Vector F D} {Siblings: Vector F (D+1)} {k : F -> Prop}:
    gVerifyProof (Siblings.head ::ᵥ Siblings.tail) PathIndices k ↔
    is_vector_binary PathIndices ∧ k (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec PathIndices) Siblings.tail Siblings.head) := by
    simp only [VerifyProof_looped, proof_rounds_uncps]
