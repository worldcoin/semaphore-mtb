import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle

import FormalVerification
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness

open InsertionProof (F Order)

variable [Fact (Nat.Prime Order)]

abbrev D := 3

def poseidon₂ : Hash F 2 := fun a => (Poseidon.perm Constants.x5_254_3 vec![0, a.get 0, a.get 1]).get 0

lemma Poseidon2_uncps (a b : F) (k : F -> Prop) : InsertionProof.Poseidon2 a b k ↔ k (poseidon₂ vec![a, b]) := by
    simp [InsertionProof.Poseidon2, poseidon₂, poseidon_3_correct, getElem]
    rfl

lemma ProofRound_uncps {direction: F} {hash: F} {sibling: F} {k: F -> Prop} : 
    InsertionProof.ProofRound direction hash sibling k ↔
    is_bit direction ∧ k (match Dir.nat_to_dir direction.val with
    | Dir.left => poseidon₂ vec![sibling, hash]
    | Dir.right => poseidon₂ vec![hash, sibling]) := by
    simp [InsertionProof.ProofRound, Gates.is_bool, Gates.select, Gates.is_bool]
    intro hb
    cases hb <;> {
        simp [*]
        simp [Dir.nat_to_dir, ZMod.val, Order]
        rw [Poseidon2_uncps]
    }

def proof_rounds (Siblings : Vector F (n+1)) (PathIndices : Vector F n) (k : F -> Prop) : Prop :=
  match n with
  | Nat.zero => k Siblings.head
  | Nat.succ _ => InsertionProof.ProofRound PathIndices.head Siblings.tail.head Siblings.head fun next =>
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
    InsertionProof.VerifyProof_4_3 Siblings PathIndices k =
      proof_rounds Siblings PathIndices k := by
    unfold InsertionProof.VerifyProof_4_3
    simp [proof_rounds]
    rw [←Vector.ofFn_get (v := PathIndices)]
    rw [←Vector.ofFn_get (v := Siblings)]
    rfl

lemma VerifyProof_31_30_uncps {PathIndices: Vector F D} {Siblings: Vector F (D+1)} {k : F -> Prop}:
    InsertionProof.VerifyProof_4_3 (Siblings.head ::ᵥ Siblings.tail) PathIndices k ↔
    is_vector_binary PathIndices ∧ k (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec PathIndices) Siblings.tail Siblings.head) := by
    simp only [VerifyProof_looped, proof_rounds_uncps]

def natToBin : Nat → List Dir
  | 0     => [Dir.left]
  | 1     => [Dir.right]
  | n + 2 => natToBin ((n + 2) / 2) ++ natToBin (n % 2)
decreasing_by {
  simp_wf
  simp_arith
  --simp [Nat.div_le_self, Nat.mod_le]
  sorry
  -- case _ => {
  --   apply Nat.div_le_self
  -- }
  -- case _ => {
  --   simp_arith
  -- }
}

def zmodToBin {n} (x : ZMod n) : List Dir := (natToBin (ZMod.val x)).reverse

def toBinaryVector {n} (x : ZMod n) (d : Nat) : Vector Dir d :=
  ⟨List.takeI d (zmodToBin x), by simp⟩

lemma InsertionRound_uncps {Index: F} {Item: F} {PrevRoot: F} {Proof: Vector F D} {k: F -> Prop} :
  InsertionProof.InsertionRound_3 Index Item PrevRoot Proof k ↔
  MerkleTree.recover_tail poseidon₂ (toBinaryVector Index D) Proof 0 = PrevRoot ∧
  k (MerkleTree.recover_tail poseidon₂ (toBinaryVector Index D) Proof Item) := by
  sorry

-- Write insertion_rounds