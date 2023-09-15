import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle

import FormalVerification
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness

open SemaphoreMTB (F Order)

variable [Fact (Nat.Prime Order)]

abbrev D := 30 -- Tree depth
abbrev B := 4 -- Batch sizes
abbrev gVerifyProof := SemaphoreMTB.VerifyProof_31_30
abbrev gDeletionRound := SemaphoreMTB.DeletionRound_30_30
abbrev gDeletionProof := SemaphoreMTB.DeletionProof_4_4_30_4_4_30

def poseidon₂ : Hash F 2 := fun a => (Poseidon.perm Constants.x5_254_3 vec![0, a.get 0, a.get 1]).get 0

lemma Poseidon2_uncps (a b : F) (k : F -> Prop) : SemaphoreMTB.Poseidon2 a b k ↔ k (poseidon₂ vec![a, b]) := by
    simp [SemaphoreMTB.Poseidon2, poseidon₂, poseidon_3_correct, getElem]
    rfl

/-!
`ProofRound_uncps` proves that `SemaphoreMTB.ProofRound` is equivalent to a
single iteration of `MerkleTree.recover_tail`
-/
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

/-!
`proof_rounds` rewrites `SemaphoreMTB.VerifyProof_31_30` with recursion using `proof_rounds`
-/
def proof_rounds (Siblings : Vector F (n+1)) (PathIndices : Vector F n) (k : F -> Prop) : Prop :=
  match n with
  | Nat.zero => k Siblings.head
  | Nat.succ _ => SemaphoreMTB.ProofRound PathIndices.head Siblings.tail.head Siblings.head fun next =>
    proof_rounds (next ::ᵥ Siblings.tail.tail) PathIndices.tail k

/-!
`proof_rounds_uncps` rewrites `proof_rounds` using the corresponding operations of `MerkleTree` library
-/
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

/-!
`VerifyProof_looped` proves that `SemaphoreMTB.VerifyProof_31_30` is identical to `proof_rounds`
-/
lemma VerifyProof_looped (PathIndices: Vector F D) (Siblings: Vector F (D+1)) (k: F -> Prop):
    gVerifyProof Siblings PathIndices k =
      proof_rounds Siblings PathIndices k := by
    unfold gVerifyProof
    simp [proof_rounds]
    rw [←Vector.ofFn_get (v := PathIndices)]
    rw [←Vector.ofFn_get (v := Siblings)]
    rfl

/-!
`VerifyProof_uncps` proves that `SemaphoreMTB.VerifyProof_31_30` is identical to `MerkleTree.recover_tail`
-/
lemma VerifyProof_uncps {PathIndices: Vector F D} {Siblings: Vector F (D+1)} {k : F -> Prop}:
    gVerifyProof (Siblings.head ::ᵥ Siblings.tail) PathIndices k ↔
    is_vector_binary PathIndices ∧ k (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec PathIndices) Siblings.tail Siblings.head) := by
    simp only [VerifyProof_looped, proof_rounds_uncps]

-- /-!
-- We need to prove that `DeletionRound_30` checks that `MerkleTree.recover_tail` = `root` and returns `MerkleTree.recover_tail` with empty Leaf:
-- this is shown in `DeletionRound_uncps`.
-- Then we need to show that `DeletionProof_4_4_30_4` is continuous application of `DeletionLoop`
-- -/

-- -- Helper for proving `DeletionRound_uncps`
-- lemma double_prop {a b c : Prop} : (a ∧ b ∧ a ∧ c) ↔ (a ∧ b ∧ c) := by
--   simp
--   tauto

-- /-!
-- `DeletionRound_uncps` proves that a single round of the deletion loop corresponds to checking that
-- the result of `MerkleTree.recover_tail` matches `Root` and returns the hash of the merkle tree with empty Leaf
-- -/
-- lemma DeletionRound_uncps {Root: F} {Index: F} {Item: F} {Proof: Vector F D} {k: F -> Prop} :
--   gDeletionRound Root Index Item Proof k ↔
--   ∃out : Vector F D, recover_binary_zmod' out = Index ∧ is_vector_binary out ∧
--   MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) Proof Item = Root ∧
--   k (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) Proof 0) := by
--   unfold gDeletionRound
--   -- Is there a way to automatically unfold from gDeletionRound?
--   unfold SemaphoreMTB.DeletionRound_30_30
--   simp [VerifyProof_looped]
--   simp [Gates.eq]
--   simp [proof_rounds_uncps]
--   simp [Gates.to_binary]
--   simp [and_assoc]
--   apply exists_congr
--   simp
--   intros
--   subst_vars
--   rename_i gate_0 h
--   simp [double_prop]
--   rw [←Vector.ofFn_get (v := gate_0)]
--   rw [←Vector.ofFn_get (v := gate_0)] at h
--   rw [←Vector.ofFn_get (v := Proof)]
--   tauto

-- /-!
-- `deletion_rounds` rewrites `DeletionProof_4_4_30_4` using pattern matching and recursion on the batch size
-- -/
-- def deletion_rounds (DeletionIndices: Vector F n) (PreRoot: F) (IdComms: Vector F n) (MerkleProofs: Vector (Vector F D) n)  (k : F -> Prop) : Prop :=
--   match n with
--   | Nat.zero => k PreRoot
--   | Nat.succ _ => gDeletionRound PreRoot DeletionIndices.head IdComms.head MerkleProofs.head fun next =>
--     deletion_rounds DeletionIndices.tail next IdComms.tail MerkleProofs.tail k

-- /-!
-- `DeletionLoop` rewrites `DeletionProof_4_4_30_4` using pattern matching and recursion on the batch size through by chaining
-- calls to `MerkleTree.recover_tail`. Ultimately we show that `DeletionLoop` is formally identical to `DeletionProof_4_4_30_4`
-- -/
-- def DeletionLoop {n} (DeletionIndices: Vector F n) (PreRoot: F) (IdComms: Vector F n) (MerkleProofs: Vector (Vector F D) n) (k : F -> Prop) : Prop :=
--   match n with
--   | Nat.zero => k PreRoot
--   | Nat.succ _ =>
--     ∃out : Vector F D, recover_binary_zmod' out = DeletionIndices.head ∧ is_vector_binary out ∧
--     MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) MerkleProofs.head IdComms.head = PreRoot ∧
--     DeletionLoop DeletionIndices.tail ( MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) MerkleProofs.head 0) IdComms.tail MerkleProofs.tail k

-- lemma deletion_rounds_uncps {n}
--   {DeletionIndices: Vector F n} {PreRoot: F} {IdComms: Vector F n} {MerkleProofs: Vector (Vector F D) n} {k : F -> Prop}:
--   deletion_rounds DeletionIndices PreRoot IdComms MerkleProofs k ↔
--   DeletionLoop DeletionIndices PreRoot IdComms MerkleProofs k := by
--   induction DeletionIndices, IdComms, MerkleProofs using Vector.inductionOn₃ generalizing PreRoot with
--   | nil => 
--     unfold deletion_rounds
--     unfold DeletionLoop
--     rfl
--   | cons => 
--     unfold deletion_rounds
--     unfold DeletionLoop
--     simp [DeletionRound_uncps]
--     rename_i ih
--     simp [ih]

-- set_option maxHeartbeats 2000000000
-- lemma DeletionProof_looped (DeletionIndices: Vector F B) (PreRoot: F) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (k: F -> Prop) :
--     gDeletionProof DeletionIndices PreRoot IdComms MerkleProofs k =
--       deletion_rounds DeletionIndices PreRoot IdComms MerkleProofs k := by
--         unfold gDeletionProof
--         simp [deletion_rounds]
--         rw [←Vector.ofFn_get (v := DeletionIndices)]
--         rw [←Vector.ofFn_get (v := IdComms)]
--         rw [←Vector.ofFn_get (v := MerkleProofs)]
--         rfl

-- /-!
-- `DeletionProof_uncps` is the key lemma which shows that `DeletionProof_4_4_30_4` and `DeletionLoop` are equivalent
-- -/
-- lemma DeletionProof_uncps {DeletionIndices: Vector F B} {PreRoot: F} {IdComms: Vector F B} {MerkleProofs: Vector (Vector F D) B} {k: F -> Prop}:
--     gDeletionProof DeletionIndices PreRoot IdComms MerkleProofs k ↔
--     DeletionLoop DeletionIndices PreRoot IdComms MerkleProofs k := by
--     simp only [DeletionProof_looped, deletion_rounds_uncps]
