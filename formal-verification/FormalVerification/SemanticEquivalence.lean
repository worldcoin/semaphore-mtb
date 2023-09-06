import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle

import FormalVerification
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness

open SemaphoreMTB (F Order)

variable [Fact (Nat.Prime Order)]

abbrev D := 3

def poseidon₂ : Hash F 2 := fun a => (Poseidon.perm Constants.x5_254_3 vec![0, a.get 0, a.get 1]).get 0

lemma Poseidon2_uncps (a b : F) (k : F -> Prop) : SemaphoreMTB.Poseidon2 a b k ↔ k (poseidon₂ vec![a, b]) := by
    simp [SemaphoreMTB.Poseidon2, poseidon₂, poseidon_3_correct, getElem]
    rfl

-- `ProofRound_uncps` proves that `SemaphoreMTB.ProofRound` is equivalent to a
-- single iteration of `MerkleTree.recover_tail`
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

-- `proof_rounds` rewrites `SemaphoreMTB.VerifyProof_31_30` with recursion using `proof_rounds`
def proof_rounds (Siblings : Vector F (n+1)) (PathIndices : Vector F n) (k : F -> Prop) : Prop :=
  match n with
  | Nat.zero => k Siblings.head
  | Nat.succ _ => SemaphoreMTB.ProofRound PathIndices.head Siblings.tail.head Siblings.head fun next =>
    proof_rounds (next ::ᵥ Siblings.tail.tail) PathIndices.tail k

-- `proof_rounds_uncps` rewrites `proof_rounds` using the corresponding operations of `MerkleTree` library
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

-- `VerifyProof_looped` proves that `SemaphoreMTB.VerifyProof_31_30` is identical to `proof_rounds`
lemma VerifyProof_looped (PathIndices: Vector F D) (Siblings: Vector F (D+1)) (k: F -> Prop):
    SemaphoreMTB.VerifyProof_31_30 Siblings PathIndices k =
      proof_rounds Siblings PathIndices k := by
    unfold SemaphoreMTB.VerifyProof_31_30
    simp [proof_rounds]
    rw [←Vector.ofFn_get (v := PathIndices)]
    rw [←Vector.ofFn_get (v := Siblings)]
    rfl

-- `VerifyProof_31_30_uncps` proves that `SemaphoreMTB.VerifyProof_31_30` is identical to `MerkleTree.recover_tail`
lemma VerifyProof_31_30_uncps {PathIndices: Vector F D} {Siblings: Vector F (D+1)} {k : F -> Prop}:
    SemaphoreMTB.VerifyProof_31_30 (Siblings.head ::ᵥ Siblings.tail) PathIndices k ↔
    is_vector_binary PathIndices ∧ k (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec PathIndices) Siblings.tail Siblings.head) := by
    simp only [VerifyProof_looped, proof_rounds_uncps]

-- We need to prove that `DeletionRound_3` is identical to `MerkleTree.recover_tail` = `root` and returns `MerkleTree.recover_tail` with empty Leaf.
-- This is shown in `DeletionRound_uncps`.
-- Then we need to show that `DeletionProof_2_2_3_2` is continuous application of `MerkleTree.recover_tail`

def natToBin : Nat → List Dir
  | 0     => [Dir.left]
  | 1     => [Dir.right]
  | n + 2 => natToBin ((n + 2) / 2) ++ natToBin (n % 2)
decreasing_by {
  simp_wf
  simp_arith
  sorry
}

def zmodToBin {n} (x : ZMod n) : List Dir := (natToBin (ZMod.val x)).reverse

def toBinaryVector {n} (x : ZMod n) (d : Nat) : Vector Dir d :=
  ⟨List.takeI d (zmodToBin x), by simp⟩

def toBinaryVectorZ {n} (x : ZMod n) (d : Nat) : Vector (ZMod n) d :=
  Vector.map Dir.toZMod (toBinaryVector x d)

-- lemma toBinary_uncps {a : ZMod N} {x : Vector (ZMod N) D} :
--   ∃out, Gates.to_binary a D out ↔ is_vector_binary out := by
--   sorry

-- def verify_proofs (Root: F) (Index: F) (Item: F) (MerkleProofs: Vector F (D+1)) (k: F -> Prop): Prop :=
--   SemaphoreMTB.VerifyProof_31_30 MerkleProofs (toBinaryVectorZ Index D) ↔ 

def deletion_round_loop (Root: F) (Paths: Vector F 3) (Item: F) (MerkleProofs: Vector F 3) (k: F -> Prop) : Prop :=
  SemaphoreMTB.VerifyProof_31_30 (Item ::ᵥ MerkleProofs) Paths fun computed_root =>
    computed_root = Root ∧ SemaphoreMTB.VerifyProof_31_30 (0 ::ᵥ MerkleProofs) Paths fun next_root => k next_root

-- VerifyProof_31_30_uncps {PathIndices: Vector F D} {Siblings: Vector F (D+1)} {k : F -> Prop}
-- VerifyProof_31_30_uncps = k ()

lemma DeletionRound_uncps {Root: F} {Index: F} {Item: F} {Proof: Vector F D} {k: F -> Prop} :
  SemaphoreMTB.DeletionRound_3 Root Index Item Proof k ↔
  ∃out : Vector F D, recover_binary_zmod' out = Index ∧ is_vector_binary out ∧
  MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) Proof Item = Root ∧
  k (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) Proof 0) := by
  unfold SemaphoreMTB.DeletionRound_3
  simp [VerifyProof_looped]
  simp [Gates.eq]
  simp [proof_rounds_uncps]
  simp [Gates.to_binary]
  -- This should be proven with `rfl`!
  sorry

def deletion_rounds (DeletionIndices: Vector F n) (PreRoot: F) (IdComms: Vector F n) (MerkleProofs: Vector (Vector F D) n)  (k : F -> Prop) : Prop :=
  match n with
  | Nat.zero => k PreRoot
  | Nat.succ _ => SemaphoreMTB.DeletionRound_3 PreRoot DeletionIndices.head IdComms.head MerkleProofs.head fun next =>
    deletion_rounds DeletionIndices.tail next IdComms.tail MerkleProofs.tail k

-- I need to write a loop of MerkleTree.recover_tail for `deletion_rounds_uncps`
-- I can match with number of IdComms and it returns F
def DeletionLoop {n} (DeletionIndices: Vector F n) (PreRoot: F) (IdComms: Vector F n) (MerkleProofs: Vector (Vector F D) n) : F :=
  match n with
  | Nat.zero => PreRoot
  | Nat.succ _ =>
    let new_root := MerkleTree.recover_tail poseidon₂ (toBinaryVector DeletionIndices.head D) MerkleProofs.head 0
    -- MerkleTree.recover_tail poseidon₂ (toBinaryVector DeletionIndices.head D) MerkleProofs.head IdComms.head = PreRoot ∧
    DeletionLoop DeletionIndices.tail new_root IdComms.tail MerkleProofs.tail

lemma deletion_rounds_uncps {n}
  {DeletionIndices: Vector F n} {PreRoot: F} {IdComms: Vector F n} {MerkleProofs: Vector (Vector F D) n} {k : F -> Prop}:
  deletion_rounds DeletionIndices PreRoot IdComms MerkleProofs k ↔ k (DeletionLoop DeletionIndices PreRoot IdComms MerkleProofs) := by
  induction DeletionIndices, IdComms, MerkleProofs using Vector.inductionOn₃ generalizing PreRoot with
  | nil => 
    unfold deletion_rounds
    unfold DeletionLoop
    rfl
  | cons => 
    unfold deletion_rounds
    unfold DeletionLoop
    simp [DeletionRound_uncps]
    rename_i ih
    simp [ih]
    -- I need to use `∃out : Vector F D, recover_binary_zmod' out = Index ∧ is_vector_binary out ∧`
    -- instead of `toBinaryVector`
    sorry

lemma DeletionProof_looped (DeletionIndices: Vector F 2) (PreRoot: F) (IdComms: Vector F 2) (MerkleProofs: Vector (Vector F D) 2) (k: F -> Prop) :
    SemaphoreMTB.DeletionProof_2_2_3_2 DeletionIndices PreRoot IdComms MerkleProofs k =
      deletion_rounds DeletionIndices PreRoot IdComms MerkleProofs k := by
        unfold SemaphoreMTB.DeletionProof_2_2_3_2
        simp [deletion_rounds]
        rw [←Vector.ofFn_get (v := DeletionIndices)]
        rw [←Vector.ofFn_get (v := IdComms)]
        rw [←Vector.ofFn_get (v := MerkleProofs)]
        rfl

lemma DeletionProof_2_2_3_2_uncps {DeletionIndices: Vector F 2} {PreRoot: F} {IdComms: Vector F 2} {MerkleProofs: Vector (Vector F D) 2} {k: F -> Prop}:
    SemaphoreMTB.DeletionProof_2_2_3_2 DeletionIndices PreRoot IdComms MerkleProofs k ↔
    k (DeletionLoop DeletionIndices PreRoot IdComms MerkleProofs) := by
    simp only [DeletionProof_looped, deletion_rounds_uncps]
