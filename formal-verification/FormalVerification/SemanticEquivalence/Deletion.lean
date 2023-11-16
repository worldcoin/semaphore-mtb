import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Misc

import FormalVerification
import FormalVerification.Utils
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness

import FormalVerification.SemanticEquivalence.Verification

open SemaphoreMTB (F Order)

open SemaphoreMTB renaming DeletionRound_30_30 → gDeletionRound
open SemaphoreMTB renaming DeletionProof_4_4_30_4_4_30 → gDeletionProof

-- Deletion round semantic equivalence

lemma sub_zero_is_eq {a b cond : F} {k: F -> Prop}:
    (fun gate_2 =>
    ∃gate_3, gate_3 = Gates.sub a b ∧      -- gate_3 = a - b
    ∃gate_4, Gates.is_zero gate_3 gate_4 ∧ -- gate_4 = (a - b) == 0 = a == b
    ∃gate_5, Gates.or gate_4 cond gate_5 ∧ -- gate_5 = (a == b) ∨ cond
    Gates.eq gate_5 (1:F) ∧                -- gate_5 == 1
    ∃gate_7, Gates.select cond b gate_2 gate_7 ∧ -- return $ if cond then b else gate_2
    k gate_7) = (fun gate_2 => is_bit cond ∧ match zmod_to_bit cond with
                  | Bit.zero => (a = b) ∧ k gate_2 -- Update the root
                  | Bit.one => k b  -- Skip flag set, don't update the root
                ) := by
  funext g2
  unfold Gates.select
  simp only [or_rw]
  unfold Gates.sub
  unfold Gates.is_zero
  unfold Gates.is_bool
  unfold Gates.eq
  simp
  apply Iff.intro
  . intros; casesm* (∃ _, _), (_∧ _)
    rename (cond = 0 ∨ cond = 1) => hp
    cases hp
    . simp at *; subst_vars; simp at *; subst_vars; simp at *
      apply And.intro
      . apply eq_of_sub_eq_zero; assumption
      . tauto
    . subst_vars
      apply And.intro
      . tauto
      . simp at *; subst_vars; assumption
  . rintro ⟨is_b, rest⟩
    cases is_b <;> (
      subst_vars
      conv at rest => whnf
    )
    . cases rest; subst_vars; simp; assumption
    . simp
      cases h: decide (a - b = 0) with
      | false =>
        simp at h;
        exists 0
        apply And.intro
        . tauto
        . exists 1
      | true =>
        simp at h;
        exists 1;
        apply And.intro
        . tauto
        . exists 1

def deletion_round (Root: F) (Skip : Bit) (Path : Vector F D) (Item: F) (Proof: Vector F D) (k: F -> Prop) : Prop :=
  match Skip with
    | Bit.zero => (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec Path) Proof Item = Root) ∧
                k (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec Path) Proof 0) -- Update the root
    | Bit.one => k Root  -- Skip flag set, don't update the root

def deletion_round_prep (Root: F) (Index: F) (Item: F) (Proof: Vector F D) (k: F -> Prop) : Prop :=
  ∃out: Vector F (D+1), recover_binary_zmod' out = Index ∧ is_vector_binary out ∧
  is_bit out.last ∧ deletion_round Root (zmod_to_bit out.last) (out.dropLast) Item Proof k

lemma DeletionRound_uncps {Root: F} {Index: F} {Item: F} {Proof: Vector F D} {k: F -> Prop} :
  gDeletionRound Root Index Item Proof k ↔
  deletion_round_prep Root Index Item Proof k := by
  unfold gDeletionRound
  simp only [sub_zero_is_eq]
  simp [VerifyProof_looped, proof_rounds_uncps]
  simp [Gates.to_binary, and_assoc]
  apply exists_congr
  simp
  intros
  subst_vars
  rename_i gate_0 h
  rw [←Vector.ofFn_get (v := gate_0)]
  rw [←Vector.ofFn_get (v := gate_0)] at h
  rw [←Vector.ofFn_get (v := Proof)]
  rw [and_iff_right]
  tauto
  have : is_vector_binary (gate_0.dropLast) := by
    simp at h
    apply is_vector_binary_dropLast
    assumption
  rw [←Vector.ofFn_get (v := gate_0)]
  rw [←Vector.ofFn_get (v := gate_0)] at this
  assumption

def deletion_rounds {n} (DeletionIndices: Vector F n) (PreRoot: F) (IdComms: Vector F n) (MerkleProofs: Vector (Vector F D) n) (k : F -> Prop) : Prop :=
  match n with
  | Nat.zero => k PreRoot
  | Nat.succ _ => gDeletionRound PreRoot DeletionIndices.head IdComms.head MerkleProofs.head fun next =>
    deletion_rounds DeletionIndices.tail next IdComms.tail MerkleProofs.tail k

def DeletionLoop {n} (DeletionIndices: Vector F n) (PreRoot: F) (IdComms: Vector F n) (MerkleProofs: Vector (Vector F D) n) (k : F -> Prop) : Prop :=
  match n with
  | Nat.zero => k PreRoot
  | Nat.succ _ =>
    deletion_round_prep PreRoot DeletionIndices.head IdComms.head MerkleProofs.head fun next =>
      DeletionLoop DeletionIndices.tail next IdComms.tail MerkleProofs.tail k

lemma deletion_rounds_uncps {n} {DeletionIndices: Vector F n} {PreRoot: F} {IdComms: Vector F n} {MerkleProofs: Vector (Vector F D) n} {k : F -> Prop}:
  deletion_rounds DeletionIndices PreRoot IdComms MerkleProofs k ↔
  DeletionLoop DeletionIndices PreRoot IdComms MerkleProofs k := by
  induction DeletionIndices, IdComms, MerkleProofs using Vector.inductionOn₃ generalizing PreRoot with
  | nil =>
    unfold deletion_rounds
    unfold DeletionLoop
    rfl
  | cons =>
    unfold deletion_rounds
    unfold DeletionLoop
    rename_i ih
    simp [ih]
    simp [DeletionRound_uncps, Dir.dropLastOrder]

lemma DeletionProof_looped (DeletionIndices: Vector F B) (PreRoot: F) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (k: F -> Prop) :
    gDeletionProof DeletionIndices PreRoot IdComms MerkleProofs k =
      deletion_rounds DeletionIndices PreRoot IdComms MerkleProofs k := by
        unfold gDeletionProof
        simp [deletion_rounds]
        rw [←Vector.ofFn_get (v := DeletionIndices)]
        rw [←Vector.ofFn_get (v := IdComms)]
        rw [←Vector.ofFn_get (v := MerkleProofs)]
        rfl

lemma DeletionProof_uncps {DeletionIndices: Vector F B} {PreRoot: F} {IdComms: Vector F B} {MerkleProofs: Vector (Vector F D) B} {k: F -> Prop}:
    gDeletionProof DeletionIndices PreRoot IdComms MerkleProofs k ↔
    DeletionLoop DeletionIndices PreRoot IdComms MerkleProofs k := by
    simp only [DeletionProof_looped, deletion_rounds_uncps]
