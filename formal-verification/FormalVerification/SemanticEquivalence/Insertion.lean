import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Misc

import FormalVerification
import FormalVerification.Utils
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness

import FormalVerification.SemanticEquivalence.Verification
import FormalVerification.SemanticEquivalence.Deletion

open SemaphoreMTB (F Order)

open SemaphoreMTB renaming InsertionRound_30_30 → gInsertionRound
open SemaphoreMTB renaming InsertionProof_4_30_4_4_30 → gInsertionProof

-- Insertion round semantic equivalence

def insertion_round (Path: Vector F D) (Item: F) (PrevRoot: F) (Proof: Vector F D) (k: F -> Prop) : Prop :=
  (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec Path) Proof 0 = PrevRoot) ∧
  k (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec Path) Proof Item)

def insertion_round_prep (Index: F) (Item: F) (PrevRoot: F) (Proof: Vector F D) (k: F -> Prop) : Prop :=
  ∃out: Vector F D, recover_binary_zmod' out = Index ∧ is_vector_binary out ∧
  insertion_round out Item PrevRoot Proof k

lemma InsertionRound_uncps {Index: F} {Item: F} {PrevRoot: F} {Proof: Vector F D} {k: F -> Prop} :
  gInsertionRound Index Item PrevRoot Proof k ↔
  insertion_round_prep Index Item PrevRoot Proof k := by
  simp [insertion_round_prep, insertion_round]
  simp [gInsertionRound]
  simp [Gates.to_binary, Gates.eq]
  simp [VerifyProof_looped, proof_rounds_uncps]
  simp [and_assoc]
  apply exists_congr
  intros
  simp [double_prop]
  rename_i gate
  rw [←Vector.ofFn_get (v := gate)]
  rw [←Vector.ofFn_get (v := Proof)]
  tauto

def insertion_rounds {n} (StartIndex: F) (PreRoot: F) (IdComms: Vector F n) (MerkleProofs: Vector (Vector F D) n) (k : F -> Prop) : Prop :=
  match n with
  | Nat.zero => k PreRoot
  | Nat.succ _ => gInsertionRound StartIndex IdComms.head PreRoot MerkleProofs.head fun next =>
    insertion_rounds (StartIndex + 1) next IdComms.tail MerkleProofs.tail k

def InsertionLoop {n} (StartIndex: F) (PreRoot: F) (IdComms: Vector F n) (MerkleProofs: Vector (Vector F D) n) (k : F -> Prop) : Prop :=
  match n with
  | Nat.zero => k PreRoot
  | Nat.succ _ =>
    insertion_round_prep StartIndex IdComms.head PreRoot MerkleProofs.head fun next =>
    InsertionLoop (StartIndex + 1) next IdComms.tail MerkleProofs.tail k

lemma insertion_rounds_uncps {n} {StartIndex: F} {PreRoot: F} {IdComms: Vector F n} {MerkleProofs: Vector (Vector F D) n} {k : F -> Prop}:
  insertion_rounds StartIndex PreRoot IdComms MerkleProofs k ↔
  InsertionLoop StartIndex PreRoot IdComms MerkleProofs k := by
  induction IdComms, MerkleProofs using Vector.inductionOn₂ generalizing StartIndex PreRoot with
  | nil =>
    unfold insertion_rounds
    unfold InsertionLoop
    rfl
  | cons =>
    unfold insertion_rounds
    unfold InsertionLoop
    simp [InsertionRound_uncps, insertion_round_prep, insertion_round]
    rename_i ih
    simp [ih]

lemma InsertionProof_looped (StartIndex: F) (PreRoot: F) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (k: F -> Prop) :
    gInsertionProof StartIndex PreRoot IdComms MerkleProofs k =
      insertion_rounds StartIndex PreRoot IdComms MerkleProofs k := by
        unfold gInsertionProof
        simp [insertion_rounds]
        simp [InsertionRound_uncps]
        simp [Gates.add]
        rw [add_assoc]
        rw [add_assoc]
        rw [←Vector.ofFn_get (v := IdComms)]
        rw [←Vector.ofFn_get (v := MerkleProofs)]
        rfl

lemma InsertionProof_uncps {StartIndex: F} {PreRoot: F} {IdComms: Vector F B} {MerkleProofs: Vector (Vector F D) B} {k: F -> Prop}:
    gInsertionProof StartIndex PreRoot IdComms MerkleProofs k ↔
    InsertionLoop StartIndex PreRoot IdComms MerkleProofs k := by
    simp only [InsertionProof_looped, insertion_rounds_uncps]
