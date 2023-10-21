import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Ext.Vector

import FormalVerification
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness
import FormalVerification.SemanticEquivalence

import FormalVerification.InsertionCircuit

open SemaphoreMTB (F Order)

variable [Fact (Nat.Prime Order)]

open SemaphoreMTB renaming VerifyProof_31_30 → gVerifyProof
open SemaphoreMTB renaming DeletionRound_30_30 → gDeletionRound
open SemaphoreMTB renaming DeletionProof_4_4_30_4_4_30 → gDeletionProof
open SemaphoreMTB renaming InsertionRound_30_30 → gInsertionRound
open SemaphoreMTB renaming InsertionProof_4_30_4_4_30 → gInsertionProof

set_option pp.coercions false

------------------ MISC

lemma vector_zmod_to_bit_last {n d : Nat} {xs : Vector (ZMod n) (d+1)} :
  (vector_zmod_to_bit xs).last = (zmod_to_bit xs.last) := by
  simp [vector_zmod_to_bit, Vector.last]

lemma dropLast_symm {n} {xs : Vector Bit d} :
  Vector.map (fun i => @Bit.toZMod n i) (Vector.dropLast xs) = (Vector.map (fun i => @Bit.toZMod n i) xs).dropLast := by
  induction xs using Vector.inductionOn with
  | h_nil =>
    simp [Vector.dropLast, Vector.map]
  | h_cons ih₁ =>
    rename_i x₁ xs
    induction xs using Vector.inductionOn with
    | h_nil =>
      simp [Vector.dropLast, Vector.map]
    | h_cons _ =>
      rename_i x₂ xs
      simp [Vector.vector_list_vector]
      simp [ih₁]

lemma zmod_to_bit_to_zmod {n : Nat} [Fact (n > 1)] {x : (ZMod n)} (h : is_bit x):
  Bit.toZMod (zmod_to_bit x) = x := by
  simp [is_bit] at h
  cases h with
  | inl =>
    subst_vars
    simp [zmod_to_bit, Bit.toZMod]
  | inr =>
    subst_vars
    simp [zmod_to_bit, ZMod.val_one, Bit.toZMod]

lemma bit_to_zmod_to_bit {n : Nat} [Fact (n > 1)] {x : Bit}:
  zmod_to_bit (@Bit.toZMod n x) = x := by
  cases x with
  | zero =>
    simp [zmod_to_bit, Bit.toZMod]
  | one =>
    simp [zmod_to_bit, Bit.toZMod]
    simp [zmod_to_bit, ZMod.val_one, Bit.toZMod]

lemma vector_zmod_to_bit_to_zmod {n d : Nat} [Fact (n > 1)] {xs : Vector (ZMod n) d} (h : is_vector_binary xs) :
  Vector.map Bit.toZMod (vector_zmod_to_bit xs) = xs := by
  induction xs using Vector.inductionOn with
  | h_nil => simp
  | h_cons ih =>
    simp [is_vector_binary_cons] at h
    cases h
    simp [vector_zmod_to_bit]
    simp [vector_zmod_to_bit] at ih
    rw [zmod_to_bit_to_zmod]
    rw [ih]
    assumption
    assumption

lemma vector_bit_to_zmod_to_bit {d n : Nat} [Fact (n > 1)] {xs : Vector Bit d} :
  vector_zmod_to_bit (Vector.map (fun i => @Bit.toZMod n i) xs) = xs := by
  induction xs using Vector.inductionOn with
  | h_nil => simp
  | h_cons ih =>
    rename_i x xs
    simp [vector_zmod_to_bit]
    simp [vector_zmod_to_bit] at ih
    simp [ih]
    rw [bit_to_zmod_to_bit]

lemma vector_zmod_to_bit_last' {n d : Nat} [Fact (n > 1)] {xs : Vector (ZMod n) (d+1)} (h : is_vector_binary xs) :
  Vector.map Bit.toZMod (Vector.dropLast (vector_zmod_to_bit xs)) = (Vector.dropLast xs) := by
  simp [dropLast_symm]
  rw [vector_zmod_to_bit_to_zmod]
  assumption

------------------

def TreeDelete [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Skip : Bit) (Path : Vector F D) (Item : F) (Proof : Vector F D) (k : F → Prop): Prop :=
  match Skip with
  | Bit.zero => 
      MerkleTree.item_at Tree (Dir.create_dir_vec Path).reverse = Item ∧
      MerkleTree.proof Tree (Dir.create_dir_vec Path).reverse = Proof.reverse ∧
      k (MerkleTree.set Tree (Dir.create_dir_vec Path).reverse 0).root
  | Bit.one => k Tree.root

def TreeDeletePrep [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (Proof : Vector F D) (k : F → Prop): Prop :=
  ∃path, nat_to_bits_le (D+1) Index.val = some path ∧
  TreeDelete Tree (path.last) (Vector.map Bit.toZMod path.dropLast) Item Proof k

theorem deletion_round_uncps [Fact (perfect_hash poseidon₂)] (Tree : MerkleTree F poseidon₂ D) (Skip : Bit) (Path : Vector F D) (Item: F) (Proof : Vector F D) (k : F → Prop):
  deletion_round Tree.root Skip Path Item Proof k ↔
  TreeDelete Tree Skip Path Item Proof k := by
  unfold deletion_round
  unfold TreeDelete
  split
  . simp
    simp [MerkleTree.recover_tail_equals_recover_reverse]
    rw [<-MerkleTree.recover_equivalence]
    simp [and_assoc]
    intro hitem_at hproof
    rw [MerkleTree.proof_insert_invariant (ix := (Vector.reverse (Dir.create_dir_vec Path))) (tree := Tree) (old := Item) (new := (0:F)) (proof := Vector.reverse Proof)]
    rw [<-MerkleTree.recover_equivalence]
    apply And.intro
    rw [hitem_at]
    rw [hproof]
  . simp

theorem deletion_round_prep_uncps [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (Proof : Vector F D) (k : F → Prop) : 
  deletion_round_prep Tree.root Index Item Proof k ↔
  TreeDeletePrep Tree Index Item Proof k := by
  unfold deletion_round_prep
  unfold TreeDeletePrep
  simp [deletion_round_uncps]
  apply Iff.intro
  . rintro ⟨ixbin, _⟩
    casesm* (_ ∧ _)
    have : nat_to_bits_le (D+1) Index.val = some (vector_zmod_to_bit ixbin) := by
      apply recover_binary_zmod'_to_bits_le
      . simp
      . assumption
      . rename_i h _ _ _; simp[h]
    rw [this]
    simp [←Dir.create_dir_vec_bit]
    simp [vector_zmod_to_bit_last]
    rw [vector_zmod_to_bit_last']
    assumption
    assumption
  . rintro ⟨ixbin, h⟩
    casesm* (_ ∧ _)
    rename_i l r
    let t : Vector F (D+1) := (Vector.map Bit.toZMod ixbin)
    refine ⟨t, ?_⟩
    refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
    . apply recover_binary_of_to_bits
      simp [l]
    . apply vector_binary_of_bit_to_zmod
    . simp [Bit.toZMod, is_bit, Vector.last]
      split
      simp
      simp
    . simp
      simp [dropLast_symm] at r
      have : (Vector.last ixbin) = zmod_to_bit (Vector.last (Vector.map (fun i => @Bit.toZMod Order i) ixbin)) := by
        rw [<-vector_zmod_to_bit_last]
        simp [vector_bit_to_zmod_to_bit]
      rw [<-this]
      assumption

def main : IO Unit := pure ()