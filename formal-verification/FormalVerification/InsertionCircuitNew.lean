import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Ext.Vector

import FormalVerification
import FormalVerification.SemanticEquivalence

open SemaphoreMTB (F Order)

variable [Fact (Nat.Prime Order)]

open SemaphoreMTB renaming VerifyProof_31_30 → gVerifyProof
open SemaphoreMTB renaming InsertionRound_30_30 → gInsertionRound
open SemaphoreMTB renaming InsertionProof_4_30_4_4_30 → gInsertionProof

set_option pp.coercions false

------------ MISC

lemma proof_of_set
  {F d}
  (H : Hash F 2)
  [Fact (perfect_hash H)]
  (Tree : MerkleTree F H d)
  (ix : Vector Dir d)
  (item : F):
  (MerkleTree.proof (MerkleTree.set Tree ix item) ix) = MerkleTree.proof Tree ix := by
  induction d with
  | zero =>
    simp [MerkleTree.set, MerkleTree.proof]
  | succ d ih =>
    cases Tree
    simp [MerkleTree.set, MerkleTree.proof, MerkleTree.tree_for]
    split
    . rename_i hdir
      have : Dir.swap (Dir.swap (Vector.head ix)) = Dir.right := by
        rw [hdir]
        simp [Dir.swap]
      have : Vector.head ix = Dir.right := by
        rw [<-this]
        simp [Dir.swap]
        cases ix.head
        . simp
        . simp
      rw [this]
      simp [MerkleTree.set, MerkleTree.left, MerkleTree.right]
      simp [Vector.vector_eq_cons]
      rw [ih]
    . rename_i hdir
      have : Dir.swap (Dir.swap (Vector.head ix)) = Dir.left := by
        rw [hdir]
        simp [Dir.swap]
      have : Vector.head ix = Dir.left := by
        rw [<-this]
        simp [Dir.swap]
        cases ix.head
        . simp
        . simp
      rw [this]
      simp [MerkleTree.set, MerkleTree.left, MerkleTree.right]
      simp [Vector.vector_eq_cons]
      rw [ih]

------------

def TreeInsert [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Path : Vector F D) (Item : F) : MerkleTree F poseidon₂ D :=
  MerkleTree.set Tree (Dir.create_dir_vec Path).reverse Item

theorem insertion_round_item_validation [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Path : Vector F D) (Proof : Vector F D) (k : F → Prop) :
  insertion_round Path Item Tree.root Proof k → (0:F) = MerkleTree.item_at Tree (Dir.create_dir_vec Path).reverse := by
  intro ⟨H, _⟩
  rw [MerkleTree.recover_tail_equals_recover_reverse] at H
  exact Eq.symm (MerkleTree.proof_ceritfies_item _ _ _ _ H)

theorem insertion_round_proof_validation [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Path : Vector F D) (Item: F) (Proof : Vector F D) (k : F → Prop) :
  insertion_round Path Item Tree.root Proof k → Proof = (MerkleTree.proof Tree (Dir.create_dir_vec Path).reverse).reverse := by
  intro ⟨H, _⟩
  rw [MerkleTree.recover_tail_equals_recover_reverse] at H
  apply Eq.symm
  rw [Vector.vector_reverse_eq]
  exact MerkleTree.recover_proof_reversible H

theorem insertion_round_uncps [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Path : Vector F D) (Item : F) (k : F → Prop) :
  let newTree := (MerkleTree.set Tree (Dir.create_dir_vec Path).reverse Item)
  let item := MerkleTree.item_at newTree (Dir.create_dir_vec Path).reverse
  let proof := (MerkleTree.proof newTree (Dir.create_dir_vec Path).reverse).reverse
  MerkleTree.item_at Tree (Dir.create_dir_vec Path).reverse = (0:F) →
  (insertion_round Path item Tree.root proof k ↔
  k (TreeInsert Tree Path Item).root) := by
  simp
  intro hzero
  unfold insertion_round
  unfold TreeInsert
  simp [MerkleTree.recover_tail_equals_recover_reverse]
  simp [MerkleTree.recover_proof_is_root]
  intro
  rw [<-hzero]
  rw [proof_of_set]
  simp [MerkleTree.recover_proof_is_root]
