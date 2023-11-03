import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Ext.Vector

import FormalVerification
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness
import FormalVerification.SemanticEquivalence

import FormalVerification.InsertionCircuit
import FormalVerification.DeletionCircuit

open SemaphoreMTB (F Order)

variable [Fact (Nat.Prime Order)]

open SemaphoreMTB renaming DeletionProof_4_4_30_4_4_30 → gDeletionProof

open SemaphoreMTB renaming InsertionProof_4_30_4_4_30 → gInsertionProof

theorem insertion_is_set_circuit
  [Fact (perfect_hash poseidon₂)]
  {Tree: MerkleTree F poseidon₂ D}
  (StartIndex: Nat) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (PostRoot : F)
  {ixBound: StartIndex + B < Order}:
  (gInsertionProof ↑StartIndex Tree.root IdComms MerkleProofs fun newRoot => PostRoot = newRoot) ↔
  (insertion_circuit Tree ↑StartIndex IdComms MerkleProofs fun newRoot => PostRoot = newRoot) := by
  rw [InsertionProof_uncps]
  apply insertion_is_set
  simp [ixBound]

theorem deletion_is_set_circuit [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F B) (xs_small : are_indices_in_range (D+1) DeletionIndices) (k : F -> Prop) :
  TreeDeleteCircuit Tree DeletionIndices xs_small (fun newTree => k newTree.root) ↔
  let items := (list_of_items Tree DeletionIndices xs_small)
  let proofs := (list_of_proofs Tree DeletionIndices xs_small)
  gDeletionProof DeletionIndices Tree.root items proofs k := by
  rw [DeletionProof_uncps]
  simp [deletion_loop_equivalence']

theorem before_insertion_all_items_zero
  [Fact (perfect_hash poseidon₂)]
  {Tree: MerkleTree F poseidon₂ D}
  (StartIndex: Nat) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (k: F -> Prop)
  {ixBound: StartIndex + B < Order}:
  gInsertionProof ↑StartIndex Tree.root IdComms MerkleProofs k →
  (∀ i ∈ [StartIndex:StartIndex + B], MerkleTree.item_at_nat Tree i = some 0) := by
  rw [InsertionProof_looped]
  apply before_insertion_all_items_zero_loop
  simp [ixBound]

theorem after_deletion_all_zeroes_batch [Fact (perfect_hash poseidon₂)]
  (Tree₁ Tree₂ : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F B) (xs_small : are_indices_in_range (D+1) DeletionIndices) :
  let items := (list_of_items Tree₁ DeletionIndices xs_small)
  let proofs := (list_of_proofs Tree₁ DeletionIndices xs_small)
  gDeletionProof DeletionIndices Tree₁.root items proofs k →
  TreeDeleteCircuitZero DeletionIndices xs_small := by
  simp [DeletionProof_uncps]
  rw [<-deletion_loop_equivalence']
  apply after_deletion_all_zeroes

def main : IO Unit := pure ()
