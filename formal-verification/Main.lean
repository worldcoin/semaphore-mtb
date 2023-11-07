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

theorem insertion_is_set_circuit
  [Fact (perfect_hash poseidon₂)]
  (Tree: MerkleTree F poseidon₂ D)
  (StartIndex: Nat) (IdComms: Vector F B) (xs_small : is_index_in_range_nat D (StartIndex + B)) (hzero : InsertionLoopZero Tree StartIndex IdComms xs_small) (k : F -> Prop) :
  TreeInsertCircuit Tree StartIndex IdComms xs_small (fun newTree => k newTree.root) ↔
  (let items := list_of_items_insert Tree StartIndex IdComms xs_small
  let proofs := list_of_proofs_insert Tree StartIndex IdComms xs_small
  SemaphoreMTB.InsertionProof_4_30_4_4_30 StartIndex Tree.root items proofs k) := by
  simp
  rw [InsertionProof_uncps]
  rw [insertion_loop_equivalence']
  simp [hzero]

theorem deletion_is_set_circuit [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F B) (xs_small : are_indices_in_range (D+1) DeletionIndices) (k : F -> Prop) :
  TreeDeleteCircuit Tree DeletionIndices xs_small (fun newTree => k newTree.root) ↔
  let items := (list_of_items_delete Tree DeletionIndices xs_small)
  let proofs := (list_of_proofs_delete Tree DeletionIndices xs_small)
  SemaphoreMTB.DeletionProof_4_4_30_4_4_30 DeletionIndices Tree.root items proofs k := by
  rw [DeletionProof_uncps]
  simp [deletion_loop_equivalence']

theorem before_insertion_all_zeroes_batch
  [Fact (perfect_hash poseidon₂)]
  (Tree: MerkleTree F poseidon₂ D)
  (StartIndex: Nat) (IdComms: Vector F B) (xs_small : is_index_in_range_nat D (StartIndex + B)) (k : F -> Prop) :
  let items := list_of_items_insert Tree StartIndex IdComms xs_small
  let proofs := list_of_proofs_insert Tree StartIndex IdComms xs_small
  SemaphoreMTB.InsertionProof_4_30_4_4_30 StartIndex Tree.root items proofs k →
  InsertionLoopZero Tree StartIndex IdComms xs_small := by
  simp [InsertionProof_uncps]
  apply before_insertion_all_zeroes

theorem after_deletion_all_zeroes_batch [Fact (perfect_hash poseidon₂)]
  (Tree₁ : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F B) (xs_small : are_indices_in_range (D+1) DeletionIndices) :
  let items := (list_of_items_delete Tree₁ DeletionIndices xs_small)
  let proofs := (list_of_proofs_delete Tree₁ DeletionIndices xs_small)
  SemaphoreMTB.DeletionProof_4_4_30_4_4_30 DeletionIndices Tree₁.root items proofs k →
  TreeDeleteCircuitZero DeletionIndices xs_small := by
  simp [DeletionProof_uncps]
  rw [<-deletion_loop_equivalence']
  apply after_deletion_all_zeroes

def main : IO Unit := pure ()
