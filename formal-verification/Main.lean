import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Ext.Vector

import FormalVerification
import FormalVerification.Utils
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness
import FormalVerification.Keccak.SemanticEquivalence
import FormalVerification.BinaryReps.Basic
import FormalVerification.BinaryReps.SemanticEquivalence


import FormalVerification.SemanticEquivalence

import FormalVerification.InsertionCircuit
import FormalVerification.DeletionCircuit

open SemaphoreMTB (F Order)

theorem insertion_is_set_circuit
  [Fact (CollisionResistant poseidon₂)]
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

theorem deletion_is_set_circuit [Fact (CollisionResistant poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F B) (xs_small : are_indices_in_range (D+1) DeletionIndices) (k : F -> Prop) :
  TreeDeleteCircuit Tree DeletionIndices xs_small (fun newTree => k newTree.root) ↔
  let items := (list_of_items_delete Tree DeletionIndices xs_small)
  let proofs := (list_of_proofs_delete Tree DeletionIndices xs_small)
  SemaphoreMTB.DeletionProof_4_4_30_4_4_30 DeletionIndices Tree.root items proofs k := by
  rw [DeletionProof_uncps]
  simp [deletion_loop_equivalence']

theorem before_insertion_all_zeroes_batch
  [Fact (CollisionResistant poseidon₂)]
  (Tree: MerkleTree F poseidon₂ D)
  (StartIndex: Nat) (IdComms: Vector F B) (xs_small : is_index_in_range_nat D (StartIndex + B)) (k : F -> Prop) :
  let items := list_of_items_insert Tree StartIndex IdComms xs_small
  let proofs := list_of_proofs_insert Tree StartIndex IdComms xs_small
  SemaphoreMTB.InsertionProof_4_30_4_4_30 StartIndex Tree.root items proofs k →
  (∀ i ∈ [StartIndex:StartIndex + B], MerkleTree.tree_item_at_fin Tree (i:F).val = (0:F)) := by
  simp [InsertionProof_uncps]
  apply before_insertion_all_zeroes_batch'

-- TreeDeleteZero checks that item_at is equal to 0 if the skip flag is false
theorem after_deletion_all_zeroes_batch [Fact (CollisionResistant poseidon₂)] {range : i ∈ [0:B]}
  (Tree: MerkleTree F poseidon₂ D) (DeletionIndices : Vector F B) (xs_small : are_indices_in_range (D+1) DeletionIndices) :
  let items := (list_of_items_delete Tree DeletionIndices xs_small)
  let proofs := (list_of_proofs_delete Tree DeletionIndices xs_small)
  SemaphoreMTB.DeletionProof_4_4_30_4_4_30 DeletionIndices Tree.root items proofs (fun finalRoot => t.root = finalRoot) →
  TreeDeleteZero t (DeletionIndices[i]'(by rcases range; linarith)) (by apply for_all_is_index_in_range (Indices := DeletionIndices) (xs_small := xs_small) (range := by tauto)) := by
  simp [DeletionProof_uncps]
  rw [<-deletion_loop_equivalence']
  simp [MerkleTree.eq_root_eq_tree]
  rcases range with ⟨_, hi⟩
  apply after_deletion_all_zeroes (range := ⟨zero_le _, hi⟩)

def main : IO Unit := pure ()
