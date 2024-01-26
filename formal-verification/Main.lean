import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Ext.Vector

import FormalVerification
import FormalVerification.Utils
import FormalVerification.Poseidon
import FormalVerification.InputHashing
import FormalVerification.BinaryReps.Basic
import FormalVerification.BinaryReps.SemanticEquivalence


import FormalVerification.SemanticEquivalence

open SemaphoreMTB (F Order)

namespace Deletion

/-!
### Input Hash Correctness

Both Semaphore MTB circuits use a construction where the inputs that are
logically used as public inputs, are instead concatenated and hashed to a single
field element. This hash is the only real public input to the circuit. This is
done to significantly reduce the cost of proof verification.

This section establishes the correctness of that construction.
-/
section InputHash

/--
Establishes that the deletion circuit's InputHash parameter is uniquely
determined by DeletionIndices, PreRoot and PostRoot. That is done by showing
that any two valid assigments that agree on those parameters, must also agree
on InputHash.
-/
theorem DeletionCircuit_InputHash_deterministic:
  (SemaphoreMTB.DeletionMbuCircuit_4_4_30_4_4_30 InputHash₁ DeletionIndices PreRoot PostRoot IdComms₁ MerkleProofs₁ ∧
   SemaphoreMTB.DeletionMbuCircuit_4_4_30_4_4_30 InputHash₂ DeletionIndices PreRoot PostRoot IdComms₂ MerkleProofs₂)
  → InputHash₁ = InputHash₂
  := Deletion_InputHash_deterministic


end InputHash

section InputValidations

theorem indices_rangecheck:
  SemaphoreMTB.DeletionMbuCircuit_4_4_30_4_4_30 InputHash DeletionIndices PreRoot PostRoot IdComms MerkleProofs →
  ∀ v ∈ DeletionIndices, v.val < 2^32 := by
  intro hp v hv
  have hp := Deletion_skipHashing hp
  sorry

end InputValidations


end Deletion

namespace Insertion

theorem before_insertion_all_items_zero
  [Fact (CollisionResistant poseidon₂)]
  {tree: MerkleTree F poseidon₂ D}
  {startIndex : F}:
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash startIndex tree.root PostRoot IdComms MerkleProofs →
  ∀ i ∈ [startIndex.val:startIndex.val + B], tree[i]! = 0 := by
  intro hp i hir
  have hp := Insertion_skipHashing hp
  rw [insertionRoundsCircuit_eq_insertionRoundsSemantics] at hp
  have hp'' := ix_bound hp
  rw [getElem!_eq_getElem?_get!]
  rw [before_insertion_all_zero hp]; rfl
  apply And.intro
  . exact hir.1
  . apply Nat.lt_of_lt_of_eq hir.2
    rw [ZMod.val_add, Nat.mod_eq_of_lt]
    rfl
    calc
      startIndex.val + 4 = (startIndex.val + 3) + 1 := by ring
      _ < 2^D + 1 := Nat.add_lt_add_right hp'' (k := 1)
      _ < Order := by decide

theorem root_transformation_correct
  [Fact (CollisionResistant poseidon₂)]
  {Tree : MerkleTree F poseidon₂ D}:
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash StartIndex Tree.root PostRoot IdComms MerkleProofs →
  ∃(postTree : MerkleTree F poseidon₂ D),
  postTree.root = PostRoot ∧
  (∀ i, i ∈ [StartIndex.val:StartIndex.val + B] → postTree[i]! = IdComms[i-StartIndex.val]!) ∧
  (∀ i, i ∉ [StartIndex.val:StartIndex.val + B] → postTree[i]! = Tree[i]!) := by
  intro hp
  have hp := Insertion_skipHashing hp
  rw [insertionRoundsCircuit_eq_insertionRoundsSemantics] at hp
  have hp := insertionRoundsRootTransformation hp
  rcases hp with ⟨postTree, treeTrans, rootTrans⟩
  exists postTree
  simp_rw [getElem!_eq_getElem?_get!]
  refine ⟨rootTrans, ?inrange, ?outrange⟩
  case inrange =>
    intro i hi
    have : i = StartIndex.val + (i - StartIndex.val) := by
      rw [add_comm, Nat.sub_add_cancel hi.1]
    have i_off_inrange : i - StartIndex.val ∈ [0:B] := by
      refine ⟨Nat.zero_le _, ?_⟩
      cases hi
      linarith
    rw [this, treeTransform_get_inrange treeTrans i_off_inrange, ←this]
    apply congrArg
    apply eq_comm.mp
    apply getElem?_eq_some_getElem_of_valid_index
  case outrange =>
    intro i hi
    cases Nat.lt_or_ge i StartIndex.val with
    | inl h =>
      apply congrArg
      apply eq_comm.mp
      apply treeTransform_get_lt treeTrans h
    | inr h =>
      cases Nat.lt_or_ge i (StartIndex.val + B) with
      | inl h' =>
        exfalso
        exact hi ⟨h, h'⟩
      | inr h =>
        apply congrArg
        apply eq_comm.mp
        apply treeTransform_get_gt treeTrans h

/--
Establishes that the insertion circuit's InputHash parameter is uniquely
determined by StartIndex, PreRoot, PostRoot and the identity commitments. That
is done by showing that any two valid assigments that agree on those
parameters, must also agree on InputHash.
-/
theorem InsertionCircuit_InputHash_deterministic:
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash₁ StartIndex PreRoot PostRoot IdComms MerkleProofs₁ ∧
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash₂ StartIndex PreRoot PostRoot IdComms MerkleProofs₂ →
  InputHash₁ = InputHash₂
  := Insertion_InputHash_deterministic

theorem reducedKeccak1568_zeros :
  reducedKeccak1568 (SubVector.lift (Vector.replicate 1568 bZero)) = 0x2872693cd1edb903471cf4a03c1e436f32dccf7ffa2218a4e0354c2514004511 := by
  native_decide

theorem reducedKeccak1568_ones :
  reducedKeccak1568 (SubVector.lift (Vector.replicate 1568 bOne)) = 0x1d7add23b253ac47705200179f6ea5df39ba965ccda0a213c2afc112bc842a5 := by
  native_decide

axiom reducedKeccak1568_collision_resistant :
  ∀x y, reducedKeccak1568 x = reducedKeccak1568 y → x = y

theorem InsertionCircuit_InputHash_injective:
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash StartIndex₁ PreRoot₁ PostRoot₁ IdComms₁ MerkleProofs₁ ∧
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash StartIndex₂ PreRoot₂ PostRoot₂ IdComms₂ MerkleProofs₂ →
  StartIndex₁ = StartIndex₂ ∧ PreRoot₁ = PreRoot₂ ∧ PostRoot₁ = PostRoot₂ ∧ IdComms₁ = IdComms₂ :=
  Insertion_InputHash_injective (fun hp => reducedKeccak1568_collision_resistant _ _ hp)

end Insertion

-- def treeInsertionSpec {d b} (tree : MerkleTree F poseidon₂ d)

-- /-

-- theorem insertion_is_set_circuit
--   [Fact (CollisionResistant poseidon₂)]
--   (Tree: MerkleTree F poseidon₂ D)
--   (StartIndex: Nat) (IdComms: Vector F B) (xs_small : is_index_in_range_nat D (StartIndex + B)) (hzero : InsertionLoopZero Tree StartIndex IdComms xs_small) (k : F -> Prop) :
--   TreeInsertCircuit Tree StartIndex IdComms xs_small (fun newTree => k newTree.root) ↔
--   (let items := list_of_items_insert Tree StartIndex IdComms xs_small
--   let proofs := list_of_proofs_insert Tree StartIndex IdComms xs_small
--   SemaphoreMTB.InsertionProof_4_30_4_4_30 StartIndex Tree.root items proofs k) := by
--   simp
--   rw [InsertionProof_uncps]
--   rw [insertion_loop_equivalence']
--   simp [hzero]

-- theorem deletion_is_set_circuit [Fact (CollisionResistant poseidon₂)]
--   (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F B) (xs_small : are_indices_in_range (D+1) DeletionIndices) (k : F -> Prop) :
--   TreeDeleteCircuit Tree DeletionIndices xs_small (fun newTree => k newTree.root) ↔
--   let items := (list_of_items_delete Tree DeletionIndices xs_small)
--   let proofs := (list_of_proofs_delete Tree DeletionIndices xs_small)
--   SemaphoreMTB.DeletionProof_4_4_30_4_4_30 DeletionIndices Tree.root items proofs k := by
--   rw [DeletionProof_uncps]
--   simp [deletion_loop_equivalence']

-- theorem before_insertion_all_zeroes_batch
--   [Fact (CollisionResistant poseidon₂)]
--   (Tree: MerkleTree F poseidon₂ D)
--   (StartIndex: Nat) (IdComms: Vector F B) (xs_small : is_index_in_range_nat D (StartIndex + B)) (k : F -> Prop) :
--   let items := list_of_items_insert Tree StartIndex IdComms xs_small
--   let proofs := list_of_proofs_insert Tree StartIndex IdComms xs_small
--   SemaphoreMTB.InsertionProof_4_30_4_4_30 StartIndex Tree.root items proofs k →
--   (∀ i ∈ [StartIndex:StartIndex + B], MerkleTree.tree_item_at_fin Tree (i:F).val = (0:F)) := by
--   simp [InsertionProof_uncps]
--   apply before_insertion_all_zeroes_batch'

-- -- TreeDeleteZero checks that item_at is equal to 0 if the skip flag is false
-- theorem after_deletion_all_zeroes_batch [Fact (CollisionResistant poseidon₂)] {range : i ∈ [0:B]}
--   (Tree: MerkleTree F poseidon₂ D) (DeletionIndices : Vector F B) (xs_small : are_indices_in_range (D+1) DeletionIndices) :
--   let items := (list_of_items_delete Tree DeletionIndices xs_small)
--   let proofs := (list_of_proofs_delete Tree DeletionIndices xs_small)
--   SemaphoreMTB.DeletionProof_4_4_30_4_4_30 DeletionIndices Tree.root items proofs (fun finalRoot => t.root = finalRoot) →
--   TreeDeleteZero t (DeletionIndices[i]'(by rcases range; linarith)) (by apply for_all_is_index_in_range (Indices := DeletionIndices) (xs_small := xs_small) (range := by tauto)) := by
--   simp [DeletionProof_uncps]
--   rw [<-deletion_loop_equivalence']
--   simp [MerkleTree.eq_root_eq_tree]
--   rcases range with ⟨_, hi⟩
--   apply after_deletion_all_zeroes (range := ⟨zero_le _, hi⟩)

-- def main : IO Unit := pure ()

-- -/
