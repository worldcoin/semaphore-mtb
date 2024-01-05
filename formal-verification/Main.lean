import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Ext.Vector

import FormalVerification
import FormalVerification.Utils
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness
import FormalVerification.Keccak.SemanticEquivalence
import FormalVerification.KeccakUniqueness
import FormalVerification.BinaryReps.Basic
import FormalVerification.BinaryReps.SemanticEquivalence


import FormalVerification.SemanticEquivalence

import FormalVerification.InsertionCircuit
import FormalVerification.DeletionCircuit

open SemaphoreMTB (F Order)

instance : Membership α (Vector α n) := ⟨fun x xs => x ∈ xs.toList⟩

namespace MerkleTree

instance : GetElem (MerkleTree α H d) Nat α (fun _ i => i < 2^d) where
  getElem tree ix inb := tree.tree_item_at_fin ⟨ix, inb⟩

lemma getElem?_eq_item_at_nat {d} (tree : MerkleTree α H d) (ix : Nat) :
  tree[ix]? = tree.item_at_nat ix := by
  simp only [getElem?, getElem]
  split
  . rename_i h
    rw [eq_comm, MerkleTree.item_at_nat_to_fin_some']
  . rename_i h
    exact eq_comm.mp (MerkleTree.item_at_nat_none_when_ge (Nat.ge_of_not_lt h))

lemma getElem!_eq_item_at_nat [Inhabited α] {d} {tree : MerkleTree α H d} {ix : ℕ}:
  tree[ix]! = (tree.item_at_nat ix).get! := by
  simp only [getElem!, getElem]
  split
  . rename_i h
    rw [eq_comm, MerkleTree.item_at_nat_to_fin' (h:=h)]
    rfl
  . rename_i h
    rw [MerkleTree.item_at_nat_none_when_ge (Nat.ge_of_not_lt h)]
    conv => lhs; whnf

end MerkleTree

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

section InputValidations

theorem before_insertion_all_items_zero
  [Fact (CollisionResistant poseidon₂)]
  {tree: MerkleTree F poseidon₂ D}
  {startIndex : F}:
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash startIndex tree.root PostRoot IdComms MerkleProofs →
  ∀ i ∈ [startIndex.val:startIndex.val + B], tree[i]! = 0 := by
  intro hp i hir
  have hp := Insertion_skipHashing hp
  rw [insertionRounds_rw] at hp
  have hp'' := ix_bound hp
  rw [MerkleTree.getElem!_eq_item_at_nat]
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

end InputValidations


section Semantics

theorem root_transformation_correct
  [Fact (CollisionResistant poseidon₂)]
  {StartIndex : ℕ}
  {Tree : MerkleTree F poseidon₂ D}:
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash StartIndex Tree.root PostRoot IdComms MerkleProofs →
  ∃(postTree : MerkleTree F poseidon₂ D),
  postTree.root = PostRoot ∧
  (∀ i, i ∈ [StartIndex:StartIndex + B] → postTree[i]! = IdComms[i-StartIndex]!) ∧
  (∀ i, i ∉ [StartIndex:StartIndex + B] → postTree[i]! = Tree[i]!) := by
  intro hp
  have hp := Insertion_skipHashing hp
  rw [insertionRounds_rw] at hp
  have hp := insertionRoundsRootTransformation (by sorry) hp



def rootTransformationSpec
  (tree : MerkleTree F poseidon₂ D)
  (identities : Vector F B)
  (startIndex : Nat)
  (indexIsValid : startIndex + B < 2 ^ D): MerkleTree F poseidon₂ D := Id.run do
  let mut tree := tree
  for h : i in [0 : B] do
    have i_valid : startIndex + i < 2 ^ D :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left h.2 _) (le_of_lt indexIsValid)
    tree := tree.tree_set_at_fin ⟨startIndex + i, i_valid⟩ (identities[i]'h.2)
  tree

theorem rootTransformationSpec_correct
  [Fact (CollisionResistant poseidon₂)]
  {Tree : MerkleTree F poseidon₂ D}
  (index_valid : StartIndex + B < 2 ^ D):
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash StartIndex Tree.root PostRoot IdComms MerkleProofs →
  PostRoot = (rootTransformationSpec Tree IdComms StartIndex index_valid).root := by
  intro hp
  have hp := Insertion_skipHashing hp
  rw [insertionRounds_rw, InsertionLoop, insertion_round_prep] at hp
  rcases hp with ⟨_, _, _, hp⟩






end Semantics


end Insertion

-- def treeInsertionSpec {d b} (tree : MerkleTree F poseidon₂ d)

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
