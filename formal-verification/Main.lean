import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Ext.Vector

import FormalVerification
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness
import FormalVerification.Keccak.SemanticEquivalence

import FormalVerification.SemanticEquivalence

open SemaphoreMTB (F Order)

variable [Fact (Nat.Prime Order)]

open SemaphoreMTB renaming VerifyProof_31_30 → gVerifyProof
open SemaphoreMTB renaming DeletionRound_30_30 → gDeletionRound
open SemaphoreMTB renaming DeletionProof_4_4_30_4_4_30 → gDeletionProof
open SemaphoreMTB renaming InsertionRound_30_30 → gInsertionRound
open SemaphoreMTB renaming InsertionProof_4_30_4_4_30 → gInsertionProof

def TreeInsert [Fact (perfect_hash poseidon₂)] (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (Proof : Vector F D) (k : F → Prop): Prop :=
  MerkleTree.item_at_nat Tree Index.val = some 0 ∧
  MerkleTree.proof_at_nat Tree Index.val = some Proof.reverse ∧
  ∃postTree, MerkleTree.set_at_nat Tree Index.val Item = some postTree ∧
  k postTree.root

theorem insertion_round_uncps [Fact (perfect_hash poseidon₂)] (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (Proof : Vector F D) (k : F → Prop):
  insertion_round Index Item Tree.root Proof k ↔
  TreeInsert Tree Index Item Proof k := by
  unfold insertion_round
  unfold TreeInsert
  apply Iff.intro
  . rintro ⟨ixbin, _⟩
    casesm* (_ ∧ _)
    have : nat_to_bits_le D Index.val = some (vector_zmod_to_bit ixbin) := by
      apply recover_binary_zmod'_to_bits_le
      . simp
      . assumption
      . rename_i h _ _ _; simp[h]
    unfold MerkleTree.item_at_nat
    unfold MerkleTree.proof_at_nat
    unfold MerkleTree.set_at_nat
    unfold Dir.nat_to_dir_vec
    rw [this]
    simp [←Dir.create_dir_vec_bit]
    rename_i h₀ h₁ h₂ h₃
    refine ⟨?_, ⟨?_, ?_⟩⟩
    . apply MerkleTree.proof_ceritfies_item (proof := Proof.reverse)
      rw [←MerkleTree.recover_tail_reverse_equals_recover]
      simp [h₂]
    . apply MerkleTree.recover_proof_reversible
      rw [←MerkleTree.recover_tail_reverse_equals_recover (item := (0:F))]
      simp [h₂]
    . rw [←MerkleTree.proof_insert_invariant (proof := Proof.reverse) (old := 0)]
      . rw [←MerkleTree.recover_tail_reverse_equals_recover]
        simp [h₃]
      . rw [←MerkleTree.recover_tail_reverse_equals_recover]
        simp [h₂]
  . rintro ⟨hitem, ⟨hproof, ⟨ftree, ⟨hftree, hresult⟩⟩⟩⟩
    simp [MerkleTree.item_at_nat, Dir.nat_to_dir_vec] at hitem
    rcases hitem with ⟨bits, ⟨hbits, hitem_at⟩⟩
    simp [MerkleTree.proof_at_nat, Dir.nat_to_dir_vec] at hproof
    rcases hproof with ⟨bits', ⟨hbits', hproof_at⟩⟩
    simp [hbits] at hbits'
    simp [hbits'] at *
    simp [MerkleTree.set_at_nat, Dir.nat_to_dir_vec] at hftree
    rcases hftree with ⟨bits'', ⟨hbits'', hftree_at⟩⟩
    simp [hbits''] at hbits
    rw [←Vector.vector_reverse_eq] at hproof_at
    simp [hbits] at *
    simp [<-hproof_at]
    let t : Vector F D := (Vector.map Bit.toZMod bits')
    refine ⟨t, ?_⟩
    refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
    . apply recover_binary_of_to_bits
      simp [hbits'']
    . apply vector_binary_of_bit_to_zmod
    . rw [MerkleTree.recover_tail_equals_recover_reverse, Dir.create_dir_vec_bit, zmod_to_bit_coe, ←hitem_at]
      simp [MerkleTree.recover_proof_is_root]
    . rw [<-hftree_at] at hresult
      rw [MerkleTree.recover_tail_equals_recover_reverse, Dir.create_dir_vec_bit, zmod_to_bit_coe]
      rw [MerkleTree.proof_insert_invariant _]
      . apply hresult
      . exact 0
      . rw [← hitem_at]
        simp [MerkleTree.recover_proof_is_root]

theorem before_insertion_all_items_zero_loop
  [Fact (perfect_hash poseidon₂)]
  {Tree: MerkleTree F poseidon₂ D}
  {StartIndex B: Nat}
  {ixBound: StartIndex + B < Order}
  {IdComms: Vector F B} {MerkleProofs: Vector (Vector F D) B} {k: F -> Prop}:
  insertion_rounds ↑StartIndex Tree.root IdComms MerkleProofs k →
  (∀ i ∈ [StartIndex:StartIndex + B], MerkleTree.item_at_nat Tree i = some 0) := by
  induction B generalizing StartIndex Tree with
  | zero =>
    intro _ i range
    rcases range with ⟨lo, hi⟩
    have := Nat.ne_of_lt (Nat.lt_of_le_of_lt lo hi)
    contradiction
  | succ B ih =>
    intro hp i range
    rcases range with ⟨lo, hi⟩; simp at lo hi
    have hStartIndexCast : ZMod.val (StartIndex : F) = StartIndex := by
      apply ZMod.val_cast_of_lt
      linarith
    cases lo with
    | refl =>
      simp [insertion_rounds,  InsertionRound_uncps, insertion_round_uncps, TreeInsert, hStartIndexCast] at hp
      cases hp
      rename_i l r
      simp [l]
    | @step StartIndex' h =>
      have : (StartIndex : F) + 1 = ((StartIndex + 1 : Nat) : F) := by
        simp [Fin.ext]
      rw [insertion_rounds,  InsertionRound_uncps, insertion_round_uncps, TreeInsert, this] at hp
      rcases hp with ⟨_, ⟨_, ⟨postTree, ⟨hinsert, hnext⟩⟩⟩⟩
      rw [←MerkleTree.item_at_nat_invariant hinsert]
      apply ih hnext StartIndex'.succ
      . apply And.intro
        . simp_arith; simp [Nat.le] at h; simp [h]
        . simp; linarith
      . linarith
      . rw [hStartIndexCast]
        apply Nat.ne_of_lt
        simp_arith; simp [Nat.le] at h; simp [h]

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

def main : IO Unit := pure ()
