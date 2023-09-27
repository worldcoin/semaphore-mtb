import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle

import FormalVerification
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness
import FormalVerification.SemanticEquivalence

open SemaphoreMTB (F Order)

variable [Fact (Nat.Prime Order)]

open SemaphoreMTB renaming VerifyProof_4_3 → gVerifyProof
open SemaphoreMTB renaming DeletionRound_3_3 → gDeletionRound
open SemaphoreMTB renaming DeletionProof_2_2_3_2_2_3 → gDeletionProof
open SemaphoreMTB renaming InsertionRound_3_3 → gInsertionRound
open SemaphoreMTB renaming InsertionProof_2_3_2_2_3 → gInsertionProof

-- theorem before_deletion_tree_matches_root (DeletionIndices: Vector F B) (PreRoot: F) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (k: F -> Prop) :
--   gDeletionProof DeletionIndices PreRoot IdComms MerkleProofs k →
--   ∃out, recover_binary_zmod' out = DeletionIndices.head ∧ is_vector_binary out ∧
--   MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) MerkleProofs.head IdComms.head = PreRoot := by
--   simp [DeletionProof_looped, deletion_rounds_uncps, DeletionLoop]
--   intros
--   apply Exists.intro
--   tauto

-- theorem after_deletion_items_are_zero (DeletionIndices: Vector F B) (PreRoot: F) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) :
--   gDeletionProof DeletionIndices PreRoot IdComms MerkleProofs fun post_root => ∃x, recover_binary_zmod' x = DeletionIndices.last ∧ is_vector_binary x ∧
--   MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec x) MerkleProofs.last 0 = post_root := by
--   -- simp [DeletionProof_2_2_3_2_uncps]
--   -- simp [DeletionLoop]
  
--   -- simp [SemaphoreMTB.DeletionProof_2_2_3_2]
--   -- simp [DeletionRound_uncps]

--   sorry

-- IdComms not needed because proving that all items are 0 after deletion
def item_is_zero_or_skip {n} (DeletionIndices: Vector F n) (PostRoot: F) (MerkleProofs: Vector (Vector F D) n) : Prop :=
  match n with
  | Nat.zero => True
  | Nat.succ _ =>
    ∃out: Vector F (D+1), recover_binary_zmod' out = DeletionIndices.head ∧ is_vector_binary out ∧
    match zmod_to_bit out.last with
      | Bit.zero => MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out).front MerkleProofs.head 0 = PostRoot ∧ item_is_zero_or_skip DeletionIndices.tail PostRoot MerkleProofs.tail -- Update the root
      | Bit.one => item_is_zero_or_skip DeletionIndices.tail PostRoot MerkleProofs.tail  -- Skip flag set, don't update the root

-- IdComms not needed because proving that all items are 0 before insertion
def item_is_zero {n} (StartIndex: F) (PreRoot: F) (MerkleProofs: Vector (Vector F D) n) : Prop :=
  match n with
  | Nat.zero => True
  | Nat.succ _ =>
    ∃out: Vector F (D), recover_binary_zmod' out = StartIndex ∧ is_vector_binary out ∧
    MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) MerkleProofs.head 0 = PreRoot ∧ item_is_zero (StartIndex + 1) PreRoot MerkleProofs.tail

theorem after_deletion_all_items_zero (DeletionIndices: Vector F B) (PreRoot: F) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (k: F -> Prop) :
  gDeletionProof DeletionIndices PreRoot IdComms MerkleProofs fun PostRoot => item_is_zero_or_skip DeletionIndices PostRoot MerkleProofs := by
    simp [DeletionProof_uncps]
    sorry

theorem before_insertion_all_items_zero (StartIndex: F) (PreRoot: F) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (k: F -> Prop) :
  gInsertionProof StartIndex PreRoot IdComms MerkleProofs k → item_is_zero StartIndex PreRoot MerkleProofs := by
  sorry

def main : IO Unit := pure ()