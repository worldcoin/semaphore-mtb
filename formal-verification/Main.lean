import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle

import FormalVerification
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness
import FormalVerification.SemanticEquivalence

open SemaphoreMTB (F Order)

variable [Fact (Nat.Prime Order)]

theorem before_deletion_tree_matches_root (DeletionIndices: Vector F 2) (PreRoot: F) (IdComms: Vector F 2) (MerkleProofs: Vector (Vector F 3) 2) (k: F -> Prop) :
  SemaphoreMTB.DeletionProof_2_2_3_2 DeletionIndices PreRoot IdComms MerkleProofs k →
  ∃out, recover_binary_zmod' out = DeletionIndices.head ∧ is_vector_binary out ∧
  MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) MerkleProofs.head IdComms.head = PreRoot := by
  simp [DeletionProof_looped, deletion_rounds_uncps, DeletionLoop]
  intros
  apply Exists.intro
  tauto

def main : IO Unit := pure ()