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

-- def list_to_vec_n (L : List Dir) (n : Nat) : Vector Dir n := ⟨List.takeI n L, List.takeI_length n L⟩

-- def mod_two (inp : Nat) : Dir := match (inp%2) with
--  | 0 => Dir.left
--  | 1 => Dir.right
--  | _ => panic "Unreachable" -- Unreachable

-- def recover_binary_list : Nat → List Dir
--   | 0 => [Dir.left]
--   | 1 => [Dir.right]
--   | x+2 => have : Nat.succ (x / 2) < Nat.succ (Nat.succ x) := by sorry
--   (recover_binary_list ((x+2)/2)) ++ [mod_two x]
-- termination_by recover_binary_list x => x

-- def nat_to_dir_vec (idx : Nat) (depth : Nat ): Vector Dir depth :=
--   list_to_vec_n (List.reverse (recover_binary_list idx)) depth

-- def item_at_nat {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (idx : Nat) : F := 
--   let p := nat_to_dir_vec idx depth
--   t.item_at p

-- IdComms not needed because proving that all items are 0 after deletion
def item_is_zero_or_skip {n} (Tree: MerkleTree F poseidon₂ D) (DeletionIndices: Vector F n) (PostRoot: F) (MerkleProofs: Vector (Vector F D) n) : Prop :=
  match n with
  | Nat.zero => True
  | Nat.succ _ =>
    ∃out: Vector F (D+1), recover_binary_zmod' out = DeletionIndices.head ∧ is_vector_binary out ∧
    match zmod_to_bit out.last with
      | Bit.zero => Tree.item_at (Dir.create_dir_vec out).front = 0 ∧ item_is_zero_or_skip Tree DeletionIndices.tail PostRoot MerkleProofs.tail -- Update the root
      | Bit.one => item_is_zero_or_skip Tree DeletionIndices.tail PostRoot MerkleProofs.tail  -- Skip flag set, don't update the root

-- IdComms not needed because proving that all items are 0 before insertion
theorem after_deletion_all_items_zero (Tree: MerkleTree F poseidon₂ D) (DeletionIndices: Vector F B) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (k: F -> Prop) :
  gDeletionProof DeletionIndices Tree.root IdComms MerkleProofs fun PostRoot => Tree.root = PostRoot ∧ item_is_zero_or_skip Tree DeletionIndices PostRoot MerkleProofs := by
    simp [DeletionProof_uncps]
    unfold DeletionLoop
    unfold item_is_zero_or_skip
    --apply Exists.intro
    
    sorry

def InsertionLoopTree {n} (Tree: MerkleTree F poseidon₂ D) (StartIndex: F) (PreRoot: F) (IdComms: Vector F n) (MerkleProofs: Vector (Vector F D) n) : Prop :=
  match n with
  | Nat.zero => PreRoot = Tree.root
  | Nat.succ _ =>
    ∃out: Vector F D, recover_binary_zmod' out = StartIndex ∧ is_vector_binary out ∧
    MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) MerkleProofs.head 0 = Tree.root ∧
    InsertionLoopTree Tree (StartIndex + 1) (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) MerkleProofs.head IdComms.head) IdComms.tail MerkleProofs.tail

def item_is_zero {n} (Tree: MerkleTree F poseidon₂ D) (StartIndex: F) (PreRoot: F) (MerkleProofs: Vector (Vector F D) n) : Prop :=
  match n with
  | Nat.zero => True
  | Nat.succ _ =>
    ∃out: Vector F D, recover_binary_zmod' out = StartIndex ∧ is_vector_binary out ∧
    Tree.item_at (Dir.create_dir_vec out).reverse = 0 ∧ item_is_zero Tree (StartIndex + 1) PreRoot MerkleProofs.tail

theorem recover_tail_reverse_equals_recover'
  {F depth}
  (H : Hash F 2)
  (ix : Vector Dir depth)
  (proof : Vector F depth)
  (item : F) :
  MerkleTree.recover_tail H ix proof item = MerkleTree.recover H ix.reverse proof.reverse item := by
  rw [←Vector.ofFn_get (v := ix)]
  rw [←Vector.ofFn_get (v := proof)]
  rw [<-MerkleTree.recover_tail_reverse_equals_recover H _ _ item]
  simp

def TreeInsert [Fact (perfect_hash poseidon₂)] (Tree : MerkleTree F poseidon₂ D) (Index: F) (Item: F) (Proof: Vector F D) (k: F -> Prop) : Prop :=
  ∃out: Vector F D, recover_binary_zmod' out = Index ∧ is_vector_binary out ∧
  MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) Proof 0 = Tree.root ∧
  k (Tree.set (Dir.create_dir_vec out).reverse Item).root

theorem InsertIsSet [Fact (perfect_hash poseidon₂)] {Tree : MerkleTree F poseidon₂ D} {Index: F} {Item: F} {Proof: Vector F D} {k: F -> Prop} :
  insertion_round Index Item Tree.root Proof k ↔
  TreeInsert Tree Index Item Proof k := by
    simp [insertion_round]
    simp [TreeInsert]
    apply exists_congr
    intro out
    simp
    intros
    have : MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) Proof Item = (Tree.set (Dir.create_dir_vec out).reverse Item).root := by
      simp [recover_tail_reverse_equals_recover'] at *
      rw [MerkleTree.proof_insert_invariant (Dir.create_dir_vec out).reverse Tree 0 Item Proof.reverse]
      assumption
    simp [<-MerkleTree.recover_tail_reverse_equals_recover] at this
    simp [this]

-- theorem nat_to_dir_vec_is_recovery {idx : Nat} {depth : Nat} {out : Vector F depth} { h : recover_binary_zmod' out = idx ∧ is_vector_binary out }:
--   (nat_to_dir_vec idx depth) = (Dir.create_dir_vec out).reverse := by
--   cases h
--   rename_i h₁ h₂
--   sorry

theorem before_insertion_all_items_zero
  [Fact (perfect_hash poseidon₂)]
  {Tree: MerkleTree F poseidon₂ D}
  (StartIndex: Nat) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (k: F -> Prop) :
  gInsertionProof ↑StartIndex Tree.root IdComms MerkleProofs k →
  -- (∀ i ∈ [StartIndex:StartIndex + B], item_at_nat Tree i = 0) := by
  (∀ i ∈ [StartIndex:StartIndex + B], ∃out: Vector F D, recover_binary_zmod' out = i ∧ is_vector_binary out ∧ 
  (Tree.item_at (Dir.create_dir_vec out).reverse) = 0) := by
    simp [gInsertionProof]
    simp [InsertionRound_uncps]

    -- First version!
    -- repeat (
      -- simp only [InsertIsSet]
      -- unfold TreeInsert
    -- )
    -- simp
    -- simp [item_at_nat]
    -- simp [recover_tail_reverse_equals_recover']
    -- intros
    -- rename_i _ _ h₃ _ _ _ _ _ i hi
    -- simp [Gates.add] at *
    -- rw [MerkleTree.proof_ceritfies_item _ _ MerkleProofs[0].reverse _]
    -- rw [nat_to_dir_vec_is_recovery]
    -- apply h₃
    -- rename_i h₈
    -- simp [Std.instMembershipNatRange] at hi

    -- Second version!
    simp only [InsertIsSet]
    unfold TreeInsert
    simp
    simp [recover_tail_reverse_equals_recover']
    intros
    apply Exists.intro
    apply And.intro
    rename_i i hi
    sorry
    apply And.intro
    assumption
    rw [MerkleTree.proof_ceritfies_item _ _ MerkleProofs[0].reverse _]
    assumption

def main : IO Unit := pure ()