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
def item_is_zero_or_skip {n} (Tree: MerkleTree F poseidon₂ D) (DeletionIndices: Vector F n) (PostRoot: F) (MerkleProofs: Vector (Vector F D) n) : Prop :=
  match n with
  | Nat.zero => True
  | Nat.succ _ =>
    ∃out: Vector F (D+1), recover_binary_zmod' out = DeletionIndices.head ∧ is_vector_binary out ∧
    match zmod_to_bit out.last with
      | Bit.zero => Tree.item_at (Dir.create_dir_vec out).front = 0 ∧ item_is_zero_or_skip Tree DeletionIndices.tail PostRoot MerkleProofs.tail -- Update the root
      | Bit.one => item_is_zero_or_skip Tree DeletionIndices.tail PostRoot MerkleProofs.tail  -- Skip flag set, don't update the root

-- IdComms not needed because proving that all items are 0 before insertion
theorem after_deletion_all_items_zero (Tree: MerkleTree F poseidon₂ D) (DeletionIndices: Vector F B) (PreRoot: F) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (k: F -> Prop) :
  gDeletionProof DeletionIndices PreRoot IdComms MerkleProofs fun PostRoot => item_is_zero_or_skip Tree DeletionIndices PostRoot MerkleProofs := by
    simp [DeletionProof_uncps]
    unfold DeletionLoop
    unfold item_is_zero_or_skip

    -- conv =>
    --   arg 1;
    --   intro out;
    --   . tactic => cases out; rename_i
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
    ∃out: Vector F (D), recover_binary_zmod' out = StartIndex ∧ is_vector_binary out ∧
    Tree.item_at (Dir.create_dir_vec out).reverse = 0 ∧ item_is_zero Tree (StartIndex + 1) PreRoot MerkleProofs.tail

theorem recover_tail_reverse_equals_recover'
  {F depth}
  (H : Hash F 2)
  (ix : Vector Dir depth)
  (proof : Vector F depth)
  (item : F) :
  MerkleTree.recover_tail H ix proof item = MerkleTree.recover H ix.reverse proof.reverse item := by sorry

-- theorem proof_ceritfies_item'
--   {depth : Nat}
--   {F: Type}
--   {H: Hash F 2}
--   [Fact (perfect_hash H)]
--   (ix : Vector Dir depth)
--   (tree : MerkleTree F H depth)
--   (proof : Vector F depth)
--   (item : F)
--   :
--   MerkleTree.recover H ix.reverse proof.reverse item = tree.root → tree.item_at ix.reverse = item := by sorry

lemma verify_proof_is_root {Tree: MerkleTree F poseidon₂ D} {Path: Vector Dir D} {Proof: Vector F D} {Item: F} :
  (MerkleTree.recover_tail poseidon₂ Path Proof Item) = (MerkleTree.recover_tail poseidon₂ Path (Tree.proof Path) (Tree.item_at Path)) := by sorry


def TreeInsert [Fact (perfect_hash poseidon₂)] (Index: F) (Item: F) (Tree : MerkleTree F poseidon₂ D) (Proof: Vector F D) (k: F -> Prop) : Prop :=
  ∃out: Vector F D, recover_binary_zmod' out = Index ∧ is_vector_binary out ∧
  MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) Proof 0 = Tree.root ∧
  k (Tree.set (Dir.create_dir_vec out) Item).root

theorem InsertIsSet [Fact (perfect_hash poseidon₂)] {Tree : MerkleTree F poseidon₂ D} {Index: F} {Item: F} {Proof: Vector F D} {k: F -> Prop} :
  insertion_round Index Item () Proof k ↔
  TreeInsert Index Item PrevRoot Proof k
  -- := by
  -- simp [InsertionRound_uncps]
  -- conv =>
  --   rhs; arg 1; intro out; rw [<-MerkleTree.recover_proof_is_root poseidon₂ (Dir.create_dir_vec out) _]
  -- apply exists_congr
  -- intro out
  -- simp
  -- intros
  -- have : (MerkleTree.proof (MerkleTree.set Tree (Dir.create_dir_vec out) Item) (Dir.create_dir_vec out)) = Proof := by sorry
  -- simp [this]
  -- have : (MerkleTree.item_at (MerkleTree.set Tree (Dir.create_dir_vec out) Item) (Dir.create_dir_vec out)) = Item := by sorry
  -- simp [this]

  -- rw [MerkleTree.proof_ceritfies_item (Dir.create_dir_vec out) _ Proof 0]
  -- sorry
  -- sorry

theorem before_insertion_all_items_zero
  [Fact (perfect_hash poseidon₂)]
  {Tree: MerkleTree F poseidon₂ D}
  (StartIndex: Nat) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (k: F -> Prop) :
  gInsertionProof ↑StartIndex Tree.root IdComms MerkleProofs k →
  (∀ i ∈ [StartIndex:StartIndex + B], Tree.item_at_nat i = 0) := by
  --item_is_zero Tree StartIndex PreRoot MerkleProofs := by
    simp [gInsertionProof]
    simp [InsertionRound_uncps]
    simp only [InsertIsSet]
    simp [TreeInsert]
    simp [item_is_zero]
    simp [recover_tail_reverse_equals_recover']
    intros
    rename_i h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃
    rw [MerkleTree.proof_ceritfies_item] at h₁₂
    -- apply Exists.intro
    -- apply And.intro
    -- rename_i h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃
    -- unfold Gates.add at h₂
    -- simp at *
    -- assumption
    -- apply And.intro
    -- assumption
    -- apply And.intro
    -- rw [MerkleTree.proof_ceritfies_item] at *
    -- assumption
    -- rename_i h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃
    -- subst_vars
    -- --rw [←Vector.ofFn_get (v := MerkleProofs)] at *
    -- have : h₆ = (Vector.reverse MerkleProofs[0]) ∧ Tree = h₄ := by
    --   apply And.intro

    --   sorry
    -- simp [this]
    -- assumption
    sorry
    -- apply Exists.intro
    -- apply And.intro
    -- unfold Gates.add at *
    -- assumption
    -- apply And.intro
    -- assumption
    -- simp [recover_tail_reverse_equals_recover'] at *
    -- rw [MerkleTree.proof_ceritfies_item] at *
    -- assumption
    -- simp [*] at *

    -- sorry

-- theorem before_insertion_all_items_zero [Fact (perfect_hash poseidon₂)] {Tree: MerkleTree F poseidon₂ D} (StartIndex: F) (PreRoot: F) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (k: F -> Prop) :
--   (Tree.root = PreRoot ∧ gInsertionProof StartIndex PreRoot IdComms MerkleProofs fun postRoot => Tree.root = postRoot)  → item_is_zero Tree StartIndex PreRoot MerkleProofs := by
--   simp [InsertionProof_uncps]
--   simp [InsertionLoop]
--   simp [item_is_zero]
--   simp [recover_tail_reverse_equals_recover']


--   intros
--   subst_vars
--   apply Exists.intro
--   repeat' (apply And.intro)
--   rfl
--   assumption
--   rw [MerkleTree.proof_ceritfies_item]
--   assumption
--   --simp [<-proof_ceritfies_item'] at *
--   -- rename_i h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
--   -- let ix := (Dir.create_dir_vec h₁).reverse
--   -- let t := Tree
--   -- let p := (Vector.head MerkleProofs).reverse
--   -- let item := (0:F)
--   -- rw [MerkleTree.proof_ceritfies_item ix t p (0:F)]
--   -- simp
--   -- rw [<-MerkleTree.recover_tail_reverse_equals_recover poseidon₂ ix p (0:F)]
--   -- simp
--   -- simp [h₈]
--   -- --rename_i h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
--   -- apply Exists.intro
--   -- repeat' (apply And.intro)
--   -- --assumption
--   -- rename_i h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
--   -- --assumption
--   -- --let ix := (Dir.create_dir_vec h₃).reverse
--   -- --let t := Tree
--   -- --let p := (Vector.head (Vector.tail MerkleProofs)).reverse
--   -- --let item := (0:F)
--   -- --rw [MerkleTree.proof_ceritfies_item ix t p (0:F)]
--   -- --simp
--   -- --simp
--   -- --rw [<-MerkleTree.recover_tail_reverse_equals_recover poseidon₂ ix p (0:F)]
--   -- -- simp
--   -- -- have: Tree.root = MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec h₁) (Vector.head MerkleProofs) (Vector.head IdComms) := by
--   -- --   simp [*]
--   -- --   sorry
--   -- -- simp [this]
--   -- -- assumption
--   -- assumption
--   -- assumption
--   -- simp [recover_tail_reverse_equals_recover'] at *
--   -- rw [MerkleTree.proof_ceritfies_item]
--   -- assumption
--   -- rename_i h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈


--   --rw [MerkleTree.proof_ceritfies_item _ _ _ _]
--   --rw [<-MerkleTree.recover_tail_reverse_equals_recover _ _ _ _]
--   sorry
--   sorry

def main : IO Unit := pure ()