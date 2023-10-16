import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Ext.Vector

import FormalVerification
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness
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

def TreeDelete [Fact (perfect_hash poseidon₂)] (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (Proof : Vector F D) (k : F → Prop): Prop :=
  match nat_to_bit (Nat.land Index.val 1) with
  | Bit.zero => MerkleTree.item_at_nat Tree (Nat.shiftr Index.val 1) = some Item ∧
      MerkleTree.proof_at_nat Tree (Nat.shiftr Index.val 1) = some Proof.reverse ∧
      ∃postTree, MerkleTree.set_at_nat Tree (Nat.shiftr Index.val 1) 0 = some postTree ∧
      k postTree.root
  | Bit.one => k Tree.root

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

-- theorem after_deletion_all_items_zero
--   [Fact (perfect_hash poseidon₂)]
--   {Tree: MerkleTree F poseidon₂ D}
--   (DeletionIndices: Vector F B) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (k: F -> Prop) :
--   gDeletionProof DeletionIndices Tree.root IdComms MerkleProofs fun nextRoot =>
--   Tree.root = nextRoot ∧
--   (∀ i ∈ [0:B], DeletionIndices[i]!.val < Order ∧ MerkleTree.item_at_nat Tree DeletionIndices[i]!.val = some 0) := by
--   rw [DeletionProof_looped]
--   rw [deletion_rounds_uncps]
--   sorry

-- Dir.nat_to_dir_vec idx depth
  -- | Dir.left => 0
  -- | Dir.right => 1
-- def a : Nat := 1
-- #eval some (Dir.nat_to_dir (Nat.land a 1)) -- Get Skip flag
-- #eval Vector.last <$> (Dir.nat_to_dir_vec a 3)
-- #eval Vector.dropLast <$> (Dir.nat_to_dir_vec a 3)
-- #eval (Dir.nat_to_dir_vec (Nat.shiftr a 1) 2) -- Get Index

-- Nat.shiftr (ZMod.val (recover_binary_zmod (vector_zmod_to_bit w))) 1
theorem binary_zmod_same_as_nat_drop_last {n d} (rep : Vector Bit d):
  2 ^ d < n ->
  Nat.shiftr (recover_binary_zmod rep : ZMod n).val 1 = recover_binary_nat rep.dropLast := by
  intro d_small
  rw [binary_nat_zmod_equiv_mod_p]
  sorry
  -- apply Nat.mod_eq_of_lt
  -- apply @lt_trans _ _ _ (2^d)
  -- . apply binary_nat_lt
  -- . assumption

theorem recover_binary_zmod'_to_bits_le_drop_last {n : Nat} [Fact (n > 1)] {v : ZMod n} {w : Vector (ZMod n) (d)}:
  2 ^ d < n →
  is_vector_binary w →
  recover_binary_zmod' w = v →
  nat_to_bits_le (d-1) (Nat.shiftr v.val 1) = some (vector_zmod_to_bit w).dropLast := by
  intros
  rw [←recover_binary_nat_to_bits_le]
  subst_vars
  rw [recover_binary_zmod_bit]
  . apply Eq.symm
    apply binary_zmod_same_as_nat_drop_last
    assumption
  . assumption

theorem vectorToListIff {x₁ : α} {xs : Vector α d} : (x₁ ::ᵥ xs) ↔ (x₁ :: xs.toList) := by
  sorry

theorem dropLast_toList {d : Nat} {x₁ x₂ : α} {xs : Vector α d} :
  (x₁ ::ᵥ x₂ ::ᵥ xs).dropLast = (x₁ ::ᵥ (x₂ ::ᵥ xs).dropLast) ↔
  (x₁ ::ᵥ x₂ ::ᵥ xs).dropLast.toList = x₁ :: (x₂ ::ᵥ xs).dropLast.toList := by

  sorry

theorem dropLast_cons {d : Nat} {x₁ x₂ : α} {xs : Vector α d}: Vector.dropLast (x₁ ::ᵥ x₂ ::ᵥ xs) = (x₁ ::ᵥ Vector.dropLast (x₂ ::ᵥ xs)) := by
  rw [dropLast_toList]
  simp only [Vector.toList_dropLast]
  rw [Vector.toList_cons, Vector.toList_cons, List.dropLast_cons]

theorem dropLastComm {n d : Nat} {x : Vector (ZMod n) d} : (vector_zmod_to_bit x.dropLast) = (vector_zmod_to_bit x).dropLast := by
  induction x using Vector.inductionOn with
  | h_nil => 
    simp [vector_zmod_to_bit, Vector.dropLast, Vector.map]
  | h_cons h =>
    simp [vector_zmod_to_bit_cons]
    simp [vector_zmod_to_bit]
    simp [Vector.map]
    sorry

theorem deletion_round_uncps [Fact (perfect_hash poseidon₂)] (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (Proof : Vector F D) (k : F → Prop):
  deletion_round Tree.root Index Item Proof k ↔
  TreeDelete Tree Index Item Proof k := by
  unfold deletion_round
  unfold TreeDelete
  apply Iff.intro
  . rintro ⟨ixbin, _⟩
    casesm* (_ ∧ _)
    have : nat_to_bits_le D (Nat.shiftr Index.val 1) = some (vector_zmod_to_bit ixbin.dropLast) := by
      rw [dropLastComm]
      apply recover_binary_zmod'_to_bits_le_drop_last (v := Index) (w := ixbin)
      sorry
      sorry
      sorry
    unfold MerkleTree.item_at_nat
    unfold MerkleTree.proof_at_nat
    unfold MerkleTree.set_at_nat
    unfold Dir.nat_to_dir_vec
    rw [this]
    simp [←Dir.create_dir_vec_bit]
    sorry
  sorry
  -- apply Iff.intro
  -- . rintro ⟨ixbin, h⟩
  --   casesm* (_ ∧ _)
    
  --   sorry
  -- . rintro ⟨hitem, ⟨hproof, ⟨ftree, ⟨hftree, hresult⟩⟩⟩⟩
  --   sorry

def main : IO Unit := pure ()