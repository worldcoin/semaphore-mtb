import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Ext.Vector

import FormalVerification
import FormalVerification.SemanticEquivalence

open SemaphoreMTB (F Order)

variable [Fact (Nat.Prime Order)]

open SemaphoreMTB renaming VerifyProof_31_30 → gVerifyProof
open SemaphoreMTB renaming InsertionRound_30_30 → gInsertionRound
open SemaphoreMTB renaming InsertionProof_4_30_4_4_30 → gInsertionProof

set_option pp.coercions false

------------ MISC

def is_index_in_range {n : Nat} (D : Nat) (a : ZMod n) : Prop :=
  a.val < 2^D

def is_index_in_range_nat (D : Nat) (a : Nat) : Prop :=
  a < 2^D

lemma is_index_in_range_nat_sum {n : Nat} (D : Nat) (a b : Nat) (h : 2^D < n): is_index_in_range_nat D (a + b) → is_index_in_range D (a:ZMod n) := by
  intro xs_small
  rw [is_index_in_range_nat] at xs_small
  rw [is_index_in_range]
  rw [ZMod.val_cast_of_lt]
  . linarith
  . linarith

def are_indices_in_range {d n : Nat} (D : Nat) (a : Vector (ZMod n) d) : Prop :=
  List.foldr (fun x r => (is_index_in_range D x) ∧ r) True a.toList

theorem are_indices_in_range_cons {d n : Nat} (D : Nat) (a : ZMod n) (vec : Vector (ZMod n) d) :
  are_indices_in_range D (a ::ᵥ vec) ↔ is_index_in_range D a ∧ are_indices_in_range D vec := by
  unfold are_indices_in_range
  conv => lhs; unfold List.foldr; simp

theorem are_indices_in_range_split {d n : Nat} (D : Nat) (a : Vector (ZMod n) (d+1)) :
  are_indices_in_range D a ↔ is_index_in_range D a.head ∧ are_indices_in_range D a.tail := by
  rw [<-are_indices_in_range_cons]
  simp

lemma head_index_in_range {b : Nat} (D : Nat) (Index : Vector (ZMod n) (b+1)) (xs_small : are_indices_in_range D Index) :
  is_index_in_range D (Vector.head Index) := by
  rw [are_indices_in_range_split] at xs_small
  cases xs_small
  rename_i x xs
  simp [x]

lemma tail_index_in_range {b : Nat} (D : Nat) (Index : Vector (ZMod n) (b+1)) (xs_small : are_indices_in_range D Index) :
  are_indices_in_range D (Vector.tail Index) := by
  rw [are_indices_in_range_split] at xs_small
  cases xs_small
  rename_i x xs
  simp [xs]

lemma proof_of_set
  {F d}
  (H : Hash F 2)
  [Fact (perfect_hash H)]
  (Tree : MerkleTree F H d)
  (ix : Vector Dir d)
  (item : F):
  (MerkleTree.proof (MerkleTree.set Tree ix item) ix) = MerkleTree.proof Tree ix := by
  induction d with
  | zero =>
    simp [MerkleTree.set, MerkleTree.proof]
  | succ d ih =>
    cases Tree
    simp [MerkleTree.set, MerkleTree.proof, MerkleTree.tree_for]
    split
    . rename_i hdir
      have : Dir.swap (Dir.swap (Vector.head ix)) = Dir.right := by
        rw [hdir]
        simp [Dir.swap]
      have : Vector.head ix = Dir.right := by
        rw [<-this]
        simp [Dir.swap]
        cases ix.head
        . simp
        . simp
      rw [this]
      simp [MerkleTree.set, MerkleTree.left, MerkleTree.right]
      simp [Vector.vector_eq_cons]
      rw [ih]
    . rename_i hdir
      have : Dir.swap (Dir.swap (Vector.head ix)) = Dir.left := by
        rw [hdir]
        simp [Dir.swap]
      have : Vector.head ix = Dir.left := by
        rw [<-this]
        simp [Dir.swap]
        cases ix.head
        . simp
        . simp
      rw [this]
      simp [MerkleTree.set, MerkleTree.left, MerkleTree.right]
      simp [Vector.vector_eq_cons]
      rw [ih]

def tree_item_at_fin {F: Type} {H: Hash F 2} (Tree : MerkleTree F H d) (i : Fin (2^d)): F :=
  MerkleTree.item_at Tree (Dir.fin_to_dir_vec i).reverse

def tree_proof_at_fin {F: Type} {H: Hash F 2} (Tree : MerkleTree F H d) (i : Fin (2^d)): Vector F d :=
  MerkleTree.proof Tree (Dir.fin_to_dir_vec i).reverse

def tree_set_at_fin {F: Type} {H: Hash F 2} (Tree : MerkleTree F H d) (i : Fin (2^d)) (Item : F): MerkleTree F H d :=
  MerkleTree.set Tree (Dir.fin_to_dir_vec i).reverse Item

------------

def TreeInsert [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Path : Vector F D) (Item : F) : MerkleTree F poseidon₂ D :=
  MerkleTree.set Tree (Dir.create_dir_vec Path).reverse Item

theorem insertion_round_item_validation [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Path : Vector F D) (Proof : Vector F D) (k : F → Prop) :
  insertion_round Path Item Tree.root Proof k → (0:F) = MerkleTree.item_at Tree (Dir.create_dir_vec Path).reverse := by
  intro ⟨H, _⟩
  rw [MerkleTree.recover_tail_equals_recover_reverse] at H
  exact Eq.symm (MerkleTree.proof_ceritfies_item _ _ _ _ H)

theorem insertion_round_proof_validation [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Path : Vector F D) (Item: F) (Proof : Vector F D) (k : F → Prop) :
  insertion_round Path Item Tree.root Proof k → Proof = (MerkleTree.proof Tree (Dir.create_dir_vec Path).reverse).reverse := by
  intro ⟨H, _⟩
  rw [MerkleTree.recover_tail_equals_recover_reverse] at H
  apply Eq.symm
  rw [Vector.vector_reverse_eq]
  exact MerkleTree.recover_proof_reversible H

theorem insertion_round_uncps [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Path : Vector F D) (Item : F) (k : F → Prop) :
  let newTree := (MerkleTree.set Tree (Dir.create_dir_vec Path).reverse Item)
  let item := MerkleTree.item_at newTree (Dir.create_dir_vec Path).reverse
  let proof := (MerkleTree.proof newTree (Dir.create_dir_vec Path).reverse).reverse
  MerkleTree.item_at Tree (Dir.create_dir_vec Path).reverse = (0:F) →
  (insertion_round Path item Tree.root proof k ↔
  k (TreeInsert Tree Path Item).root) := by
  simp
  intro hzero
  unfold insertion_round
  unfold TreeInsert
  simp [MerkleTree.recover_tail_equals_recover_reverse]
  simp [MerkleTree.recover_proof_is_root]
  intro
  rw [<-hzero]
  rw [proof_of_set]
  simp [MerkleTree.recover_proof_is_root]

theorem insertion_round_prep_index_validation
  (Root Index Item : F) (Proof : Vector F D) (k : F → Prop) :
  insertion_round_prep Index Item Root Proof k → is_index_in_range D Index := by
  unfold insertion_round_prep
  intro ⟨out, prop, is_bin, _⟩
  rw [recover_binary_zmod_bit is_bin] at prop
  rw [←prop]
  simp [is_index_in_range]
  rw [binary_nat_zmod_equiv_mod_p]
  apply Nat.lt_of_le_of_lt
  apply Nat.mod_le
  apply binary_nat_lt

def TreeInsertPrep [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index : F) (Item : F) (ix_small : is_index_in_range D Index) : MerkleTree F poseidon₂ D :=
  let path := fin_to_bits_le ⟨Index.val, ix_small⟩
  TreeInsert Tree (Vector.map Bit.toZMod path) Item

theorem insertion_round_prep_uncps [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index : F) (Item : F) (ix_small : is_index_in_range D Index) (k : F → Prop) :
  let newTree := tree_set_at_fin Tree Index.val Item
  let item := tree_item_at_fin newTree Index.val
  let proof := tree_proof_at_fin newTree Index.val
  tree_item_at_fin Tree Index = (0:F) →
  (insertion_round_prep Index item Tree.root proof.reverse k ↔
  k (TreeInsertPrep Tree Index Item ix_small).root) := by
  simp
  intro hzero
  unfold insertion_round_prep
  apply Iff.intro
  . rintro ⟨ixbin, _⟩
    casesm* (_ ∧ _)
    rename_i h
    rw [tree_item_at_fin, tree_proof_at_fin, tree_set_at_fin] at h
    rw [ZMod.cast_eq_val] at h
    rw [Dir.recover_binary_zmod'_to_dir (w := ixbin)] at h
    . unfold TreeInsertPrep
      rw [insertion_round_uncps] at h
      rw [fin_to_bits_le_to_recover_binary_zmod' (v := Index) (w := ixbin)]
      . simp
        rw [vector_zmod_to_bit_to_zmod]
        . simp [h]
        . assumption
      . simp [ix_small]
      . assumption
      . assumption
      . assumption
      . rw [tree_item_at_fin] at hzero
        rw [ZMod.cast_eq_val] at hzero
        rw [Dir.recover_binary_zmod'_to_dir (w := ixbin)] at hzero
        . simp [hzero]
        . rw [is_index_in_range] at ix_small
          simp [ix_small]
        . simp [Order]
        . assumption
        . assumption
    . simp [is_index_in_range] at ix_small
      simp [ix_small]
    . simp [Order]
    . assumption
    . assumption
  . intro h
    simp [TreeInsertPrep] at h
    let t : Vector F D := Vector.map Bit.toZMod (fin_to_bits_le ⟨Index.val, ix_small⟩)
    refine ⟨t, ?_⟩
    rw [tree_item_at_fin, tree_proof_at_fin, tree_set_at_fin]
    rw [ZMod.cast_eq_val]
    rw [Dir.recover_binary_zmod'_to_dir (w := t)]
    rw [insertion_round_uncps]
    simp
    refine ⟨?_, ?_, ?_⟩
    . rw [recover_binary_of_to_bits]
      rw [fin_to_bits_le]
      split
      . assumption
      . contradiction
    . simp [vector_binary_of_bit_to_zmod]
    . simp [h]
    . rw [tree_item_at_fin] at hzero
      rw [ZMod.cast_eq_val] at hzero
      rw [Dir.recover_binary_zmod'_to_dir (w := t)] at hzero
      . simp [hzero]
      . rw [is_index_in_range] at ix_small
        simp [ix_small]
      . simp [Order]
      . simp [vector_binary_of_bit_to_zmod]
      . rw [recover_binary_of_to_bits]
        simp [fin_to_bits_le]
        split
        . assumption
        . contradiction
    . rw [is_index_in_range] at ix_small
      simp [ix_small]
    . simp [Order]
    . simp [vector_binary_of_bit_to_zmod]
    . rw [recover_binary_of_to_bits]
      simp [fin_to_bits_le]
      split
      . assumption
      . contradiction

def TreeInsertZero [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index : F) (ix_small : is_index_in_range D Index) : Prop :=
  let path := fin_to_bits_le ⟨Index.val, ix_small⟩
  let idx := Vector.map (fun x => @Bit.toZMod Order x) path
  MerkleTree.item_at Tree (Dir.create_dir_vec idx).reverse = (0:F)

-- theorem deletion_round_set_zero [Fact (perfect_hash poseidon₂)]
--   (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (ix_small : is_index_in_range D Index) :
--   TreeInsertPrep Tree Index Item ix_small = t →
--   TreeInsertZero Tree Index ix_small := by
--   intro htree
--   unfold TreeInsertPrep at htree
--   unfold TreeInsert at htree
--   simp [TreeInsertZero]
--   apply MerkleTree.set_implies_item_at (t₁ := Tree)
--   sorry

def TreeInsertCircuit [Fact (perfect_hash poseidon₂)] {b : Nat}
  (InitialTree : MerkleTree F poseidon₂ D) (StartIndex : Nat) (IdComms: Vector F b) (xs_small : is_index_in_range_nat D (StartIndex + b)) (k : MerkleTree F poseidon₂ D → Prop) : Prop :=
  match b with
  | Nat.zero => k InitialTree
  | Nat.succ i =>
    ∃newTree, TreeInsertPrep InitialTree StartIndex IdComms.head (by
    apply is_index_in_range_nat_sum (a := StartIndex) (b := Nat.succ i)
    . simp [D]
    . simp [xs_small]) = newTree ∧
    TreeInsertCircuit newTree (StartIndex+1) IdComms.tail (by
    simp
    have : StartIndex + Nat.succ i = StartIndex + 1 + i := by
      simp [<-Nat.add_one, add_assoc]
      simp [add_comm]
    rw [<-this]
    simp [xs_small]) k

-- TreeInsertCircuitZero

-- before_insertion_all_zeroes

def InsertionLoopTree [Fact (perfect_hash poseidon₂)] {b : Nat}
  (Tree : MerkleTree F poseidon₂ D) (StartIndex : Nat) (IdComms: Vector F b) (xs_small : is_index_in_range_nat D (StartIndex + b)) (k : MerkleTree F poseidon₂ D → Prop) : Prop :=
  match b with
  | Nat.zero => k Tree
  | Nat.succ i =>
    ∃t : MerkleTree F poseidon₂ D,
    insertion_round_prep StartIndex IdComms.head Tree.root (tree_proof_at_fin Tree StartIndex).reverse (fun nextRoot => t.root = nextRoot) ∧
      InsertionLoopTree t (StartIndex+1) IdComms.tail (by
    simp
    have : StartIndex + Nat.succ i = StartIndex + 1 + i := by
      simp [<-Nat.add_one, add_assoc]
      simp [add_comm]
    rw [<-this]
    simp [xs_small]) k

def insertion_loop_uncps [Fact (perfect_hash poseidon₂)] {b : Nat}
  (Tree : MerkleTree F poseidon₂ D) (StartIndex : Nat) (IdComms: Vector F b) (xs_small : is_index_in_range_nat D (StartIndex + b)) (k : MerkleTree F poseidon₂ D → Prop) :
  TreeInsertCircuit Tree StartIndex IdComms xs_small k ↔
  InsertionLoopTree Tree StartIndex IdComms xs_small k := by

  sorry
