import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Ext.Vector

import FormalVerification
import FormalVerification.Utils
import FormalVerification.SemanticEquivalence

open SemaphoreMTB (F Order)

open SemaphoreMTB renaming VerifyProof_31_30 → gVerifyProof
open SemaphoreMTB renaming InsertionRound_30_30 → gInsertionRound
open SemaphoreMTB renaming InsertionProof_4_30_4_4_30 → gInsertionProof

set_option pp.coercions false
/-
def TreeInsert [Fact (CollisionResistant poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Path : Vector F D) (Item : F) : MerkleTree F poseidon₂ D :=
  MerkleTree.set Tree (Dir.create_dir_vec Path).reverse Item

theorem insertion_round_item_validation [Fact (CollisionResistant poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Path : Vector F D) (Proof : Vector F D) (k : F → Prop) :
  insertion_round Path Item Tree.root Proof k → (0:F) = MerkleTree.item_at Tree (Dir.create_dir_vec Path).reverse := by
  intro ⟨H, _⟩
  rw [MerkleTree.recover_tail_equals_recover_reverse] at H
  exact Eq.symm (MerkleTree.proof_ceritfies_item _ _ _ _ H)

theorem insertion_round_proof_validation [Fact (CollisionResistant poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Path : Vector F D) (Item: F) (Proof : Vector F D) (k : F → Prop) :
  insertion_round Path Item Tree.root Proof k → Proof = (MerkleTree.proof Tree (Dir.create_dir_vec Path).reverse).reverse := by
  intro ⟨H, _⟩
  rw [MerkleTree.recover_tail_equals_recover_reverse] at H
  apply Eq.symm
  rw [Vector.vector_reverse_eq]
  exact MerkleTree.recover_proof_reversible H

def TreeInsertZeroVector [Fact (CollisionResistant poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Path : Vector F D) : Prop :=
  MerkleTree.item_at Tree (Dir.create_dir_vec Path).reverse = (0:F)

def TreeInsertZeroZMod [Fact (CollisionResistant poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index : F) : Prop :=
  MerkleTree.tree_item_at_fin Tree Index.val = (0:F)

theorem insertion_round_uncps [Fact (CollisionResistant poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Path : Vector F D) (Item : F) (hzero : TreeInsertZeroVector Tree Path) (k : F → Prop) :
  (let newTree := (MerkleTree.set Tree (Dir.create_dir_vec Path).reverse Item)
  let item := MerkleTree.item_at newTree (Dir.create_dir_vec Path).reverse
  let proof := (MerkleTree.proof newTree (Dir.create_dir_vec Path).reverse).reverse
  insertion_round Path item Tree.root proof k) ↔
  k (TreeInsert Tree Path Item).root := by
  simp
  unfold insertion_round
  unfold TreeInsert
  simp [MerkleTree.recover_tail_equals_recover_reverse]
  simp [MerkleTree.recover_proof_is_root]
  intro
  rw [<-hzero]
  rw [MerkleTree.proof_of_set_is_proof]
  simp [MerkleTree.recover_proof_is_root]

theorem insertion_round_prep_index_validation'
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

theorem insertion_round_prep_index_validation
  (Root Index Item : F) (Proof : Vector F D) (k : F → Prop) :
  insertion_round_prep Index Item Root Proof k → Index.val < 2 ^ D := by
  unfold insertion_round_prep
  intro ⟨out, prop, is_bin, _⟩
  rw [recover_binary_zmod_bit is_bin] at prop
  rw [←prop]
  simp [is_index_in_range]
  rw [binary_nat_zmod_equiv_mod_p]
  apply Nat.lt_of_le_of_lt
  apply Nat.mod_le
  apply binary_nat_lt

theorem insertion_round_prep_zero [Fact (CollisionResistant poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index : F) (Item : F) (ix_small : is_index_in_range D Index) (k : F → Prop) :
  let newTree := MerkleTree.tree_set_at_fin Tree Index.val Item
  let item := MerkleTree.tree_item_at_fin newTree Index.val
  let proof := MerkleTree.tree_proof_at_fin newTree Index.val
  insertion_round_prep Index item Tree.root proof.reverse k → TreeInsertZeroZMod Tree Index := by
  simp
  unfold insertion_round_prep
  rintro ⟨ixbin, _⟩
  casesm* (_ ∧ _)
  rename_i h
  simp [TreeInsertZeroZMod]
  simp [insertion_round] at h
  casesm* (_ ∧ _)
  rename_i hrecov hixbin h _
  simp [MerkleTree.tree_item_at_fin]
  simp [MerkleTree.recover_tail_equals_recover_reverse] at h
  rw [MerkleTree.tree_proof_at_fin, MerkleTree.tree_set_at_fin] at h
  rw [MerkleTree.proof_of_set_is_proof] at h
  apply MerkleTree.proof_ceritfies_item
  . rw [ZMod.cast_eq_val]
    rw [Dir.recover_binary_zmod'_to_dir (w := ixbin)]
    . rw [h]
    . simp [is_index_in_range] at ix_small
      simp [ix_small]
    . simp [Order]
    . simp [hixbin]
    . simp [hrecov]

def TreeInsertPrep [Fact (CollisionResistant poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index : F) (Item : F) (ix_small : is_index_in_range D Index) : MerkleTree F poseidon₂ D :=
  let path := fin_to_bits_le ⟨Index.val, ix_small⟩
  TreeInsert Tree (Vector.map Bit.toZMod path) Item

theorem insertion_round_prep_uncps [Fact (CollisionResistant poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index : F) (Item : F) (ix_small : is_index_in_range D Index) (hzero : TreeInsertZeroZMod Tree Index) (k : F → Prop) :
  (let newTree := MerkleTree.tree_set_at_fin Tree Index.val Item
  let item := MerkleTree.tree_item_at_fin newTree Index.val
  let proof := MerkleTree.tree_proof_at_fin newTree Index.val
  insertion_round_prep Index item Tree.root proof.reverse k) ↔
  k (TreeInsertPrep Tree Index Item ix_small).root := by
  simp
  unfold insertion_round_prep
  apply Iff.intro
  . rintro ⟨ixbin, _⟩
    casesm* (_ ∧ _)
    rename_i h
    rw [MerkleTree.tree_item_at_fin, MerkleTree.tree_proof_at_fin, MerkleTree.tree_set_at_fin] at h
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
      . rw [TreeInsertZeroZMod, MerkleTree.tree_item_at_fin] at hzero
        rw [TreeInsertZeroVector]
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
    rw [MerkleTree.tree_item_at_fin, MerkleTree.tree_proof_at_fin, MerkleTree.tree_set_at_fin]
    rw [ZMod.cast_eq_val]
    rw [Dir.recover_binary_zmod'_to_dir (w := t)]
    rw [insertion_round_uncps]
    simp
    refine ⟨?_, ?_, ?_⟩
    . simp [fin_to_bits_recover_binary]
    . simp [vector_binary_of_bit_to_zmod]
    . simp [h]
    . rw [TreeInsertZeroZMod, MerkleTree.tree_item_at_fin] at hzero
      rw [TreeInsertZeroVector]
      rw [Dir.recover_binary_zmod'_to_dir (w := t)] at hzero
      . simp [hzero]
      . rw [is_index_in_range] at ix_small
        simp [ix_small]
      . simp [Order]
      . simp [vector_binary_of_bit_to_zmod]
      . simp [fin_to_bits_recover_binary]
    . rw [is_index_in_range] at ix_small
      simp [ix_small]
    . simp [Order]
    . simp [vector_binary_of_bit_to_zmod]
    . simp [fin_to_bits_recover_binary]

def TreeInsertCircuit [Fact (CollisionResistant poseidon₂)] {b : Nat}
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

def InsertionLoopTree [Fact (CollisionResistant poseidon₂)] {b : Nat}
  (Tree : MerkleTree F poseidon₂ D) (StartIndex : Nat) (IdComms: Vector F b) (xs_small : is_index_in_range_nat D (StartIndex + b)) (k : MerkleTree F poseidon₂ D → Prop) : Prop :=
  match b with
  | Nat.zero => k Tree
  | Nat.succ i =>
    let newTree := MerkleTree.tree_set_at_fin Tree (StartIndex:F).val IdComms.head
    let item := MerkleTree.tree_item_at_fin newTree (StartIndex:F).val
    let proof := MerkleTree.tree_proof_at_fin newTree (StartIndex:F).val
    ∃t : MerkleTree F poseidon₂ D,
    insertion_round_prep StartIndex item Tree.root proof.reverse (fun nextRoot => t.root = nextRoot) ∧
      InsertionLoopTree t (StartIndex+1) IdComms.tail (by
    simp
    have : StartIndex + Nat.succ i = StartIndex + 1 + i := by
      simp [<-Nat.add_one, add_assoc]
      simp [add_comm]
    rw [<-this]
    simp [xs_small]) k

def InsertionLoopZero [Fact (CollisionResistant poseidon₂)] {b : Nat}
  (Tree : MerkleTree F poseidon₂ D) (StartIndex : Nat) (IdComms: Vector F b) (xs_small : is_index_in_range_nat D (StartIndex + b)) : Prop :=
  match b with
  | Nat.zero => True
  | Nat.succ i =>
    let t := TreeInsertPrep Tree StartIndex IdComms.head (by
    apply is_index_in_range_nat_sum (a := StartIndex) (b := Nat.succ i)
    . simp [D]
    . simp [xs_small])

    MerkleTree.tree_item_at_fin Tree (StartIndex:F).val = (0:F) ∧
    InsertionLoopZero t (StartIndex+1) IdComms.tail (by
    simp
    have : StartIndex + Nat.succ i = StartIndex + 1 + i := by
      simp [<-Nat.add_one, add_assoc]
      simp [add_comm]
    rw [<-this]
    simp [xs_small])

theorem insertion_loop_uncps [Fact (CollisionResistant poseidon₂)] {b : Nat}
  (Tree : MerkleTree F poseidon₂ D) (StartIndex : Nat) (IdComms: Vector F b) (xs_small : is_index_in_range_nat D (StartIndex + b)) (hzero : InsertionLoopZero Tree StartIndex IdComms xs_small) (k : MerkleTree F poseidon₂ D → Prop) :
  (TreeInsertCircuit Tree StartIndex IdComms xs_small k ↔
  InsertionLoopTree Tree StartIndex IdComms xs_small k) := by
  induction b generalizing Tree StartIndex with
  | zero =>
    simp [TreeInsertCircuit, InsertionLoopTree]
  | succ _ ih =>
    simp only [TreeInsertCircuit, InsertionLoopTree]
    simp [InsertionLoopZero] at hzero
    rcases hzero with ⟨hzero, hnext⟩
    apply Iff.intro
    . rintro ⟨tree, htree, hroot⟩
      refine ⟨tree, ?_, ?_⟩
      rw [insertion_round_prep_uncps]
      . rw [MerkleTree.eq_root_eq_tree]
        apply Eq.symm
        . simp [htree]
        . rename_i i
          apply is_index_in_range_nat_sum (a := StartIndex) (b := Nat.succ i)
          . simp [D]
          . simp [xs_small]
      . rw [TreeInsertZeroZMod]
        simp [hzero]
      . rw [<-ih]
        . simp [hroot]
        . rw [<-htree]
          simp [hnext]
    . rintro ⟨tree, htree, hroot⟩
      refine ⟨tree, ?_⟩
      rw [insertion_round_prep_uncps] at htree
      refine ⟨?_, ?_⟩
      . rw [<-MerkleTree.eq_root_eq_tree]
        simp [htree]
      . rw [ih]
        . simp [hroot]
        . rename_i i _
          let t₁ := tree
          let t₂ := TreeInsertPrep Tree (StartIndex) (IdComms.head) (by
          apply is_index_in_range_nat_sum (a := StartIndex) (b := Nat.succ i)
          . simp [D]
          . simp [xs_small])
          rw [MerkleTree.eq_root_eq_tree (t₁ := t₁) (t₂ := t₂)] at htree
          simp at htree
          rw [htree]
          simp [hnext]
      . rw [TreeInsertZeroZMod]
        simp [hzero]

def list_of_items_insert [Fact (CollisionResistant poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (StartIndex : Nat) (IdComms: Vector F b) (xs_small : is_index_in_range_nat D (StartIndex + b)) : Vector F b :=
  match b with
  | Nat.zero => Vector.nil
  | Nat.succ i =>
    let t := (MerkleTree.tree_set_at_fin Tree (StartIndex:F).val IdComms.head)

    let item_at := MerkleTree.tree_item_at_fin t (StartIndex:F).val
    let tail := list_of_items_insert t (StartIndex+1) IdComms.tail (by
    simp
    have : StartIndex + Nat.succ i = StartIndex + 1 + i := by
      simp [<-Nat.add_one, add_assoc]
      simp [add_comm]
    rw [<-this]
    simp [xs_small])
    item_at ::ᵥ tail

def list_of_proofs_insert {b : Nat} [Fact (CollisionResistant poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (StartIndex : Nat) (IdComms: Vector F b) (xs_small : is_index_in_range_nat D (StartIndex + b)) : Vector (Vector F D) b :=
  match b with
  | Nat.zero => Vector.nil
  | Nat.succ i =>
    let t := (MerkleTree.tree_set_at_fin Tree (StartIndex:F).val IdComms.head)

    let proof := (MerkleTree.tree_proof_at_fin t (StartIndex:F).val).reverse
    let tail := list_of_proofs_insert t (StartIndex+1) IdComms.tail (by
    simp
    have : StartIndex + Nat.succ i = StartIndex + 1 + i := by
      simp [<-Nat.add_one, add_assoc]
      simp [add_comm]
    rw [<-this]
    simp [xs_small])

    proof ::ᵥ tail

@[simp]
lemma list_of_items_insert_tail {b : Nat} [Fact (CollisionResistant poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (StartIndex : Nat) (IdComms: Vector F (b+1)) (xs_small : is_index_in_range_nat D (StartIndex + b + 1)) :
  Vector.tail (list_of_items_insert Tree StartIndex IdComms xs_small) =
  let t := TreeInsertPrep Tree (StartIndex:F) IdComms.head (by
  apply is_index_in_range_nat_sum (a := StartIndex) (b := b + 1)
  . simp [D]
  . rw [<-add_assoc]
    simp [xs_small])
  list_of_items_insert t (StartIndex+1) IdComms.tail (by
  simp
  have : StartIndex + 1 + b = StartIndex + b + 1 := by
    simp [<-Nat.add_one, add_assoc]
    simp [add_comm]
  rw [this]
  simp [xs_small]) := by
  simp
  simp [list_of_items_insert]
  simp [MerkleTree.tree_set_at_fin]
  simp [TreeInsertPrep]
  simp [TreeInsert]
  rw [<-Dir.recover_binary_zmod'_to_dir]
  . tauto
  . rw [is_index_in_range_nat] at xs_small
    rw [ZMod.val_cast_of_lt]
    . linarith
    . simp [D] at xs_small
      simp [Order]
      linarith
  . simp [Order, D]
  . simp [vector_binary_of_bit_to_zmod]
  . simp [fin_to_bits_recover_binary]

@[simp]
lemma list_of_proofs_insert_tail {b : Nat} [Fact (CollisionResistant poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (StartIndex : Nat) (IdComms: Vector F (b+1)) (xs_small : is_index_in_range_nat D (StartIndex + b + 1)) :
  Vector.tail (list_of_proofs_insert Tree StartIndex IdComms xs_small) =
  let t := TreeInsertPrep Tree (StartIndex:F) IdComms.head (by
  apply is_index_in_range_nat_sum (a := StartIndex) (b := b + 1)
  . simp [D]
  . rw [<-add_assoc]
    simp [xs_small])
  list_of_proofs_insert t (StartIndex+1) IdComms.tail (by
  simp
  have : StartIndex + 1 + b = StartIndex + b + 1 := by
    simp [<-Nat.add_one, add_assoc]
    simp [add_comm]
  rw [this]
  simp [xs_small]) := by
  simp
  simp [list_of_items_insert]
  simp [MerkleTree.tree_set_at_fin]
  simp [TreeInsertPrep]
  simp [TreeInsert]
  rw [<-Dir.recover_binary_zmod'_to_dir]
  . tauto
  . rw [is_index_in_range_nat] at xs_small
    rw [ZMod.val_cast_of_lt]
    . linarith
    . simp [D] at xs_small
      simp [Order]
      linarith
  . simp [Order, D]
  . simp [vector_binary_of_bit_to_zmod]
  . simp [fin_to_bits_recover_binary]

theorem insertion_loop_equivalence [Fact (CollisionResistant poseidon₂)] {b : Nat}
  (Tree : MerkleTree F poseidon₂ D) (StartIndex : Nat) (IdComms: Vector F b) (xs_small : is_index_in_range_nat D (StartIndex + b)) (hzero : InsertionLoopZero Tree StartIndex IdComms xs_small) (k : F -> Prop) :
  InsertionLoopTree Tree StartIndex IdComms xs_small (fun newTree => k newTree.root) ↔
  (let items := list_of_items_insert Tree StartIndex IdComms xs_small
  let proofs := list_of_proofs_insert Tree StartIndex IdComms xs_small
  InsertionLoop StartIndex Tree.root items proofs k) := by
  simp
  apply Iff.intro
  . induction b generalizing Tree StartIndex with
    | zero =>
      simp [InsertionLoopTree, InsertionLoop]
    | succ _ ih =>
      simp [InsertionLoopZero] at hzero
      rcases hzero with ⟨hzero', hzero⟩
      simp only [InsertionLoopTree]
      rintro ⟨tree, htree, hroot⟩
      simp only [list_of_items_insert] at htree
      simp only [Vector.head_cons] at htree
      rw [insertion_round_prep_uncps] at htree
      rename_i i _
      let t₁ := tree
      let t₂ := TreeInsertPrep Tree (StartIndex) (IdComms.head) (by
      apply is_index_in_range_nat_sum (a := StartIndex) (b := Nat.succ i)
      . simp [D]
      . simp [xs_small])
      rw [MerkleTree.eq_root_eq_tree (t₁ := t₁) (t₂ := t₂)] at htree
      simp at htree
      rw [InsertionLoop]
      nth_rewrite 1 [list_of_items_insert, list_of_proofs_insert]
      simp only [Vector.head_cons]
      rw [insertion_round_prep_uncps]
      . simp only [list_of_items_insert_tail]
        simp only [list_of_proofs_insert_tail]
        rw [htree] at hroot
        have : @Nat.cast F Semiring.toNatCast StartIndex + 1 = Nat.cast (StartIndex + 1) := by
          simp [Nat.cast]
        rw [this]
        apply ih
        simp [hzero]
        simp [hroot]
      . rw [TreeInsertZeroZMod]
        simp [hzero']
      . rw [TreeInsertZeroZMod]
        simp [hzero']
  . induction b generalizing Tree StartIndex with
    | zero =>
      simp [InsertionLoopTree, InsertionLoop]
    | succ _ ih =>
      intro htree
      simp only [InsertionLoopTree]
      simp [InsertionLoop] at htree
      rename_i i
      let t := TreeInsertPrep Tree (StartIndex) (IdComms.head) (by
        apply is_index_in_range_nat_sum (a := StartIndex) (b := Nat.succ i)
        . simp [D]
        . simp [xs_small])
      refine ⟨t, ?_⟩
      nth_rewrite 1 [list_of_items_insert, list_of_proofs_insert] at htree
      simp only [Vector.head_cons] at htree
      rw [insertion_round_prep_uncps] at htree
      . rw [insertion_round_prep_uncps, MerkleTree.eq_root_eq_tree]
        refine ⟨?_, ?_⟩
        . tauto
        . apply ih
          simp [InsertionLoopZero] at hzero
          rcases hzero with ⟨_, hzero⟩
          simp [hzero]
          simp [htree]
        . rw [TreeInsertZeroZMod]
          simp [InsertionLoopZero] at hzero
          rcases hzero with ⟨hzero', _⟩
          simp [hzero']
      . apply is_index_in_range_nat_sum (a := StartIndex) (b := Nat.succ i)
        . simp [D]
        . simp [xs_small]
      . rw [TreeInsertZeroZMod]
        simp [InsertionLoopZero] at hzero
        rcases hzero with ⟨hzero', _⟩
        simp [hzero']

theorem insertion_loop_equivalence' [Fact (CollisionResistant poseidon₂)] {b : Nat}
  (Tree : MerkleTree F poseidon₂ D) (StartIndex : Nat) (IdComms: Vector F b) (xs_small : is_index_in_range_nat D (StartIndex + b)) (hzero : InsertionLoopZero Tree StartIndex IdComms xs_small) (k : F -> Prop) :
  TreeInsertCircuit Tree StartIndex IdComms xs_small (fun newTree => k newTree.root) ↔
  (let items := list_of_items_insert Tree StartIndex IdComms xs_small
  let proofs := list_of_proofs_insert Tree StartIndex IdComms xs_small
  InsertionLoop StartIndex Tree.root items proofs k) := by
  simp
  rw [<-insertion_loop_equivalence]
  apply insertion_loop_uncps
  . simp [hzero]
  . simp [hzero]

theorem before_insertion_all_zeroes [Fact (CollisionResistant poseidon₂)] {b : Nat}
  (Tree : MerkleTree F poseidon₂ D) (StartIndex: Nat) (IdComms: Vector F b) (xs_small : is_index_in_range_nat D (StartIndex + b)) :
  (let items := list_of_items_insert Tree StartIndex IdComms xs_small
  let proofs := list_of_proofs_insert Tree StartIndex IdComms xs_small
  InsertionLoop StartIndex Tree.root items proofs k) →
  InsertionLoopZero Tree StartIndex IdComms xs_small := by
  simp
  induction b generalizing Tree StartIndex with
  | zero => simp [InsertionLoop, InsertionLoopZero]
  | succ i ih =>
    intro htree
    simp [InsertionLoop] at htree
    simp [InsertionLoopZero]
    nth_rewrite 1 [list_of_items_insert, list_of_proofs_insert] at htree
    simp only [Vector.head_cons] at htree
    rw [insertion_round_prep_uncps] at htree
    . refine ⟨?_, ?_⟩
      . apply insertion_round_prep_zero
        . apply is_index_in_range_nat_sum (a := StartIndex) (b := Nat.succ i)
          . simp [D]
          . simp [xs_small]
        . assumption
      . apply ih
        simp [htree]
    . apply is_index_in_range_nat_sum (a := StartIndex) (b := Nat.succ i)
      . simp [D]
      . simp [xs_small]
    . apply insertion_round_prep_zero
      . apply is_index_in_range_nat_sum (a := StartIndex) (b := Nat.succ i)
        . simp [D]
        . simp [xs_small]
      . assumption

lemma TreeInsertPrep_equivalence [Fact (CollisionResistant poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index : F) (Item : F) (ix_small : is_index_in_range D Index) :
  TreeInsertPrep Tree Index Item ix_small = Tree.set (Vector.reverse (Dir.fin_to_dir_vec Index)) Item := by
  rw [TreeInsertPrep, TreeInsert]
  rw [ZMod.cast_eq_val]
  rw [Dir.recover_binary_zmod'_to_dir]
  . simp [is_index_in_range] at ix_small
    linarith
  . simp [Order, D]
  . simp [vector_binary_of_bit_to_zmod]
  . simp [fin_to_bits_recover_binary]

lemma TreeInsertPrep_equivalence' [Fact (CollisionResistant poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index : F) (Item : F) (ix_small : is_index_in_range D Index) :
  TreeInsertPrep Tree Index Item ix_small = Tree.tree_set_at_fin Index Item := by
  rw [TreeInsertPrep_equivalence]
  rw [MerkleTree.tree_set_at_fin]

theorem before_insertion_all_zeroes_batch'
  [Fact (CollisionResistant poseidon₂)]
  {Tree: MerkleTree F poseidon₂ D}
  {StartIndex b: Nat} {IdComms: Vector F b} {xs_small : is_index_in_range_nat D (StartIndex + b)} {k : F -> Prop} :
  (let items := list_of_items_insert Tree StartIndex IdComms xs_small
  let proofs := list_of_proofs_insert Tree StartIndex IdComms xs_small
  InsertionLoop StartIndex Tree.root items proofs k) →
  (∀ i ∈ [StartIndex:StartIndex + b], MerkleTree.tree_item_at_fin Tree (i:F).val = (0:F)) := by
  induction b generalizing StartIndex Tree with
  | zero =>
    intro _ i range
    rcases range with ⟨lo, hi⟩
    have := Nat.ne_of_lt (Nat.lt_of_le_of_lt lo hi)
    contradiction
  | succ b ih =>
    intro hp i range
    rcases range with ⟨lo, hi⟩; simp at lo hi
    have hStartIndexCast : ZMod.val (StartIndex : F) = StartIndex := by
      apply ZMod.val_cast_of_lt
      rw [is_index_in_range_nat, D] at xs_small
      rw [Order]
      linarith
    cases lo with
    | refl =>
      rw [InsertionLoop] at hp
      nth_rewrite 1 [list_of_items_insert, list_of_proofs_insert] at hp
      simp only [Vector.head_cons] at hp
      apply insertion_round_prep_zero
      . apply is_index_in_range_nat_sum (a := StartIndex) (b := Nat.succ b)
        . simp [D]
        . simp [xs_small]
      . assumption
    | @step StartIndex' h =>
      rw [InsertionLoop] at hp
      nth_rewrite 1 [list_of_items_insert, list_of_proofs_insert] at hp
      simp only [Vector.head_cons] at hp
      unfold insertion_round_prep at hp
      rcases hp with ⟨ixdir, ⟨hixdir, ⟨hvec, ⟨hrecover, hnext⟩⟩⟩⟩
      simp [MerkleTree.recover_tail_equals_recover_reverse] at hrecover

      have : ∃newTree, MerkleTree.tree_set_at_fin Tree StartIndex IdComms.head = newTree := by
        simp [hrecover]
      rcases this with ⟨postTree, hinsert⟩
      rw [←MerkleTree.item_at_fin_invariant hinsert]

      rw [MerkleTree.recover_tail_equals_recover_reverse, Vector.reverse_reverse] at hnext
      rw [MerkleTree.tree_proof_at_fin, MerkleTree.tree_item_at_fin] at hnext
      have : (Dir.create_dir_vec ixdir).reverse = Vector.reverse (Dir.fin_to_dir_vec (StartIndex:F).val) := by
        apply congr_arg
        rw [Dir.recover_binary_zmod'_to_dir]
        . simp [is_index_in_range_nat] at xs_small
          linarith
        . simp [Order, D]
        . simp [hvec]
        . simp [hixdir]
      rw [<-this] at hnext
      rw [MerkleTree.recover_proof_is_root] at hnext

      have : @Nat.cast F Semiring.toNatCast StartIndex' + 1 = Nat.cast (StartIndex' + 1) := by
        simp [Nat.cast]
      simp
      rw [this]

      simp at ih
      simp [list_of_items_insert_tail, list_of_proofs_insert_tail] at hnext
      have : @Nat.cast F Semiring.toNatCast StartIndex + 1 = Nat.cast (StartIndex + 1) := by
        simp [Nat.cast]
      rw [this] at hnext
      rw [TreeInsertPrep_equivalence'] at hnext
      rw [ZMod.cast_eq_val, ZMod.val_cast_of_lt] at hnext
      rw [hinsert] at hnext

      apply ih hnext (StartIndex' + 1)
      . apply And.intro
        . simp_arith; simp [Nat.le] at h; simp [h]
        . simp; linarith
      . simp [Order]
        simp [is_index_in_range_nat, D] at xs_small
        linarith
      . rw [ZMod.val_cast_of_lt]
        apply Nat.ne_of_lt
        . simp_arith; simp [Nat.le] at h; simp [h]
        . simp [Order]
          simp [is_index_in_range_nat, D] at xs_small
          linarith
      . simp [is_index_in_range_nat] at xs_small
        linarith
      . rw [ZMod.val_cast_of_lt]
        . simp [Nat.le] at h
          simp [is_index_in_range_nat] at xs_small
          linarith
        . simp [Order]
          simp [is_index_in_range_nat, D] at xs_small
          linarith
-/
def foo := 10
