import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Ext.Vector

import FormalVerification
import FormalVerification.SemanticEquivalence

open SemaphoreMTB (F Order)

variable [Fact (Nat.Prime Order)]

open SemaphoreMTB renaming VerifyProof_31_30 → gVerifyProof
open SemaphoreMTB renaming DeletionRound_30_30 → gDeletionRound
open SemaphoreMTB renaming DeletionProof_4_4_30_4_4_30 → gDeletionProof

set_option pp.coercions false

------------------- MISC

def is_index_in_range {n : Nat} (D : Nat) (a : ZMod n) : Prop :=
  a.val < 2^D

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

lemma head_index_in_range {b : Nat} (D : Nat) (Index : Vector F (b+1)) (xs_small : are_indices_in_range D Index) :
  is_index_in_range D (Vector.head Index) := by
  rw [are_indices_in_range_split] at xs_small
  cases xs_small
  rename_i x xs
  simp [x]

lemma tail_index_in_range {b : Nat} (D : Nat) (Index : Vector F (b+1)) (xs_small : are_indices_in_range D Index) :
  are_indices_in_range D (Vector.tail Index) := by
  rw [are_indices_in_range_split] at xs_small
  cases xs_small
  rename_i x xs
  simp [xs]

theorem eq_root_eq_tree {H} [ph: Fact (perfect_hash H)] {t₁ t₂ : MerkleTree α H d}:
  t₁.root = t₂.root ↔ t₁ = t₂ := by
  induction d with
  | zero => cases t₁; cases t₂; tauto
  | succ _ ih =>
    cases t₁
    cases t₂
    apply Iff.intro
    . intro h
      have h := Fact.elim ph h
      injection h with h
      injection h with _ h
      injection h
      congr <;> {rw [←ih]; assumption}
    . intro h
      injection h
      subst_vars
      rfl

------------------

def TreeDelete [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Skip : Bit) (Path : Vector F D): MerkleTree F poseidon₂ D :=
  match Skip with
  | Bit.zero => (MerkleTree.set Tree (Dir.create_dir_vec Path).reverse 0)
  | Bit.one => Tree

theorem deletion_round_item_validation [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Path : Vector F D) (Item: F) (Proof : Vector F D) (k : F → Prop) :
  deletion_round Tree.root Bit.zero Path Item Proof k → Item = MerkleTree.item_at Tree (Dir.create_dir_vec Path).reverse := by
  intro ⟨H, _⟩
  rw [MerkleTree.recover_tail_equals_recover_reverse] at H
  exact Eq.symm (MerkleTree.proof_ceritfies_item _ _ _ _ H)

theorem deletion_round_proof_validation [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Path : Vector F D) (Item: F) (Proof : Vector F D) (k : F → Prop) :
  deletion_round Tree.root Bit.zero Path Item Proof k → Proof = (MerkleTree.proof Tree (Dir.create_dir_vec Path).reverse).reverse := by
  intro ⟨H, _⟩
  rw [MerkleTree.recover_tail_equals_recover_reverse] at H
  apply Eq.symm
  rw [Vector.vector_reverse_eq]
  exact MerkleTree.recover_proof_reversible H

theorem deletion_round_uncps [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Skip : Bit) (Path : Vector F D) (k : F → Prop) :
  deletion_round Tree.root Skip Path (MerkleTree.item_at Tree (Dir.create_dir_vec Path).reverse) (MerkleTree.proof Tree (Dir.create_dir_vec Path).reverse).reverse k ↔
  k (TreeDelete Tree Skip Path).root := by
  unfold deletion_round
  unfold TreeDelete
  cases Skip with
  | zero =>
    simp [MerkleTree.recover_tail_equals_recover_reverse, MerkleTree.recover_proof_is_root]
    apply Iff.of_eq
    apply congrArg
    apply MerkleTree.proof_insert_invariant
    apply MerkleTree.recover_proof_is_root
  | one => rfl

theorem deletion_round_prep_index_validation
  (Root Index Item : F) (Proof : Vector F D) (k : F → Prop) :
  deletion_round_prep Root Index Item Proof k → is_index_in_range (D+1) Index := by
  unfold deletion_round_prep
  intro ⟨out, prop, is_bin, _⟩
  rw [recover_binary_zmod_bit is_bin] at prop
  rw [←prop]
  simp [is_index_in_range]
  rw [binary_nat_zmod_equiv_mod_p]
  apply Nat.lt_of_le_of_lt
  apply Nat.mod_le
  apply binary_nat_lt

def TreeDeletePrep [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index : F) (ix_small : is_index_in_range (D+1) Index) : MerkleTree F poseidon₂ D :=
  let path := fin_to_bits_le ⟨Index.val, ix_small⟩
  TreeDelete Tree (path.last) (Vector.map Bit.toZMod path.dropLast)

theorem deletion_round_prep_uncps [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index : F) (ix_small : is_index_in_range (D+1) Index) (k : F → Prop) :
  deletion_round_prep Tree.root Index (MerkleTree.tree_item_at_fin Tree Index.val) (MerkleTree.tree_proof_at_fin Tree Index.val).reverse k ↔
  k (TreeDeletePrep Tree Index ix_small).root := by
  unfold deletion_round_prep
  apply Iff.intro
  . rintro ⟨ixbin, _⟩
    casesm* (_ ∧ _)
    rename_i h
    rw [MerkleTree.tree_item_at_fin, MerkleTree.tree_proof_at_fin] at h
    rw [Dir.recover_binary_zmod'_to_dir (w := ixbin)] at h
    . unfold TreeDeletePrep
      rw [<-Dir.dropLastOrder] at h
      let s := zmod_to_bit (Vector.last ixbin)
      let p := ixbin.dropLast
      rw [deletion_round_uncps Tree s p] at h
      rw [fin_to_bits_le_to_recover_binary_zmod' (v := Index) (w := ixbin)]
      . simp [vector_zmod_to_bit_last]
        rw [vector_zmod_to_bit_dropLast]
        simp [h]
        assumption
      . simp [ix_small]
      . assumption
      . assumption
      . assumption
    . assumption
    . simp [Order]
    . assumption
    . assumption
  . intro h
    simp [TreeDeletePrep] at h
    let t : Vector F (D+1) := Vector.map Bit.toZMod (fin_to_bits_le ⟨Index.val, ix_small⟩)
    refine ⟨t, ?_⟩
    rw [MerkleTree.tree_item_at_fin, MerkleTree.tree_proof_at_fin]
    rw [Dir.recover_binary_zmod'_to_dir (w := t)]
    rw [<-Dir.dropLastOrder]
    let s := (zmod_to_bit (Vector.last t))
    let p := (Vector.dropLast t)
    rw [deletion_round_uncps Tree s p]
    simp
    refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
    . rw [recover_binary_of_to_bits]
      rw [fin_to_bits_le]
      split
      . assumption
      . contradiction
    . simp [vector_binary_of_bit_to_zmod]
    . simp [Bit.toZMod, is_bit, Vector.last]
      split
      . simp
      . simp
    . rw [<-dropLast_symm]
      rw [vector_bit_to_zmod_last]
      simp [h]
    . simp [is_index_in_range] at ix_small
      simp [ix_small]
    . simp [Order]
    . simp [vector_binary_of_bit_to_zmod]
    . rw [recover_binary_of_to_bits]
      simp [fin_to_bits_le]
      split
      . assumption
      . contradiction

def TreeDeleteZero [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index : F) (ix_small : is_index_in_range (D+1) Index) : Prop :=
  let path := fin_to_bits_le ⟨Index.val, ix_small⟩
  let skipFlag := path.last
  let idx := Vector.map (fun x => @Bit.toZMod Order x) path.dropLast
  match skipFlag with
  | Bit.zero => MerkleTree.item_at Tree (Dir.create_dir_vec idx).reverse = (0:F)
  | Bit.one => True

theorem deletion_round_set_zero [Fact (perfect_hash poseidon₂)]
  (Tree₁ : MerkleTree F poseidon₂ D) (Index : F) (ix_small : is_index_in_range (D+1) Index) :
  TreeDeletePrep Tree₁ Index ix_small = t →
  TreeDeleteZero t Index ix_small := by
  intro htree
  unfold TreeDeletePrep at htree
  unfold TreeDelete at htree
  simp [TreeDeleteZero]
  split
  . rename_i hskip
    simp [hskip] at htree
    apply MerkleTree.set_implies_item_at (t₁ := Tree₁)
    simp [htree]
  . simp

def TreeDeleteCircuit [Fact (perfect_hash poseidon₂)] {b : Nat}
  (InitialTree : MerkleTree F poseidon₂ D) (Index : Vector F b) (xs_small : are_indices_in_range (D+1) Index) (k : MerkleTree F poseidon₂ D → Prop) : Prop :=
  match b with
  | Nat.zero => k InitialTree
  | Nat.succ _ =>
    ∃newTree, TreeDeletePrep InitialTree Index.head (by apply head_index_in_range (D+1); simp [xs_small]) = newTree ∧
    TreeDeleteCircuit newTree Index.tail (by apply tail_index_in_range (D+1); simp [xs_small]) k

def TreeDeleteCircuitZero [Fact (perfect_hash poseidon₂)] {b : Nat}
  (Index : Vector F b) (xs_small : are_indices_in_range (D+1) Index) : Prop :=
  match b with
  | Nat.zero => True
  | Nat.succ _ =>
    ∃t, TreeDeleteZero t Index.head (by apply head_index_in_range (D+1); simp [xs_small]) ∧
    TreeDeleteCircuitZero Index.tail (by apply tail_index_in_range (D+1); simp [xs_small])

theorem after_deletion_all_zeroes [Fact (perfect_hash poseidon₂)] {b : Nat}
  (Tree₁ : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F b) (xs_small : are_indices_in_range (D+1) DeletionIndices) :
  TreeDeleteCircuit Tree₁ DeletionIndices xs_small k →
  TreeDeleteCircuitZero DeletionIndices xs_small := by
  induction b generalizing Tree₁ with
  | zero =>
    simp [TreeDeleteCircuit, TreeDeleteCircuitZero]
  | succ _ ih =>
    dsimp [TreeDeleteCircuit]
    rintro ⟨tree₂, htree₂, htree⟩
    simp [TreeDeleteCircuitZero]
    refine ⟨?_, ?_⟩
    . refine ⟨tree₂, ?_⟩
      apply deletion_round_set_zero Tree₁
      simp [htree₂]
    . apply ih tree₂
      simp [htree]

def DeletionLoopTree [Fact (perfect_hash poseidon₂)] {b : Nat}
  (InitialTree : MerkleTree F poseidon₂ D) (Index : Vector F b) (xs_small : are_indices_in_range (D+1) Index) (k : MerkleTree F poseidon₂ D → Prop) : Prop :=
  match b with
  | Nat.zero => k InitialTree
  | Nat.succ _ =>
    let idx := Index.head
    ∃t : MerkleTree F poseidon₂ D,
    deletion_round_prep InitialTree.root idx (MerkleTree.tree_item_at_fin InitialTree idx.val) (MerkleTree.tree_proof_at_fin InitialTree idx.val).reverse (fun nextRoot => t.root = nextRoot) ∧
      DeletionLoopTree t Index.tail (by apply tail_index_in_range (D+1); simp [xs_small]) k

theorem deletion_loop_uncps [Fact (perfect_hash poseidon₂)] {b : Nat}
  (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F b) (xs_small : are_indices_in_range (D+1) DeletionIndices) :
  TreeDeleteCircuit Tree DeletionIndices xs_small k ↔
  DeletionLoopTree Tree DeletionIndices xs_small k := by
  induction b generalizing Tree with
  | zero =>
    simp [TreeDeleteCircuit, DeletionLoopTree]
  | succ _ ih =>
    simp only [TreeDeleteCircuit, DeletionLoopTree]
    apply Iff.intro
    . rintro ⟨tree, htree, hroot⟩
      refine ⟨tree, ?_, ?_⟩
      rw [deletion_round_prep_uncps]
      . rw [htree]
      . rw [<-ih]
        simp [hroot]
    . rintro ⟨tree, htree, hroot⟩
      refine ⟨tree, ?_⟩
      rw [deletion_round_prep_uncps] at htree
      . apply And.intro
        . rw [<-eq_root_eq_tree]
          apply Eq.symm
          rw [htree]
        . rw [ih]
          simp [hroot]

def list_of_items {b : Nat} [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F b) (xs_small : are_indices_in_range (D+1) DeletionIndices) : Vector F b :=
  match b with
  | Nat.zero => Vector.nil
  | Nat.succ _ =>
    let t := TreeDeletePrep Tree DeletionIndices.head (by
      apply head_index_in_range
      simp [xs_small])
    let item_at := (MerkleTree.tree_item_at_fin Tree DeletionIndices.head.val)
    let tail := (list_of_items t DeletionIndices.tail (by
      apply tail_index_in_range
      simp [xs_small]))
    item_at ::ᵥ tail

@[simp]
lemma list_of_items_tail {b : Nat} [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F (b+1)) (xs_small : are_indices_in_range (D+1) DeletionIndices) :
  Vector.tail (list_of_items Tree DeletionIndices xs_small) =
  let t := TreeDeletePrep Tree DeletionIndices.head (by
      apply head_index_in_range
      simp [xs_small])
  list_of_items t DeletionIndices.tail (by
  simp [are_indices_in_range_split] at xs_small; tauto) := by
  simp [list_of_items]

def list_of_proofs {b : Nat} [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F b) (xs_small : are_indices_in_range (D+1) DeletionIndices) : Vector (Vector F D) b :=
  match b with
  | Nat.zero => Vector.nil
  | Nat.succ _ =>
    let t := TreeDeletePrep Tree DeletionIndices.head (by
      apply head_index_in_range
      simp [xs_small])
    let proof := (MerkleTree.tree_proof_at_fin Tree DeletionIndices.head.val).reverse
    let tail := (list_of_proofs t DeletionIndices.tail (by
      apply tail_index_in_range
      simp [xs_small]))
    proof ::ᵥ tail

@[simp]
lemma list_of_proofs_tail {b : Nat} [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F (b+1)) (xs_small : are_indices_in_range (D+1) DeletionIndices) :
  Vector.tail (list_of_proofs Tree DeletionIndices xs_small) =
  let t := TreeDeletePrep Tree DeletionIndices.head (by
      apply head_index_in_range
      simp [xs_small])
  list_of_proofs t DeletionIndices.tail (by
  simp [are_indices_in_range_split] at xs_small; tauto) := by
  simp [list_of_proofs]

theorem deletion_loop_equivalence [Fact (perfect_hash poseidon₂)] {b : Nat}
  (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F b) (xs_small : are_indices_in_range (D+1) DeletionIndices) (k : F -> Prop) :
  DeletionLoopTree Tree DeletionIndices xs_small (fun newTree => k newTree.root) ↔
  let items := (list_of_items Tree DeletionIndices xs_small)
  let proofs := (list_of_proofs Tree DeletionIndices xs_small)
  DeletionLoop DeletionIndices Tree.root items proofs k := by
  apply Iff.intro
  . induction b generalizing Tree with
    | zero =>
      simp [DeletionLoopTree, DeletionLoop]
    | succ _ ih =>
      simp only [DeletionLoopTree]
      rintro ⟨tree, htree⟩
      simp only [DeletionLoop]
      nth_rewrite 1 [list_of_items, list_of_proofs]
      simp only [Vector.head_cons]
      rw [deletion_round_prep_uncps]
      . rw [deletion_round_prep_uncps, eq_root_eq_tree] at htree
        cases htree
        rename_i htree hroot
        simp [list_of_items_tail, list_of_proofs_tail]
        apply ih
        rw [<-htree]
        . tauto
  . induction b generalizing Tree with
    | zero =>
      simp [DeletionLoopTree, DeletionLoop]
    | succ _ ih =>
      intro htree
      simp only [DeletionLoopTree]
      simp [DeletionLoop] at htree
      let t := TreeDeletePrep Tree DeletionIndices.head (by
        apply head_index_in_range
        simp [xs_small])
      refine ⟨t, ?_⟩
      nth_rewrite 1 [list_of_items, list_of_proofs] at htree
      simp only [Vector.head_cons] at htree
      rw [deletion_round_prep_uncps] at htree
      . rw [deletion_round_prep_uncps, eq_root_eq_tree]
        refine ⟨?_, ?_⟩
        . tauto
        . apply ih
          simp [htree]
      . rw [are_indices_in_range_split] at xs_small
        cases xs_small
        rename_i x xs
        simp [x]

theorem deletion_loop_equivalence' [Fact (perfect_hash poseidon₂)] {b : Nat}
  (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F b) (xs_small : are_indices_in_range (D+1) DeletionIndices) (k : F -> Prop) :
  TreeDeleteCircuit Tree DeletionIndices xs_small (fun newTree => k newTree.root) ↔
  let items := (list_of_items Tree DeletionIndices xs_small)
  let proofs := (list_of_proofs Tree DeletionIndices xs_small)
  DeletionLoop DeletionIndices Tree.root items proofs k := by
  rw [<-deletion_loop_equivalence]
  apply deletion_loop_uncps
