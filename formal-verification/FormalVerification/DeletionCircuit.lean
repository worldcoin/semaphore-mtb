import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Ext.Vector

import FormalVerification
import FormalVerification.Utils
import FormalVerification.SemanticEquivalence

open SemaphoreMTB (F Order)

open SemaphoreMTB renaming VerifyProof_31_30 → gVerifyProof
open SemaphoreMTB renaming DeletionRound_30_30 → gDeletionRound
open SemaphoreMTB renaming DeletionProof_4_4_30_4_4_30 → gDeletionProof

set_option pp.coercions false

---------- MISC

lemma vector_head_is_zero {d} (xs : Vector α (d+1)) :
  xs.head = xs[0] := by
  rw [←Vector.ofFn_get (v := xs)]
  rfl

lemma vector_cons_get {d b d : Nat} {x : α} {xs : Vector α d} {h : b < d}:
  ((x ::ᵥ xs)[Nat.succ b]'(by linarith)) = xs[b] := by
  rw [←Vector.ofFn_get (v := xs)]
  rfl

lemma cons_zero {y : α} :
  (y ::ᵥ Vector.nil)[0] = y := by
    rfl

----------

def TreeDelete [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Skip : Bit) (Path : Vector F D) : MerkleTree F poseidon₂ D :=
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
  deletion_round_prep Tree.root Index (MerkleTree.tree_item_at_fin_dropLast Tree Index.val) (MerkleTree.tree_proof_at_fin_dropLast Tree Index.val).reverse k ↔
  k (TreeDeletePrep Tree Index ix_small).root := by
  unfold deletion_round_prep
  apply Iff.intro
  . rintro ⟨ixbin, _⟩
    casesm* (_ ∧ _)
    rename_i h
    rw [MerkleTree.tree_item_at_fin_dropLast, MerkleTree.tree_proof_at_fin_dropLast] at h
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
    rw [MerkleTree.tree_item_at_fin_dropLast, MerkleTree.tree_proof_at_fin_dropLast]
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
  (Tree : MerkleTree F poseidon₂ D) (Index : F) (ix_small : is_index_in_range (D+1) Index) :
  TreeDeletePrep Tree Index ix_small = t →
  TreeDeleteZero t Index ix_small := by
  intro htree
  unfold TreeDeletePrep at htree
  unfold TreeDelete at htree
  simp [TreeDeleteZero]
  split
  . rename_i hskip
    simp [hskip] at htree
    apply MerkleTree.set_implies_item_at (t₁ := Tree)
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
  (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F b) (xs_small : are_indices_in_range (D+1) DeletionIndices) :
  TreeDeleteCircuit Tree DeletionIndices xs_small k →
  TreeDeleteCircuitZero DeletionIndices xs_small := by
  induction b generalizing Tree with
  | zero =>
    simp [TreeDeleteCircuit, TreeDeleteCircuitZero]
  | succ _ ih =>
    dsimp [TreeDeleteCircuit]
    rintro ⟨tree₂, htree₂, htree⟩
    simp [TreeDeleteCircuitZero]
    refine ⟨?_, ?_⟩
    . refine ⟨tree₂, ?_⟩
      apply deletion_round_set_zero Tree
      simp [htree₂]
    . apply ih tree₂
      simp [htree]

def DeletionLoopTree [Fact (perfect_hash poseidon₂)] {b : Nat}
  (Tree : MerkleTree F poseidon₂ D) (Index : Vector F b) (xs_small : are_indices_in_range (D+1) Index) (k : MerkleTree F poseidon₂ D → Prop) : Prop :=
  match b with
  | Nat.zero => k Tree
  | Nat.succ _ =>
    let idx := Index.head
    ∃t : MerkleTree F poseidon₂ D,
    deletion_round_prep Tree.root idx (MerkleTree.tree_item_at_fin_dropLast Tree idx.val) (MerkleTree.tree_proof_at_fin_dropLast Tree idx.val).reverse (fun nextRoot => t.root = nextRoot) ∧
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
        . rw [<-MerkleTree.eq_root_eq_tree]
          apply Eq.symm
          rw [htree]
        . rw [ih]
          simp [hroot]

def list_of_items_delete {b : Nat} [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F b) (xs_small : are_indices_in_range (D+1) DeletionIndices) : Vector F b :=
  match b with
  | Nat.zero => Vector.nil
  | Nat.succ _ =>
    let t := TreeDeletePrep Tree DeletionIndices.head (by
      apply head_index_in_range
      simp [xs_small])
    let item_at := (MerkleTree.tree_item_at_fin_dropLast Tree DeletionIndices.head.val)
    let tail := (list_of_items_delete t DeletionIndices.tail (by
      apply tail_index_in_range
      simp [xs_small]))
    item_at ::ᵥ tail

@[simp]
lemma list_of_items_delete_tail {b : Nat} [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F (b+1)) (xs_small : are_indices_in_range (D+1) DeletionIndices) :
  Vector.tail (list_of_items_delete Tree DeletionIndices xs_small) =
  let t := TreeDeletePrep Tree DeletionIndices.head (by
      apply head_index_in_range
      simp [xs_small])
  list_of_items_delete t DeletionIndices.tail (by
  simp [are_indices_in_range_split] at xs_small; tauto) := by
  simp [list_of_items_delete]

def list_of_proofs_delete {b : Nat} [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F b) (xs_small : are_indices_in_range (D+1) DeletionIndices) : Vector (Vector F D) b :=
  match b with
  | Nat.zero => Vector.nil
  | Nat.succ _ =>
    let t := TreeDeletePrep Tree DeletionIndices.head (by
      apply head_index_in_range
      simp [xs_small])
    let proof := (MerkleTree.tree_proof_at_fin_dropLast Tree DeletionIndices.head.val).reverse
    let tail := (list_of_proofs_delete t DeletionIndices.tail (by
      apply tail_index_in_range
      simp [xs_small]))
    proof ::ᵥ tail

@[simp]
lemma list_of_proofs_delete_tail {b : Nat} [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F (b+1)) (xs_small : are_indices_in_range (D+1) DeletionIndices) :
  Vector.tail (list_of_proofs_delete Tree DeletionIndices xs_small) =
  let t := TreeDeletePrep Tree DeletionIndices.head (by
      apply head_index_in_range
      simp [xs_small])
  list_of_proofs_delete t DeletionIndices.tail (by
  simp [are_indices_in_range_split] at xs_small; tauto) := by
  simp [list_of_proofs_delete]

theorem deletion_loop_equivalence [Fact (perfect_hash poseidon₂)] {b : Nat}
  (Tree : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F b) (xs_small : are_indices_in_range (D+1) DeletionIndices) (k : F -> Prop) :
  DeletionLoopTree Tree DeletionIndices xs_small (fun newTree => k newTree.root) ↔
  let items := (list_of_items_delete Tree DeletionIndices xs_small)
  let proofs := (list_of_proofs_delete Tree DeletionIndices xs_small)
  DeletionLoop DeletionIndices Tree.root items proofs k := by
  apply Iff.intro
  . induction b generalizing Tree with
    | zero =>
      simp [DeletionLoopTree, DeletionLoop]
    | succ _ ih =>
      simp only [DeletionLoopTree]
      rintro ⟨tree, htree⟩
      simp only [DeletionLoop]
      nth_rewrite 1 [list_of_items_delete, list_of_proofs_delete]
      simp only [Vector.head_cons]
      rw [deletion_round_prep_uncps]
      . rw [deletion_round_prep_uncps, MerkleTree.eq_root_eq_tree] at htree
        cases htree
        rename_i htree hroot
        simp [list_of_items_delete_tail, list_of_proofs_delete_tail]
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
      nth_rewrite 1 [list_of_items_delete, list_of_proofs_delete] at htree
      simp only [Vector.head_cons] at htree
      rw [deletion_round_prep_uncps] at htree
      . rw [deletion_round_prep_uncps, MerkleTree.eq_root_eq_tree]
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
  let items := (list_of_items_delete Tree DeletionIndices xs_small)
  let proofs := (list_of_proofs_delete Tree DeletionIndices xs_small)
  DeletionLoop DeletionIndices Tree.root items proofs k := by
  rw [<-deletion_loop_equivalence]
  apply deletion_loop_uncps

theorem chain_of_item_at [Fact (perfect_hash poseidon₂)] { depth : Nat } {F: Type} {H : Hash F 2}
  {initialTree finalTree : MerkleTree F H depth}
  {ix₁ ix₂ : Vector Dir depth} {neq : ix₁ ≠ ix₂}
  {item₁ item₂ : F}:
  (initialTree.set ix₁ item₁).set ix₂ item₂ = finalTree →
  finalTree.item_at ix₁ = item₁ ∧ finalTree.item_at ix₂ = item₂ := by
  intro h
  have : ∃t, MerkleTree.set initialTree ix₁ item₁ = t := by
    simp [h]
  rcases this with ⟨tdelete, hdelete⟩
  rw [hdelete] at h
  refine ⟨?_, ?_⟩
  . rw [<-h]
    rw [MerkleTree.item_at_invariant]
    . rw [<-hdelete]
      rw [MerkleTree.read_after_insert_sound]
    . tauto
  . rw [<-h]
    rw [MerkleTree.read_after_insert_sound]

theorem chain_of_set [Fact (perfect_hash poseidon₂)] { depth : Nat } {F: Type} {H : Hash F 2}
  {initialTree : MerkleTree F H depth}
  {ix₁ ix₂ : Vector Dir depth}
  {item : F}:
  ((initialTree.set ix₁ item).set ix₂ item).item_at ix₁ = item := by
  if h : ix₁ = ix₂ then
    rw [h]
    apply MerkleTree.read_after_insert_sound
  else
    rw [MerkleTree.item_at_invariant]
    . rw [MerkleTree.read_after_insert_sound]
    . tauto

theorem chain_of_item_at_same [Fact (perfect_hash poseidon₂)] { depth : Nat } {F: Type} {H : Hash F 2}
  {initialTree finalTree : MerkleTree F H depth}
  {ix₁ ix₂ : Vector Dir depth}
  {item : F}:
  (initialTree.set ix₁ item).set ix₂ item = finalTree →
  finalTree.item_at ix₁ = item ∧ finalTree.item_at ix₂ = item := by
  intro h
  have : ∃t, MerkleTree.set initialTree ix₁ item = t := by
    simp [h]
  rcases this with ⟨tdelete, hdelete⟩
  rw [hdelete] at h
  refine ⟨?_, ?_⟩
  . rw [<-h]
    rw [<-hdelete]
    rw [chain_of_set]
  . rw [<-h]
    rw [MerkleTree.read_after_insert_sound]

theorem chain_of_deletions [Fact (perfect_hash poseidon₂)] {initialTree finalTree : MerkleTree F poseidon₂ D} {ix₁ ix₂ : F}
  {ix_small₁ : is_index_in_range (D+1) ix₁} {ix_small₂ : is_index_in_range (D+1) ix₂}:
  TreeDeletePrep (TreeDeletePrep initialTree ix₁ ix_small₁) ix₂ ix_small₂ = finalTree →
  TreeDeleteZero finalTree ix₁ ix_small₁ ∧ TreeDeleteZero finalTree ix₂ ix_small₂ := by
  intro h
  have : ∃t, TreeDeletePrep initialTree ix₁ ix_small₁ = t := by
    simp [h]
  rcases this with ⟨tdelete, hdelete⟩
  rw [hdelete] at h
  refine ⟨?_, ?_⟩
  . simp [TreeDeleteZero]
    split
    . rename_i hbit
      simp [TreeDeletePrep, TreeDelete] at h
      simp [TreeDeletePrep, TreeDelete, hbit] at hdelete
      cases h
      split
      . rw [<-hdelete]
        rw [chain_of_set]
      . rw [<-hdelete]
        rw [MerkleTree.read_after_insert_sound]
    . simp
  . simp [TreeDeleteZero]
    split
    . rename_i hbit
      simp [TreeDeletePrep, TreeDelete] at h
      simp [hbit] at h
      rw [<-h]
      rw [MerkleTree.read_after_insert_sound]
    . simp

theorem chain_of_deletions_left [Fact (perfect_hash poseidon₂)] {initialTree finalTree : MerkleTree F poseidon₂ D} {ix₁ ix₂ : F}
  {ix_small₁ : is_index_in_range (D+1) ix₁} {ix_small₂ : is_index_in_range (D+1) ix₂}:
  TreeDeletePrep (TreeDeletePrep initialTree ix₁ ix_small₁) ix₂ ix_small₂ = finalTree →
  TreeDeleteZero finalTree ix₁ ix_small₁ := by
  intro h
  have : ∃t, TreeDeletePrep initialTree ix₁ ix_small₁ = t := by
    simp [h]
  rcases this with ⟨tdelete, hdelete⟩
  rw [hdelete] at h
  . simp [TreeDeleteZero]
    split
    . rename_i hbit
      simp [TreeDeletePrep, TreeDelete] at h
      simp [TreeDeletePrep, TreeDelete, hbit] at hdelete
      cases h
      split
      . rw [<-hdelete]
        rw [chain_of_set]
      . rw [<-hdelete]
        rw [MerkleTree.read_after_insert_sound]
    . simp

theorem chain_of_deletions_right [Fact (perfect_hash poseidon₂)] {initialTree finalTree : MerkleTree F poseidon₂ D} {ix₁ ix₂ : F}
  {ix_small₁ : is_index_in_range (D+1) ix₁} {ix_small₂ : is_index_in_range (D+1) ix₂}:
  TreeDeletePrep (TreeDeletePrep initialTree ix₁ ix_small₁) ix₂ ix_small₂ = finalTree →
  TreeDeleteZero finalTree ix₂ ix_small₂ := by
  intro h
  have : ∃t, TreeDeletePrep initialTree ix₁ ix_small₁ = t := by
    simp [h]
  rcases this with ⟨tdelete, hdelete⟩
  rw [hdelete] at h
  . simp [TreeDeleteZero]
    split
    . rename_i hbit
      simp [TreeDeletePrep, TreeDelete] at h
      simp [hbit] at h
      rw [<-h]
      rw [MerkleTree.read_after_insert_sound]
    . simp

def multi_set { depth b : Nat } {F: Type} {H : Hash F 2} (tree : MerkleTree F H depth) (path : Vector (Vector Dir depth) b) (item : F) : MerkleTree F H depth :=
  match b with
  | Nat.zero => tree
  | Nat.succ _ => multi_set (tree.set path.head item) path.tail item

lemma tree_set_comm  { depth : Nat } {F: Type} {H : Hash F 2} {tree : MerkleTree F H depth} {p₁ p₂ : Vector Dir depth} {item : F}:
  MerkleTree.set (MerkleTree.set tree p₁ item) p₂ item = MerkleTree.set (MerkleTree.set tree p₂ item) p₁ item := by
  induction depth with
  | zero => rfl
  | succ d ih => cases tree with | bin l r =>
    cases p₁ using Vector.casesOn with | cons p₁h p₁t =>
    cases p₂ using Vector.casesOn with | cons p₂h p₂t =>
    cases p₁h <;> {
      cases p₂h <;> { simp [MerkleTree.set, MerkleTree.left, MerkleTree.right]; try rw [ih] }
    }

lemma multi_set_set { depth b : Nat } {F: Type} {H : Hash F 2} {tree : MerkleTree F H depth} {p : Vector Dir depth} {path : Vector (Vector Dir depth) b} {item : F}:
  multi_set (MerkleTree.set tree p item) path item = MerkleTree.set (multi_set tree path item) p item := by
  induction path using Vector.inductionOn generalizing tree p with
  | h_nil => rfl
  | h_cons ih => simp [multi_set, ih, tree_set_comm]

def multi_item_at { depth b : Nat } {F: Type} {H : Hash F 2} (tree : MerkleTree F H depth) (path : Vector (Vector Dir depth) b) (item : F) : Prop :=
  match b with
  | Nat.zero => true
  | Nat.succ _ => tree.item_at path.head = item ∧ multi_item_at tree path.tail item

theorem multi_set_is_item_at { depth b : Nat } {F: Type} {H : Hash F 2} {initialTree finalTree: MerkleTree F H depth} {path : Vector (Vector Dir depth) b} {item : F} :
  (multi_set initialTree path item = finalTree →
  multi_item_at finalTree path item) := by
  induction path using Vector.inductionOn generalizing initialTree finalTree with
  | h_nil =>
    simp [multi_set, multi_item_at]
  | @h_cons b' x xs ih =>
    unfold multi_set
    unfold multi_item_at
    simp only [Vector.tail_cons, Vector.head_cons]
    intro h
    refine ⟨?_, ?_⟩
    . rw [←h, multi_set_set, MerkleTree.read_after_insert_sound]
    . apply ih h

theorem multi_set_is_item_at_all_item { depth b i : Nat } {range : i ∈ [0:b]} {F: Type} {H : Hash F 2}
  {initialTree finalTree: MerkleTree F H depth} {path : Vector (Vector Dir depth) b} {item : F} :
  multi_set initialTree path item = finalTree →
  MerkleTree.item_at finalTree (path[i]'(by rcases range; tauto)) = item := by
  intro hp

  induction path using Vector.inductionOn generalizing initialTree finalTree with
  | h_nil =>
    rcases range with ⟨lo, hi⟩
    have := Nat.ne_of_lt (Nat.lt_of_le_of_lt lo hi)
    contradiction
  | @h_cons b' x xs ih =>
    rcases range with ⟨lo, hi⟩;
    cases lo with
    | refl =>
      simp [<-vector_head_is_zero]
      have hitem_at : multi_item_at finalTree (x ::ᵥ xs) item := by
        apply multi_set_is_item_at (initialTree := initialTree)
        simp [hp]
      simp at ih
      simp [multi_item_at] at hitem_at
      tauto
    | @step i ih =>
      rename_i h
      simp at ih
      simp [multi_set] at hp

      sorry


-- theorem after_deletion_all_zeroes_batch [Fact (perfect_hash poseidon₂)] {b i : Nat} {range : i ∈ [0:b]}
--   {Tree t : MerkleTree F poseidon₂ D} {DeletionIndices : Vector F b} {xs_small : are_indices_in_range (D+1) DeletionIndices} :
--   TreeDeleteCircuit Tree DeletionIndices xs_small (fun nextTree => t = nextTree) →
--   TreeDeleteZero t (DeletionIndices[i]'(by rcases range; simp_arith; linarith)) (by admit) := by
--   induction b generalizing Tree t with
--   | zero =>
--     rcases range with ⟨lo, hi⟩
--     have := Nat.ne_of_lt (Nat.lt_of_le_of_lt lo hi)
--     contradiction
--   | succ b ih =>
--     rcases range with ⟨lo, hi⟩; --simp at lo hi
--     cases lo with
--     | refl =>
--       simp [<-vector_head_is_zero, TreeDeleteCircuit]
--       --intro hp
--       --simp at ih
--       --apply chain_of_deletions_left (initialTree := Tree) (finalTree := t) --(ix₂ := DeletionIndices.tail.head) (ix_small₂ := by simp [are_indices_in_range_split] at xs_small; tauto)
--       sorry
--     | @step StartIndex' h =>
--       sorry
