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

-- lemma chain_of_set {F depth}
--   (H : Hash F 2)
--   [Fact (perfect_hash H)]
--   (tree₁ tree₂ tree₃: MerkleTree F H depth)
--   (path₁ path₂ : Vector Dir depth)
--   (item₁ item₂ : F):
--   let tree₂ := MerkleTree.set tree₁ path₁ item₁;
--   let tree₃ := MerkleTree.set tree₂ path₂ item₂;
--   MerkleTree.item_at tree₃ path₁ = item₁ := by
--   sorry

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
  (InitialTree FinalTree : MerkleTree F poseidon₂ D) (Index : Vector F b) (xs_small : are_indices_in_range (D+1) Index) : Prop :=
  match b with
  | Nat.zero => InitialTree = FinalTree
  | Nat.succ _ =>
    ∃newTree, TreeDeletePrep InitialTree Index.head (by apply head_index_in_range (D+1); simp [xs_small]) = newTree ∧
    TreeDeleteCircuit newTree FinalTree Index.tail (by apply tail_index_in_range (D+1); simp [xs_small])

def TreeDeleteCircuitZero [Fact (perfect_hash poseidon₂)] {b : Nat}
  (Index : Vector F b) (xs_small : are_indices_in_range (D+1) Index) : Prop :=
  match b with
  | Nat.zero => True
  | Nat.succ _ =>
    ∃t, TreeDeleteZero t Index.head (by apply head_index_in_range (D+1); simp [xs_small]) ∧
    TreeDeleteCircuitZero Index.tail (by apply tail_index_in_range (D+1); simp [xs_small])

theorem after_deletion_all_zeroes [Fact (perfect_hash poseidon₂)]
  (Tree₁ Tree₂ : MerkleTree F poseidon₂ D) (DeletionIndices : Vector F B) (xs_small : are_indices_in_range (D+1) DeletionIndices) :
  TreeDeleteCircuit Tree₁ Tree₂ DeletionIndices xs_small →
  TreeDeleteCircuitZero DeletionIndices xs_small := by
  dsimp [TreeDeleteCircuit]
  rintro ⟨newTree⟩
  rename_i htree₁
  cases htree₁
  rename_i htree₁ htree₂
  cases htree₂
  rename_i newTree₂ htree₃
  cases htree₃
  rename_i htree₃ htree₄
  cases htree₄
  rename_i newTree₄ htree₅
  cases htree₅
  rename_i htree₅ htree₆
  cases htree₆
  rename_i newTree₆ htree₇
  cases htree₇
  rename_i htree₇ htree

  simp [TreeDeleteCircuitZero]
  refine ⟨?_, ?_, ?_, ?_⟩
  . let t := newTree
    refine ⟨t, ?_⟩
    apply deletion_round_set_zero Tree₁
    simp [htree₁]
  . let t := newTree₂
    refine ⟨t, ?_⟩
    apply deletion_round_set_zero newTree
    simp [htree₃]
  . let t := newTree₄
    refine ⟨t, ?_⟩
    apply deletion_round_set_zero newTree₂
    simp [htree₅]
  . let t := newTree₆
    refine ⟨t, ?_⟩
    apply deletion_round_set_zero newTree₄
    simp [htree₇]




/-
let Tree₂ := Merkle.set Tree₁ ix₁ (0:F)
Merkle.set Tree₂ ix₂ (0:F) →
Merkle.item_at Tree₂ ix₁ = (0:F)
-/

--   deletion_round_prep Tree.root Index Item Proof k ↔
--   TreeDeletePrep Tree Index Item Proof k := by
--   unfold deletion_round_prep
--   unfold TreeDeletePrep
--   simp [deletion_round_uncps]
--   apply Iff.intro
--   . rintro ⟨ixbin, _⟩
--     casesm* (_ ∧ _)
--     have : nat_to_bits_le (D+1) Index.val = some (vector_zmod_to_bit ixbin) := by
--       apply recover_binary_zmod'_to_bits_le
--       . simp
--       . assumption
--       . rename_i h _ _ _; simp[h]
--     rw [this]
--     simp [←Dir.create_dir_vec_bit]
--     simp [vector_zmod_to_bit_last]
--     rw [vector_zmod_to_bit_dropLast]
--     assumption
--     assumption
--   . rintro ⟨ixbin, h⟩
--     casesm* (_ ∧ _)
--     rename_i l r
--     let t : Vector F (D+1) := (Vector.map Bit.toZMod ixbin)
--     refine ⟨t, ?_⟩
--     refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
--     . apply recover_binary_of_to_bits
--       simp [l]
--     . apply vector_binary_of_bit_to_zmod
--     . simp [Bit.toZMod, is_bit, Vector.last]
--       split
--       simp
--       simp
--     . simp
--       simp [dropLast_symm] at r
--       have : (Vector.last ixbin) = zmod_to_bit (Vector.last (Vector.map (fun i => @Bit.toZMod Order i) ixbin)) := by
--         rw [<-vector_zmod_to_bit_last]
--         simp [vector_bit_to_zmod_to_bit]
--       rw [<-this]
--       assumption

-- theorem after_deletion_item_zero_recover
--   [Fact (perfect_hash poseidon₂)]
--   {Tree: MerkleTree F poseidon₂ D}
--   {DeletionIndex: F}
--   {Item: F}
--   {MerkleProof: Vector F D}
--   -- {postRoot : F }
--   {k : F → Prop} :
--   (deletion_round_prep Tree.root DeletionIndex Item MerkleProof k) →
--   ∃path, nat_to_bits_le (D+1) DeletionIndex.val = some path ∧
--   match path.last with
--   | Bit.zero => k (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec (Vector.map (fun ix => @Bit.toZMod Order ix) path.dropLast)) MerkleProof (0:F))
--   | Bit.one => True := by
--   simp [deletion_round_prep_uncps]
--   simp only [TreeDeletePrep, TreeDelete]
--   rintro ⟨ixbin, _⟩
--   casesm* (_ ∧ _)
--   rename_i l r
--   let t : Vector Bit (D+1) := (ixbin)
--   refine ⟨t, ?_⟩
--   simp
--   split
--   . apply And.intro
--     . simp [l]
--     . rename_i hbit
--       simp [hbit] at r
--       casesm* (_ ∧ _)
--       rename_i hitem_at hproof hroot
--       rw [MerkleTree.recover_tail_equals_recover_reverse]
--       rw [MerkleTree.proof_insert_invariant (tree := Tree) (old := (Item)) (new := (0:F))]
--       simp
--       simp [hroot]
--       rw [<-MerkleTree.recover_equivalence]
--       apply And.intro
--       simp [hitem_at]
--       simp [hproof]
--   . apply And.intro
--     . simp [l]
--     . simp

-- theorem after_deletion_item_zero_loop
--   [Fact (perfect_hash poseidon₂)]
--   {Tree: MerkleTree F poseidon₂ D}
--   {DeletionIndex: F}
--   {Item: F}
--   {MerkleProof: Vector F D}
--   {postRoot : F } :
--   (deletion_round_prep Tree.root DeletionIndex Item MerkleProof fun newRoot => newRoot = postRoot) →
--   ∃path, nat_to_bits_le (D+1) DeletionIndex.val = some path ∧
--   match path.last with
--   | Bit.zero => (MerkleTree.set Tree (Dir.create_dir_vec (Vector.map (fun ix => @Bit.toZMod Order ix) path.dropLast)).reverse (0:F)).item_at (Dir.create_dir_vec (Vector.map (fun ix => @Bit.toZMod Order ix) path.dropLast)).reverse = (0:F)
--   | Bit.one => True := by
--   simp [deletion_round_prep_uncps]
--   simp only [TreeDeletePrep, TreeDelete]
--   rintro ⟨ixbin, _⟩
--   casesm* (_ ∧ _)
--   rename_i l r
--   let t : Vector Bit (D+1) := (ixbin)
--   refine ⟨t, ?_⟩
--   simp
--   split
--   . let ix := (Vector.reverse (Dir.create_dir_vec (Vector.map (fun ix => @Bit.toZMod Order ix) (Vector.dropLast ixbin))))
--     let t := MerkleTree.set Tree ix (0:F)
--     rw [MerkleTree.proof_ceritfies_item (ix := ix) (tree := t) (proof := MerkleProof.reverse) (item := (0:F))]
--     simp
--     assumption
--     simp
--     rename_i hbit
--     simp [hbit] at r
--     casesm* (_ ∧ _)
--     rename_i hitem_at hproof hroot
--     simp [hroot]
--     rw [MerkleTree.proof_insert_invariant (tree := Tree) (old := (Item)) (new := (0:F))]
--     assumption
--     rw [<-MerkleTree.recover_equivalence]
--     apply And.intro
--     simp [hitem_at]
--     simp [hproof]
--   . apply And.intro
--     . simp [l]
--     . simp

-- def TreeDeleteT [Fact (perfect_hash poseidon₂)]
--   (Tree : MerkleTree F poseidon₂ D) (Skip : Bit) (Path : Vector F D) (Item : F) (k : (MerkleTree F poseidon₂ D) → Prop) : Prop :=
--   match Skip with
--   | Bit.zero =>
--       MerkleTree.item_at Tree (Dir.create_dir_vec Path).reverse = Item ∧
--       k (MerkleTree.set Tree (Dir.create_dir_vec Path).reverse 0)
--   | Bit.one => k Tree

-- -- def TreeDeleteT'
-- --   (Tree : MerkleTree F poseidon₂ D) (Skip : Bit) (Path : Vector F D) (Item : F) (Proof : Vector F D): Option (MerkleTree F poseidon₂ D) :=
-- --   match Skip with
-- --   | Bit.zero =>
-- --       let path := (Dir.create_dir_vec Path).reverse
-- --       if MerkleTree.item_at Tree path = Item then
-- --         if MerkleTree.proof Tree path = Proof.reverse then
-- --           some (MerkleTree.set Tree path 0)
-- --       else
-- --         none


-- def TreeDeletePrepT [Fact (perfect_hash poseidon₂)]
--   (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (k : (MerkleTree F poseidon₂ D) → Prop) : Prop :=
--   ∃path, nat_to_bits_le (D+1) Index.val = some path ∧
--   TreeDeleteT Tree (path.last) (Vector.map Bit.toZMod path.dropLast) Item k

-- theorem TreeDelete_equivalence [Fact (perfect_hash poseidon₂)]
--   (Tree : MerkleTree F poseidon₂ D) (Skip : Bit) (Path : Vector F D) (Item : F) (Proof : Vector F D) (k : F → Prop) :
--   TreeDelete Tree Skip Path Item Proof k ↔
--   TreeDeleteT Tree Skip Path Item (fun t => k t.root) := by
--   simp [TreeDelete, TreeDeleteT]

-- theorem TreeDeletePrepT_equivalence [Fact (perfect_hash poseidon₂)]
--   (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (Proof : Vector F D) (k : F → Prop) :
--   TreeDeletePrep Tree Index Item Proof k ↔
--   TreeDeletePrepT Tree Index Item Proof (fun t => k t.root) := by
--   simp [TreeDeletePrep, TreeDeletePrepT]
--   simp [TreeDelete_equivalence]

-- def deletion_circuit [Fact (perfect_hash poseidon₂)] {b : Nat}
--   (Tree : MerkleTree F poseidon₂ D) (Indices: Vector F b) (IdComms: Vector F b) (Proofs: Vector (Vector F D) b) (k : (MerkleTree F poseidon₂ D) → Prop) : Prop :=
--   match b with
--   | Nat.zero => k Tree
--   | Nat.succ _ => TreeDeletePrepT Tree Indices.head IdComms.head Proofs.head fun next =>
--                   deletion_circuit next Indices.tail IdComms.tail Proofs.tail k

-- theorem deletion_round_equivalence [Fact (perfect_hash poseidon₂)]
--   (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (Proof : Vector F D) (k : F → Prop) :
--   TreeDeletePrepT Tree Index Item Proof (fun t => k t.root) ↔
--   DeletionRound Index Tree.root Item Proof k := by
--   rw [<-TreeDeletePrepT_equivalence]
--   rw [<-deletion_round_prep_uncps]
--   simp [deletion_round_prep, deletion_round]
--   simp [DeletionRound]
--   simp [Dir.dropLastOrder]

-- theorem deletion_circuit_equivalence [Fact (perfect_hash poseidon₂)] {b : Nat}
--   (Tree : MerkleTree F poseidon₂ D) (Indices: Vector F b) (IdComms: Vector F b) (Proofs: Vector (Vector F D) b) (k : F → Prop) :
--   deletion_circuit Tree Indices IdComms Proofs (fun t => k t.root) ↔
--   DeletionLoop Indices Tree.root IdComms Proofs k := by
--   induction b generalizing Tree with
--   | zero =>
--     simp [deletion_circuit, DeletionLoop]
--   | succ _ ih =>
--     simp [deletion_circuit]
--     simp [DeletionLoop]
--     rw [<-deletion_round_equivalence]
--     simp [ih]

-- theorem after_deletion_round_item_zero
--   [Fact (perfect_hash poseidon₂)]
--   {OldTree NewTree: MerkleTree F poseidon₂ D}
--   {Index: F}
--   {Item: F}
--   {Proof: Vector F D}
--   :
--   (TreeDeletePrepT OldTree Index Item Proof fun newTree => newTree = NewTree) →
--   ∃path, nat_to_bits_le (D+1) Index.val = some path ∧
--   match path.last with
--   | Bit.zero =>
--     let ix := Dir.create_dir_vec (Vector.map (fun ix => @Bit.toZMod Order ix) path.dropLast)
--     MerkleTree.item_at NewTree ix.reverse = (0:F)
--   | Bit.one => True := by
--   simp [TreeDeletePrepT]
--   intros
--   rename_i ixbin l r
--   refine ⟨ixbin, ?_⟩
--   apply And.intro
--   simp [l]
--   simp [TreeDeleteT] at r
--   split
--   rename_i hskip
--   . simp [hskip] at r
--     casesm* (_ ∧ _)
--     rename_i hroot
--     apply MerkleTree.set_implies_item_at (t₁ := OldTree)
--     simp [hroot]
--   . simp

-- theorem after_deletion_all_items_zero_loop
--   [Fact (perfect_hash poseidon₂)]
--   {B : Nat}
--   {h : i ∈ [0:B]}
--   {OldTree: MerkleTree F poseidon₂ D}
--   --{NewTree: MerkleTree F poseidon₂ D}
--   {DeletionIndices: Vector F B}
--   {IdComms: Vector F B}
--   {MerkleProofs: Vector (Vector F D) B}
--   --{postRoot : F}
--   :
--   --(deletion_circuit OldTree DeletionIndices IdComms MerkleProofs fun t => t = NewTree) →
--   (deletion_circuit OldTree DeletionIndices IdComms MerkleProofs fun t =>
--   ∃path, nat_to_bits_le (D+1) (DeletionIndices[i]'(by rcases h; simp_arith; linarith)).val = some path ∧
--   match path.last with
--   | Bit.zero =>
--     let ix := Dir.create_dir_vec (Vector.map (fun ix => @Bit.toZMod Order ix) path.dropLast)
--     MerkleTree.item_at t ix.reverse = (0:F)
--   | Bit.one => True) := by
--     simp
--     induction B generalizing OldTree with
--     | zero =>
--       rcases h with ⟨lo, hi⟩
--       have := Nat.ne_of_lt (Nat.lt_of_le_of_lt lo hi)
--       contradiction
--     | succ B ih =>
--       rcases h with ⟨lo, hi⟩; --simp at lo hi
--       cases lo with
--       | refl =>
--         simp [deletion_circuit]
--         simp at ih
--         sorry
--       | @step i' hstep =>
--         sorry
