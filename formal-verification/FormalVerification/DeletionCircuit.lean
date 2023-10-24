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

def TreeDelete [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Skip : Bit) (Path : Vector F D) (Item : F) (Proof : Vector F D) (k : F → Prop): Prop :=
  match Skip with
  | Bit.zero =>
      MerkleTree.item_at Tree (Dir.create_dir_vec Path).reverse = Item ∧
      MerkleTree.proof Tree (Dir.create_dir_vec Path).reverse = Proof.reverse ∧
      k (MerkleTree.set Tree (Dir.create_dir_vec Path).reverse 0).root
  | Bit.one => k Tree.root

def TreeDeletePrep [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (Proof : Vector F D) (k : F → Prop): Prop :=
  ∃path, nat_to_bits_le (D+1) Index.val = some path ∧
  TreeDelete Tree (path.last) (Vector.map Bit.toZMod path.dropLast) Item Proof k

theorem deletion_round_uncps [Fact (perfect_hash poseidon₂)] (Tree : MerkleTree F poseidon₂ D) (Skip : Bit) (Path : Vector F D) (Item: F) (Proof : Vector F D) (k : F → Prop):
  deletion_round Tree.root Skip Path Item Proof k ↔
  TreeDelete Tree Skip Path Item Proof k := by
  unfold deletion_round
  unfold TreeDelete
  split
  . simp
    simp [MerkleTree.recover_tail_equals_recover_reverse]
    rw [<-MerkleTree.recover_equivalence]
    simp [and_assoc]
    intro hitem_at hproof
    rw [MerkleTree.proof_insert_invariant (ix := (Vector.reverse (Dir.create_dir_vec Path))) (tree := Tree) (old := Item) (new := (0:F)) (proof := Vector.reverse Proof)]
    rw [<-MerkleTree.recover_equivalence]
    apply And.intro
    rw [hitem_at]
    rw [hproof]
  . simp

theorem deletion_round_prep_uncps [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (Proof : Vector F D) (k : F → Prop) :
  deletion_round_prep Tree.root Index Item Proof k ↔
  TreeDeletePrep Tree Index Item Proof k := by
  unfold deletion_round_prep
  unfold TreeDeletePrep
  simp [deletion_round_uncps]
  apply Iff.intro
  . rintro ⟨ixbin, _⟩
    casesm* (_ ∧ _)
    have : nat_to_bits_le (D+1) Index.val = some (vector_zmod_to_bit ixbin) := by
      apply recover_binary_zmod'_to_bits_le
      . simp
      . assumption
      . rename_i h _ _ _; simp[h]
    rw [this]
    simp [←Dir.create_dir_vec_bit]
    simp [vector_zmod_to_bit_last]
    rw [vector_zmod_to_bit_dropLast]
    assumption
    assumption
  . rintro ⟨ixbin, h⟩
    casesm* (_ ∧ _)
    rename_i l r
    let t : Vector F (D+1) := (Vector.map Bit.toZMod ixbin)
    refine ⟨t, ?_⟩
    refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
    . apply recover_binary_of_to_bits
      simp [l]
    . apply vector_binary_of_bit_to_zmod
    . simp [Bit.toZMod, is_bit, Vector.last]
      split
      simp
      simp
    . simp
      simp [dropLast_symm] at r
      have : (Vector.last ixbin) = zmod_to_bit (Vector.last (Vector.map (fun i => @Bit.toZMod Order i) ixbin)) := by
        rw [<-vector_zmod_to_bit_last]
        simp [vector_bit_to_zmod_to_bit]
      rw [<-this]
      assumption

theorem after_deletion_item_zero_recover
  [Fact (perfect_hash poseidon₂)]
  {Tree: MerkleTree F poseidon₂ D}
  {DeletionIndex: F}
  {Item: F}
  {MerkleProof: Vector F D}
  -- {postRoot : F }
  {k : F → Prop} :
  (deletion_round_prep Tree.root DeletionIndex Item MerkleProof k) →
  ∃path, nat_to_bits_le (D+1) DeletionIndex.val = some path ∧
  match path.last with
  | Bit.zero => k (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec (Vector.map (fun ix => @Bit.toZMod Order ix) path.dropLast)) MerkleProof (0:F))
  | Bit.one => True := by
  simp [deletion_round_prep_uncps]
  simp only [TreeDeletePrep, TreeDelete]
  rintro ⟨ixbin, _⟩
  casesm* (_ ∧ _)
  rename_i l r
  let t : Vector Bit (D+1) := (ixbin)
  refine ⟨t, ?_⟩
  simp
  split
  . apply And.intro
    . simp [l]
    . rename_i hbit
      simp [hbit] at r
      casesm* (_ ∧ _)
      rename_i hitem_at hproof hroot
      rw [MerkleTree.recover_tail_equals_recover_reverse]
      rw [MerkleTree.proof_insert_invariant (tree := Tree) (old := (Item)) (new := (0:F))]
      simp
      simp [hroot]
      rw [<-MerkleTree.recover_equivalence]
      apply And.intro
      simp [hitem_at]
      simp [hproof]
  . apply And.intro
    . simp [l]
    . simp

theorem after_deletion_item_zero_loop
  [Fact (perfect_hash poseidon₂)]
  {Tree: MerkleTree F poseidon₂ D}
  {DeletionIndex: F}
  {Item: F}
  {MerkleProof: Vector F D}
  {postRoot : F } :
  (deletion_round_prep Tree.root DeletionIndex Item MerkleProof fun newRoot => newRoot = postRoot) →
  ∃path, nat_to_bits_le (D+1) DeletionIndex.val = some path ∧
  match path.last with
  | Bit.zero => (MerkleTree.set Tree (Dir.create_dir_vec (Vector.map (fun ix => @Bit.toZMod Order ix) path.dropLast)).reverse (0:F)).item_at (Dir.create_dir_vec (Vector.map (fun ix => @Bit.toZMod Order ix) path.dropLast)).reverse = (0:F)
  | Bit.one => True := by
  simp [deletion_round_prep_uncps]
  simp only [TreeDeletePrep, TreeDelete]
  rintro ⟨ixbin, _⟩
  casesm* (_ ∧ _)
  rename_i l r
  let t : Vector Bit (D+1) := (ixbin)
  refine ⟨t, ?_⟩
  simp
  split
  . let ix := (Vector.reverse (Dir.create_dir_vec (Vector.map (fun ix => @Bit.toZMod Order ix) (Vector.dropLast ixbin))))
    let t := MerkleTree.set Tree ix (0:F)
    rw [MerkleTree.proof_ceritfies_item (ix := ix) (tree := t) (proof := MerkleProof.reverse) (item := (0:F))]
    simp
    assumption
    simp
    rename_i hbit
    simp [hbit] at r
    casesm* (_ ∧ _)
    rename_i hitem_at hproof hroot
    simp [hroot]
    rw [MerkleTree.proof_insert_invariant (tree := Tree) (old := (Item)) (new := (0:F))]
    assumption
    rw [<-MerkleTree.recover_equivalence]
    apply And.intro
    simp [hitem_at]
    simp [hproof]
  . apply And.intro
    . simp [l]
    . simp

def TreeDeleteT [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Skip : Bit) (Path : Vector F D) (Item : F) (Proof : Vector F D) (k : (MerkleTree F poseidon₂ D) → Prop) : Prop :=
  match Skip with
  | Bit.zero =>
      MerkleTree.item_at Tree (Dir.create_dir_vec Path).reverse = Item ∧
      MerkleTree.proof Tree (Dir.create_dir_vec Path).reverse = Proof.reverse ∧
      k (MerkleTree.set Tree (Dir.create_dir_vec Path).reverse 0)
  | Bit.one => k Tree

def TreeDeletePrepT [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (Proof : Vector F D) (k : (MerkleTree F poseidon₂ D) → Prop) : Prop :=
  ∃path, nat_to_bits_le (D+1) Index.val = some path ∧
  TreeDeleteT Tree (path.last) (Vector.map Bit.toZMod path.dropLast) Item Proof k

theorem TreeDelete_equivalence [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Skip : Bit) (Path : Vector F D) (Item : F) (Proof : Vector F D) (k : F → Prop) :
  TreeDelete Tree Skip Path Item Proof k ↔
  TreeDeleteT Tree Skip Path Item Proof (fun t => k t.root) := by
  simp [TreeDelete, TreeDeleteT]

theorem TreeDeletePrepT_equivalence [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (Proof : Vector F D) (k : F → Prop) :
  TreeDeletePrep Tree Index Item Proof k ↔
  TreeDeletePrepT Tree Index Item Proof (fun t => k t.root) := by
  simp [TreeDeletePrep, TreeDeletePrepT]
  simp [TreeDelete_equivalence]

def deletion_circuit [Fact (perfect_hash poseidon₂)] {b : Nat}
  (Tree : MerkleTree F poseidon₂ D) (Indices: Vector F b) (IdComms: Vector F b) (Proofs: Vector (Vector F D) b) (k : F → Prop) : Prop :=
  match b with
  | Nat.zero => k Tree.root
  | Nat.succ _ => TreeDeletePrepT Tree Indices.head IdComms.head Proofs.head fun next =>
                  deletion_circuit next Indices.tail IdComms.tail Proofs.tail k

theorem deletion_round_equivalence [Fact (perfect_hash poseidon₂)]
  (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (Proof : Vector F D) (k : F → Prop) :
  TreeDeletePrepT Tree Index Item Proof (fun t => k t.root) ↔
  DeletionRound Index Tree.root Item Proof k := by
  rw [<-TreeDeletePrepT_equivalence]
  rw [<-deletion_round_prep_uncps]
  simp [deletion_round_prep, deletion_round]
  simp [DeletionRound]
  simp [Dir.dropLastOrder]

theorem deletion_circuit_equivalence [Fact (perfect_hash poseidon₂)] {b : Nat}
  (Tree : MerkleTree F poseidon₂ D) (Indices: Vector F b) (IdComms: Vector F b) (Proofs: Vector (Vector F D) b) (k : F → Prop) :
  deletion_circuit Tree Indices IdComms Proofs k ↔
  DeletionLoop Indices Tree.root IdComms Proofs k := by
  induction b generalizing Tree with
  | zero =>
    simp [deletion_circuit, DeletionLoop]
  | succ _ ih =>
    simp [deletion_circuit]
    simp [DeletionLoop]
    rw [<-deletion_round_equivalence]
    simp [ih]

-- theorem after_deletion_all_items_zero_loop
--   [Fact (perfect_hash poseidon₂)]
--   {B : Nat}
--   {h : i ∈ [0:B]}
--   {Tree: MerkleTree F poseidon₂ D}
--   {DeletionIndices: Vector F B}
--   {IdComms: Vector F B}
--   {MerkleProofs: Vector (Vector F D) B}
--   {postRoot : F}
--   {k₁ : F → Prop}
--   :
--   deletion_rounds DeletionIndices Tree.root IdComms MerkleProofs k₁ →
--   ∃path, nat_to_bits_le (D+1) (DeletionIndices[i]'(by rcases h; simp_arith; linarith)).val = some path ∧
--   match path.last with
--   | Bit.zero =>
--     let ix := Dir.create_dir_vec (Vector.map (fun ix => @Bit.toZMod Order ix) path.dropLast)
--     let root := MerkleTree.recover_tail poseidon₂ ix (MerkleProofs[i]'(by rcases h; simp_arith; linarith)) (0:F)
--     deletion_rounds (Vector.tail DeletionIndices) root (Vector.tail IdComms) (Vector.tail MerkleProofs) k₁
--   | Bit.one => True := by
--     induction B generalizing Tree with
--     | zero =>
--       intro hp
--       rcases h with ⟨lo, hi⟩
--       have := Nat.ne_of_lt (Nat.lt_of_le_of_lt lo hi)
--       contradiction
--     | succ B ih =>
--       intro hp
--       rcases h with ⟨lo, hi⟩; --simp at lo hi
--       cases lo with
--       | refl =>
--         simp [deletion_rounds, DeletionRound_uncps] at hp
--         simp
--         let callback := fun next => deletion_rounds (Vector.tail DeletionIndices) next (Vector.tail IdComms) (Vector.tail MerkleProofs) k₁
--         apply after_deletion_item_zero_recover (Tree := Tree) (Item := IdComms.head) (k := callback)
--         simp
--         rw [←Vector.ofFn_get (v := DeletionIndices)]
--         rw [←Vector.ofFn_get (v := DeletionIndices)] at hp
--         rw [←Vector.ofFn_get (v := MerkleProofs)]
--         rw [←Vector.ofFn_get (v := MerkleProofs)] at hp
--         assumption
--       | @step i' hstep =>
--         simp [deletion_rounds, DeletionRound_uncps] at hp
--         --conv ih
--         --simp [deletion_rounds, DeletionRound_uncps] at ih
--         let callback := fun next => deletion_rounds (Vector.tail DeletionIndices) next (Vector.tail IdComms) (Vector.tail MerkleProofs) k₁
--         --let hnext := deletion_rounds (Vector.tail DeletionIndices) next (Vector.tail IdComms) (Vector.tail MerkleProofs) k₁
--         --apply ih (i'.succ)
--         --apply after_deletion_item_zero_recover (Tree := Tree) (Item := IdComms.head) (k := callback)
--         sorry
