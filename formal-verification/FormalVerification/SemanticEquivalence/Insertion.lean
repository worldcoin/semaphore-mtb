import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Misc

import FormalVerification
import FormalVerification.Utils
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness

import FormalVerification.SemanticEquivalence.Verification
import FormalVerification.SemanticEquivalence.Deletion

open SemaphoreMTB (F Order)

open SemaphoreMTB renaming InsertionRound_30_30 → gInsertionRound
open SemaphoreMTB renaming InsertionProof_4_30_4_4_30 → gInsertionProof

lemma MerkleTree.item_at_nat_to_fin' {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (idx : Nat) (h : idx < 2 ^ depth):
  MerkleTree.item_at_nat t idx = some (MerkleTree.tree_item_at_fin t ⟨idx, h⟩) := by
  simp [MerkleTree.item_at_nat, MerkleTree.tree_item_at_fin]
  simp [Dir.nat_to_dir_vec, Dir.fin_to_dir_vec]
  simp [fin_to_bits_le_is_some h]
  congr
  apply Fin.eq_of_veq
  apply Fin.val_cast_of_lt
  assumption

lemma nat_to_bits_le_some_when_lt :
  nat_to_bits_le l a = some w → a < 2 ^ l := by
  induction l generalizing a with
  | zero =>
    unfold nat_to_bits_le
    split <;> simp [*]
  | succ l ih =>
    unfold nat_to_bits_le
    simp [Bind.bind]
    intro w h _
    have := ih h
    apply Nat.lt_of_div_lt_div (k := 2)
    simpa [Nat.pow_succ]

lemma MerkleTree.item_at_nat_some_when_le {D : Nat} {tree : MerkleTree α H D}:
  MerkleTree.item_at_nat tree idx = some el → idx < 2 ^ D := by
  intro h
  unfold item_at_nat at h
  unfold Dir.nat_to_dir_vec at h
  simp at h
  rcases h with ⟨a, h, -⟩
  exact nat_to_bits_le_some_when_lt h

lemma MerkleTree.item_at_nat_none_when_ge {D : Nat} {tree : MerkleTree α H D}:
  idx ≥ 2^D → MerkleTree.item_at_nat tree idx = none := by
  intro h
  cases hp : item_at_nat tree idx
  . rfl
  . have := MerkleTree.item_at_nat_some_when_le hp
    exfalso
    exact not_lt_of_ge h this

lemma MerkleTree.set_at_nat_some_when_le {D:Nat} {tree tree': MerkleTree α H D}:
  MerkleTree.set_at_nat tree idx el = some tree' → idx < 2 ^ D := by
  unfold MerkleTree.set_at_nat
  unfold Dir.nat_to_dir_vec
  simp
  intro w h _
  exact nat_to_bits_le_some_when_lt h


lemma fin_to_bits_le_is_some' {depth : Nat} {idx : Nat} (h : idx < 2 ^ depth) :
  nat_to_bits_le depth idx = some (fin_to_bits_le ⟨idx, h⟩) := by
  simp [fin_to_bits_le]
  split <;> tauto

lemma MerkleTree.set_at_nat_to_fin' {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (idx : Nat) (item : F) (h : idx < 2 ^ depth):
  MerkleTree.set_at_nat t idx item = some (MerkleTree.tree_set_at_fin t ⟨idx, h⟩ item) := by
  simp [MerkleTree.set_at_nat, MerkleTree.tree_set_at_fin]
  simp [Dir.nat_to_dir_vec]
  simp [Dir.fin_to_dir_vec]
  simp [fin_to_bits_le_is_some' h]

lemma MerkleTree.set_at_nat_to_fin_some' {depth : Nat} {F: Type} {H: Hash F 2} {a : MerkleTree F H depth} (t : MerkleTree F H depth) (idx : Nat) (item : F) (h : idx < 2 ^ depth):
  MerkleTree.set_at_nat t idx item = some a ↔
  MerkleTree.tree_set_at_fin t ⟨idx, h⟩ item = a := by
  rw [set_at_nat_to_fin' (h := h)]
  simp

lemma MerkleTree.item_at_nat_to_fin_some' {depth : Nat} {F: Type} {H: Hash F 2} {a : F} (t : MerkleTree F H depth) (idx : Nat) (h : idx < 2 ^ depth):
  MerkleTree.item_at_nat t idx = some a ↔
  MerkleTree.tree_item_at_fin t ⟨idx, h⟩ = a := by
  rw [item_at_nat_to_fin' (h := h)]
  . simp

theorem MerkleTree.item_at_fin_invariant' {H : Hash α 2} {tree tree': MerkleTree α H depth} {ix₁ ix₂ : Fin (2 ^ depth)} { neq : ix₁ ≠ ix₂ }:
  MerkleTree.tree_set_at_fin tree ix₁ item₁ = tree' →
  MerkleTree.tree_item_at_fin tree' ix₂ = MerkleTree.tree_item_at_fin tree ix₂ := by
  rw [<-set_at_nat_to_fin_some' (h := ix₁.2)]
  rw [<-item_at_nat_to_fin_some' (h := ix₂.2)]
  rw [<-item_at_nat_to_fin' (h := ix₂.2)]
  apply MerkleTree.item_at_nat_invariant (neq := fun h => neq (Fin.eq_of_veq h))

lemma MerkleTree.item_at_fin_set_at_fin {H : Hash α 2} {tree : MerkleTree α H depth} {item: α} {ix: Fin (2 ^ depth)}:
  tree_item_at_fin (tree.tree_set_at_fin ix item) ix = item := read_after_insert_sound _ _ _

theorem ZMod.val_fin {n : ℕ } {f : ZMod n.succ}: f.val = Fin.val f := by
  simp [val]


-- Insertion round semantic equivalence

def insertion_round (Path: Vector F D) (Item: F) (PrevRoot: F) (Proof: Vector F D) (k: F -> Prop) : Prop :=
  (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec Path) Proof 0 = PrevRoot) ∧
  k (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec Path) Proof Item)

def insertion_round_prep (Index: F) (Item: F) (PrevRoot: F) (Proof: Vector F D) (k: F -> Prop) : Prop :=
  ∃out: Vector F D, recover_binary_zmod' out = Index ∧ is_vector_binary out ∧
  insertion_round out Item PrevRoot Proof k

def fin_to_path (index : Nat) (d : Nat): Validate (index < 2^d) ⊕ Vector Dir d :=
  if h : index < 2 ^ d then
    Sum.inr (Dir.fin_to_dir_vec ⟨index, h⟩).reverse
  else
    Sum.inl ⟨h⟩

def tree_proof_at_validate (tree : MerkleTree α H d) (index : Nat): Validate (index < 2 ^ d) ⊕ Vector α d := do
  let p ← fin_to_path index d
  pure $ tree.proof p

def insertionRound_semantics (Index Item : F) (Tree : MerkleTree F poseidon₂ D) (Proof : Vector F D) (k : MerkleTree F poseidon₂ D → Prop): Prop :=
  if h : Index.val < 2 ^ D then
    Tree.tree_item_at_fin ⟨Index.val, h⟩ = 0 ∧
    Tree.tree_proof_at_fin ⟨Index.val, h⟩ = Proof.reverse ∧
    k (Tree.tree_set_at_fin ⟨Index.val, h⟩ Item)
  else False

lemma Fin.castNat_lt_pow {n k : ℕ} (h : n < 2^k) : ↑n = Fin.mk n h := by
  apply Fin.eq_of_veq
  exact Nat.mod_eq_of_lt h

theorem insertionRound_rw [Fact (CollisionResistant poseidon₂)] {Tree : MerkleTree F poseidon₂ D} :
  gInsertionRound Index Item Tree.root Proof k ↔
  insertionRound_semantics Index Item Tree Proof (fun t => k t.root) := by
  simp [insertionRound_semantics, gInsertionRound]
  simp [Gates.to_binary, Gates.eq]
  simp [VerifyProof_looped, proof_rounds_uncps]
  apply Iff.intro
  . intro ⟨path, ⟨path_rec, path_bin⟩, _, hpre, _, hpost⟩
    split
    . rename_i h
      unfold MerkleTree.tree_item_at_fin
      unfold MerkleTree.tree_set_at_fin
      unfold MerkleTree.tree_proof_at_fin
      simp_rw [←Fin.castNat_lt_pow h, Dir.recover_binary_zmod'_to_dir h (by decide) path_bin path_rec]
      have : MerkleTree.recover poseidon₂ (Dir.create_dir_vec path).reverse Proof.reverse 0 = Tree.root := by
        rw [←MerkleTree.recover_tail_equals_recover_reverse, ←hpre, ←Vector.ofFn_get (v := Proof)]
        rfl
      refine ⟨?_, ?_, ?_⟩
      . apply MerkleTree.proof_ceritfies_item
        exact this
      . apply MerkleTree.recover_proof_reversible
        exact this
      . rw [←MerkleTree.proof_insert_invariant, ←MerkleTree.recover_tail_equals_recover_reverse]
        exact hpost
        rotate_left
        rw [←Vector.ofFn_get (v := Proof)] at this
        exact this
    . rename_i h
      rw [recover_binary_zmod_bit path_bin] at path_rec
      rw [←path_rec] at h
      rw [binary_zmod_same_as_nat _ (by decide)] at h
      exact h (binary_nat_lt _)
  . intro hp
    split at hp <;> try contradiction
    rcases hp with ⟨hitem, hproof, hnext⟩
    rename_i h
    apply Exists.intro (Vector.map Bit.toZMod (fin_to_bits_le ⟨Index.val, h⟩))
    simp only
      [ ←Dir.recover_binary_zmod'_to_dir h (by decide) vector_binary_of_bit_to_zmod (fin_to_bits_recover_binary _ _)
      , vector_binary_of_bit_to_zmod
      , fin_to_bits_recover_binary _ _
      , true_and
      ]
    unfold MerkleTree.tree_item_at_fin at hitem
    unfold MerkleTree.tree_set_at_fin at hnext
    unfold MerkleTree.tree_proof_at_fin at hproof
    simp_rw [←Fin.castNat_lt_pow h] at hitem hnext hproof
    refine ⟨?_, ?_⟩
    . rw [MerkleTree.recover_tail_equals_recover_reverse]
      rw [←MerkleTree.recover_equivalence]
      refine ⟨hitem, ?_⟩
      rw [hproof, ←Vector.ofFn_get (v := Proof)]
      rfl
    . apply Eq.subst _ hnext
      rw [MerkleTree.recover_tail_equals_recover_reverse, eq_comm, ←MerkleTree.recover_equivalence]
      refine ⟨MerkleTree.read_after_insert_sound _ _ _, ?_⟩
      rw [MerkleTree.proof_of_set_is_proof, hproof, ←Vector.ofFn_get (v := Proof)]
      rfl

def insertionRoundsSemantics {b : Nat}
  (startIndex : F)
  (tree : MerkleTree F poseidon₂ D)
  (identities : Vector F b)
  (proofs : Vector (Vector F D) b)
  (k : F → Prop): Prop := match b with
  | 0 => k tree.root
  | Nat.succ _ => insertionRound_semantics
      startIndex
      identities.head
      tree
      proofs.head
      fun t => insertionRoundsSemantics (startIndex + 1) t identities.tail proofs.tail k

theorem exists_binder {f : α → Prop} : (∃x, x = y ∧ f x) ↔ f y := by
  apply Iff.intro
  . intro ⟨x, ⟨hx, hfx⟩⟩
    rw [←hx]
    exact hfx
  . intro hfy
    refine ⟨y, ⟨rfl, hfy⟩⟩

theorem insertionRounds_rw [Fact (CollisionResistant poseidon₂)]  {Tree : MerkleTree F poseidon₂ D}:
  gInsertionProof startIndex Tree.root idComms merkleProofs k ↔
  insertionRoundsSemantics startIndex Tree idComms merkleProofs k := by
  unfold gInsertionProof
  simp_rw [insertionRound_rw, Gates.add, exists_binder]
  apply Iff.of_eq
  simp only [add_zero]

  repeat (
    unfold insertionRoundsSemantics
    cases idComms using Vector.casesOn; rename_i idComm idComms -- with | cons idComm idComms =>
    cases merkleProofs using Vector.casesOn; rename_i merkleProof merkleProofs
    try rw [add_assoc]
    congr
    ext
    apply Iff.of_eq
  )

  unfold insertionRoundsSemantics
  cases idComms using Vector.casesOn with | cons idComm idComms =>
  cases merkleProofs using Vector.casesOn with | cons merkleProof merkleProofs =>
  try rw [add_assoc]
  congr

def rootTransformationSpec'' {B : ℕ}
  (tree : MerkleTree F poseidon₂ D)
  (identities : Vector F B)
  (startIndex : Nat): Option (MerkleTree F poseidon₂ D) := match B with
  | 0 => some tree
  | _ + 1 => match tree.set_at_nat startIndex identities.head with
    | some nextTree => rootTransformationSpec'' nextTree identities.tail (startIndex + 1)
    | none => none

lemma rootTransformSpec_some_ix_bound {B : ℕ} {identities : Vector F B.succ}:
  rootTransformationSpec'' tree identities startIndex = some tree' →
  startIndex < 2 ^ D := by
  intro hp
  conv at hp => lhs; whnf
  split at hp
  . apply MerkleTree.set_at_nat_some_when_le
    assumption
  . contradiction

lemma rootTransformSpec_succ {B : ℕ} {identities : Vector F B.succ}
  (hp : rootTransformationSpec'' tree identities startIndex = some tree'):
  rootTransformationSpec''
    (tree.tree_set_at_fin ⟨startIndex, rootTransformSpec_some_ix_bound hp⟩ identities.head)
    identities.tail
    (startIndex + 1) = some tree' := by
    have bound : startIndex < 2 ^ D := rootTransformSpec_some_ix_bound hp
    conv at hp => lhs; whnf
    split at hp
    . rename_i h
      rw [MerkleTree.set_at_nat_to_fin' (h:=bound)] at h
      injection h with h
      rwa [h]
    . contradiction

theorem insertionRoundsRootTransformation
  {B : ℕ} {startIndex : Nat} {identities : Vector F B} {proofs : Vector (Vector F D) B}
  (indexIsValid : startIndex + B < 2 ^ D):
  insertionRoundsSemantics startIndex tree identities proofs k →
  ∃postTree, rootTransformationSpec'' tree identities startIndex = some postTree ∧ k postTree.root := by
  intro hp
  induction B generalizing startIndex tree with
  | zero => exists tree
  | succ B ih =>
    unfold insertionRoundsSemantics at hp
    unfold insertionRound_semantics at hp
    split at hp
    . rename_i bound
      rcases hp with ⟨-, -, hp⟩
      have := by
        refine ih ?_ hp
        rw [add_assoc]
        apply Nat.lt_of_le_of_lt
        . apply Nat.add_le_add_right
          apply Nat.mod_le
        . simp; linarith
      have ixLeOrd : startIndex < Order := by
        apply LT.lt.trans
        apply Nat.lt_sub_of_add_lt
        exact indexIsValid
        apply Nat.lt_of_le_of_lt
        apply Nat.sub_le
        decide
      rcases this with ⟨t, hsome, hk⟩
      exists t
      conv => arg 1; lhs; whnf
      rw [MerkleTree.set_at_nat_to_fin']
      simp
      apply And.intro
      . rw [←hsome]
        congr
        . exact Eq.symm (ZMod.val_cast_of_lt ixLeOrd)
        . exact Eq.symm (Nat.mod_eq_of_lt ixLeOrd)
        . rw [ZMod.val_cast_of_lt ixLeOrd] at bound; exact bound
      . exact hk
    . contradiction

theorem insertionRoundsRootTransformation'
  {B : ℕ} {startIndex : F} {identities : Vector F B} {proofs : Vector (Vector F D) B}:
  -- (indexIsValid : startIndex + B < 2 ^ D):
  insertionRoundsSemantics startIndex tree identities proofs k →
  ∃postTree, rootTransformationSpec'' tree identities startIndex.val = some postTree ∧ k postTree.root := by
  intro hp
  induction B generalizing startIndex tree with
  | zero => exists tree
  | succ B ih =>
    unfold insertionRoundsSemantics at hp
    unfold insertionRound_semantics at hp
    split at hp
    . rename_i bound
      rcases hp with ⟨-, -, hp⟩
      have := ih hp
        -- refine ih hp
        -- rw [add_assoc]
        -- apply Nat.lt_of_le_of_lt
        -- . apply Nat.add_le_add_right
        --   apply Nat.mod_le
        -- . simp; linarith
      -- have ixLeOrd : startIndex < Order := by
      --   apply LT.lt.trans
      --   apply Nat.lt_sub_of_add_lt
      --   exact indexIsValid
      --   apply Nat.lt_of_le_of_lt
      --   apply Nat.sub_le
      --   decide
      rcases this with ⟨t, hsome, hk⟩
      exists t
      conv => arg 1; lhs; whnf
      rw [MerkleTree.set_at_nat_to_fin']
      simp
      apply And.intro
      . rw [←hsome]
        congr
        . exact Eq.symm (ZMod.val_cast_of_lt ixLeOrd)
        . exact Eq.symm (Nat.mod_eq_of_lt ixLeOrd)
        . rw [ZMod.val_cast_of_lt ixLeOrd] at bound; exact bound
      . exact hk
    . contradiction

theorem before_insertion_all_zero
  {B: ℕ} {startIndex : F} {proofs : Vector (Vector F D) B} {identities : Vector F B}:
  insertionRoundsSemantics (b := B) startIndex tree identities proofs k →
  ∀i ∈ [startIndex.val : (startIndex + B).val], tree.item_at_nat i = some 0 := by
  intro hp i hi

  induction B generalizing i startIndex tree with
  | zero =>
    cases hi; rename_i hl hu
    simp at hu
    simp at hl
    have := Nat.lt_of_le_of_lt hl hu
    have := lt_irrefl _ this
    contradiction
  | succ B ih =>
    cases identities using Vector.casesOn with | cons id ids =>
    cases proofs using Vector.casesOn with | cons proof proofs =>
    unfold insertionRoundsSemantics at hp
    unfold insertionRound_semantics at hp
    rcases hi with ⟨hil, hiu⟩
    split at hp
    . cases hil
      . rcases hp with ⟨hp, -, -⟩
        rename_i h
        rw [MerkleTree.item_at_nat_to_fin', hp]
      . rename_i i hil
        rcases hp with ⟨-, -, hp⟩
        have := ih hp (i.succ) (by
          apply And.intro
          . apply Nat.le_trans (m := startIndex.val + 1)
            simp [ZMod.val_fin]
            rw [Fin.val_add_one]
            split <;> simp
            simp_arith
            assumption
          . apply Nat.lt_of_lt_of_eq hiu
            simp [add_assoc]
            rw [add_comm (b:=1)]
        )
        have bound := MerkleTree.item_at_nat_some_when_le this
        rw [MerkleTree.item_at_nat_to_fin' _ _ bound] at this
        rw [MerkleTree.item_at_fin_invariant'] at this
        rw [←MerkleTree.item_at_nat_to_fin' _ _ bound] at this
        assumption
        rfl
        simp
        apply Nat.ne_of_lt
        apply Nat.lt_succ_of_le
        assumption
    . contradiction

theorem ix_bound {B : ℕ} {startIndex : F} {identities : Vector F B.succ} {proofs : Vector (Vector F D) B.succ}:
  insertionRoundsSemantics startIndex tree identities proofs k →
  startIndex.val + B < 2 ^ D := by
  induction B generalizing startIndex tree with
  | zero =>
    intro hp
    unfold insertionRoundsSemantics at hp
    unfold insertionRound_semantics at hp
    split at hp
    . simpa
    . contradiction
  | succ B ih =>
    intro hp
    unfold insertionRoundsSemantics at hp
    unfold insertionRound_semantics at hp
    split at hp
    . rename_i hi
      rcases hp with ⟨-, -, hp⟩
      have := ih hp
      rw [ZMod.val_fin] at this hi
      cases identities using Vector.casesOn with | cons id ids =>
      cases proofs using Vector.casesOn with | cons proof proofs =>
      rw [Fin.val_add_one_of_lt _] at this
      . rw [ZMod.val_fin]
        linarith
      . rw [Fin.lt_iff_val_lt_val]
        exact LT.lt.trans hi (by decide)
    . contradiction

instance : Decidable (i ∈ [a : b]) := by
  simp [Membership.mem]; infer_instance

lemma treeTransform_get_lt {i : Nat} {B : ℕ} {startIndex : Nat}
  {identities : Vector F B}:
  rootTransformationSpec'' tree identities startIndex = some tree' →
  i < startIndex → tree.item_at_nat i = tree'.item_at_nat i := by
  induction B generalizing startIndex tree tree' with
  | zero =>
    intro h _
    cases identities using Vector.casesOn
    injection h with h
    rw [h]
  | succ B ih =>
    intro h hu
    cases identities using Vector.casesOn
    conv at h => lhs; whnf
    split at h
    . rename_i hp'
      have := ih h (by linarith)
      rw [←this]
      have sibound : startIndex < 2^D := MerkleTree.set_at_nat_some_when_le hp'
      have ibound : i < 2^D := lt_trans hu sibound
      rw [MerkleTree.set_at_nat_to_fin_some' (h:=sibound)] at hp'
      rw [MerkleTree.item_at_nat_to_fin' (h:=ibound)]
      rw [MerkleTree.item_at_nat_to_fin' (h:=ibound)]
      apply congrArg
      apply Eq.symm
      apply MerkleTree.item_at_fin_invariant' hp'
      intro hp
      injection hp with hp
      exact Nat.ne_of_lt hu (eq_comm.mp hp)
    . contradiction

lemma treeTransform_get_gt {i B startIndex : ℕ}
  {identities : Vector F B}:
  rootTransformationSpec'' tree identities startIndex = some tree' →
  i ≥ startIndex + B → tree.item_at_nat i = tree'.item_at_nat i := by
  induction B generalizing startIndex tree tree' with
  | zero =>
    intro h _
    cases identities using Vector.casesOn
    injection h with h
    rw [h]
  | succ B ih =>
    intro h hl
    cases identities using Vector.casesOn
    conv at h => lhs; whnf
    split at h
    . cases Nat.lt_or_ge i (2^D) with
      | inl ibound =>
        rename_i hp
        have sibound : startIndex < 2^D := MerkleTree.set_at_nat_some_when_le hp
        repeat rw [MerkleTree.item_at_nat_to_fin' (h:=ibound)]
        rw [MerkleTree.set_at_nat_to_fin_some' (h:=sibound)] at hp
        have := ih h (by linarith)
        repeat rw [MerkleTree.item_at_nat_to_fin' (h:=ibound)] at this
        rw [←this]
        apply congrArg
        apply Eq.symm
        apply MerkleTree.item_at_fin_invariant' hp
        intro hp
        injection hp with hp
        linarith
      | inr h =>
        simp_rw [MerkleTree.item_at_nat_none_when_ge h]
    . contradiction

lemma treeTransform_get_inrange {i B startIndex : ℕ} {identities : Vector F B}
  (hp : rootTransformationSpec'' tree identities startIndex = some tree')
  (inrange : i ∈ [0 : B]):
  tree'.item_at_nat (startIndex + i) = identities[i]'inrange.2 := by
  induction B generalizing startIndex i tree tree' with
  | zero => cases inrange; exfalso; linarith
  | succ B ih =>
    have := rootTransformSpec_succ hp
    have bound := rootTransformSpec_some_ix_bound hp
    cases identities using Vector.casesOn with | cons id ids =>
    cases i with
    | zero =>
      have := treeTransform_get_lt this (by linarith)
      simp
      rw [←this, MerkleTree.item_at_nat_to_fin_some' _ _ bound]
      simp
      apply MerkleTree.read_after_insert_sound
    | succ i =>
      have inrange : i ∈ [0 : B] := by
        cases inrange
        apply And.intro <;> linarith
      have := ih this inrange
      simp
      simp at this
      rw [←this]
      apply congrArg
      simp_arith
