import ProvenZk

import FormalVerification
import FormalVerification.Utils
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness

import FormalVerification.SemanticEquivalence.Verification
import FormalVerification.SemanticEquivalence.Deletion

open SemaphoreMTB (F Order)

open SemaphoreMTB renaming InsertionRound_30_30 → gInsertionRound
open SemaphoreMTB renaming InsertionProof_4_30_4_4_30 → gInsertionProof

theorem ZMod.val_fin {n : ℕ } {f : ZMod n.succ}: f.val = Fin.val f := by
  simp [val]

-- def insertionRoundSemantics (Index Item : F) (Tree : MerkleTree F poseidon₂ D) (Proof : Vector F D) (k : MerkleTree F poseidon₂ D → Prop): Prop :=
--   if h : Index.val < 2 ^ D then
--     Tree.itemAtFin ⟨Index.val, h⟩ = 0 ∧
--     Tree.proofAtFin ⟨Index.val, h⟩ = Proof.reverse ∧
--     k (Tree.setAtFin ⟨Index.val, h⟩ Item)
--   else False

-- theorem insertionRoundCircuit_eq_insertionRoundSemantics [Fact (CollisionResistant poseidon₂)] {Tree : MerkleTree F poseidon₂ D} :
--   gInsertionRound Index Item Tree.root Proof k ↔
--   insertionRoundSemantics Index Item Tree Proof (fun t => k t.root) := by
--   unfold insertionRoundSemantics
--   unfold gInsertionRound
--   conv =>
--     pattern (occs := *) _ ::ᵥ _
--     . change 0 ::ᵥ Vector.ofFn Proof.get;
--     . change Item ::ᵥ Vector.ofFn Proof.get;
--   cases Decidable.em (Index.val < 2 ^ D) with
--   | inl h =>
--     simp [h, Gates.to_binary_iff_eq_fin_to_bits_le_of_pow_length_lt, VerifyProof_uncps]
--     simp [MerkleTree.itemAtFin, MerkleTree.proofAtFin, MerkleTree.setAtFin, ←MerkleTree.recover_equivalence, MerkleTree.set_root_eq_recover]
--     apply Iff.intro <;> { intros; casesm* _∧_; simp [*] at *; try assumption }
--   | inr h =>
--     simp [h]
--     intro _ h
--     replace h := Gates.to_binary_rangecheck h
--     contradiction

-- def insertionRoundsSemantics {b : Nat}
--   (startIndex : F)
--   (tree : MerkleTree F poseidon₂ D)
--   (identities : Vector F b)
--   (proofs : Vector (Vector F D) b)
--   (k : F → Prop): Prop := match b with
--   | 0 => k tree.root
--   | Nat.succ _ => insertionRoundSemantics
--       startIndex
--       identities.head
--       tree
--       proofs.head
--       fun t => insertionRoundsSemantics (startIndex + 1) t identities.tail proofs.tail k

-- theorem exists_binder {f : α → Prop} : (∃x, x = y ∧ f x) ↔ f y := by
--   apply Iff.intro
--   . intro ⟨x, ⟨hx, hfx⟩⟩
--     rw [←hx]
--     exact hfx
--   . intro hfy
--     refine ⟨y, ⟨rfl, hfy⟩⟩

-- theorem insertionRoundsCircuit_eq_insertionRoundsSemantics [Fact (CollisionResistant poseidon₂)]  {Tree : MerkleTree F poseidon₂ D}:
--   gInsertionProof startIndex Tree.root idComms merkleProofs k ↔
--   insertionRoundsSemantics startIndex Tree idComms merkleProofs k := by
--   unfold gInsertionProof
--   simp_rw [insertionRoundCircuit_eq_insertionRoundSemantics, Gates.add, exists_binder]
--   apply Iff.of_eq
--   simp only [add_zero]

--   repeat (
--     unfold insertionRoundsSemantics
--     cases idComms using Vector.casesOn; rename_i idComm idComms
--     cases merkleProofs using Vector.casesOn; rename_i merkleProof merkleProofs
--     try rw [add_assoc]
--     congr
--     ext
--     apply Iff.of_eq
--   )

--   unfold insertionRoundsSemantics
--   cases idComms using Vector.casesOn with | cons idComm idComms =>
--   cases merkleProofs using Vector.casesOn with | cons merkleProof merkleProofs =>
--   try rw [add_assoc]
--   congr

-- def treeTransformationSemantics {B : ℕ}
--   (tree : MerkleTree F poseidon₂ D)
--   (identities : Vector F B)
--   (startIndex : Nat): Option (MerkleTree F poseidon₂ D) := match B with
--   | 0 => some tree
--   | _ + 1 => if h : startIndex < 2 ^ D
--     then treeTransformationSemantics (tree.setAtFin ⟨startIndex, h⟩ identities.head) identities.tail (startIndex + 1)
--     else none

-- lemma treeTransformationSemantics_some_index_bound {B : ℕ} {identities : Vector F B.succ}:
--   treeTransformationSemantics tree identities startIndex = some tree' →
--   startIndex < 2 ^ D := by
--   intro hp
--   unfold treeTransformationSemantics at hp
--   split at hp
--   . assumption
--   . contradiction

-- lemma treeTransformationSemantics_next {B : ℕ} {identities : Vector F B.succ}
--   (hp : treeTransformationSemantics tree identities startIndex = some tree'):
--   treeTransformationSemantics
--     (tree.setAtFin ⟨startIndex, treeTransformationSemantics_some_index_bound hp⟩ identities.head)
--     identities.tail
--     (startIndex + 1) = some tree' := by
--     have bound : startIndex < 2 ^ D := treeTransformationSemantics_some_index_bound hp
--     unfold treeTransformationSemantics at hp
--     split at hp
--     . rename_i h
--       assumption
--     . contradiction

-- theorem insertionRoundsRootTransformation
--   {B : ℕ} {startIndex : F} {identities : Vector F B} {proofs : Vector (Vector F D) B}:
--   insertionRoundsSemantics startIndex tree identities proofs k →
--   ∃postTree, treeTransformationSemantics tree identities startIndex.val = some postTree ∧ k postTree.root := by
--   intro hp
--   induction B generalizing startIndex tree with
--   | zero => exists tree
--   | succ B ih =>
--     unfold insertionRoundsSemantics at hp
--     unfold insertionRoundSemantics at hp
--     split at hp
--     . rename_i bound
--       rcases hp with ⟨-, -, hp⟩
--       have := ih hp
--       rcases this with ⟨t, hsome, hk⟩
--       exists t
--       unfold treeTransformationSemantics
--       split; rotate_left; exfalso; rename_i h; exact h bound
--       apply And.intro
--       . rw [←hsome]
--         congr
--         rw [ZMod.val_add, Nat.mod_eq_of_lt]
--         . rfl
--         . conv => lhs; arg 2; whnf
--           calc
--             startIndex.val + 1 < 2 ^ D + 1 := Nat.add_lt_add_right bound 1
--             _ < Order := by decide
--       . exact hk
--     . contradiction

-- theorem before_insertion_all_zero
--   {B: ℕ} {startIndex : F} {proofs : Vector (Vector F D) B} {identities : Vector F B}:
--   insertionRoundsSemantics (b := B) startIndex tree identities proofs k →
--   ∀i ∈ [startIndex.val : (startIndex + B).val], tree[i]? = some 0 := by
--   intro hp i hi

--   induction B generalizing i startIndex tree with
--   | zero =>
--     cases hi; rename_i hl hu
--     simp at hu
--     simp at hl
--     have := Nat.lt_of_le_of_lt hl hu
--     have := lt_irrefl _ this
--     contradiction
--   | succ B ih =>
--     cases identities using Vector.casesOn with | cons id ids =>
--     cases proofs using Vector.casesOn with | cons proof proofs =>
--     unfold insertionRoundsSemantics at hp
--     unfold insertionRoundSemantics at hp
--     rcases hi with ⟨hil, hiu⟩
--     split at hp
--     . cases hil
--       . rcases hp with ⟨hp, -, -⟩
--         rename_i h
--         rw [getElem?_eq_some_getElem_of_valid_index]
--         . simp [getElem, hp]
--         . exact h
--       . rename_i i hil
--         rcases hp with ⟨-, -, hp⟩
--         have := ih hp (i.succ) (by
--           apply And.intro
--           . apply Nat.le_trans (m := startIndex.val + 1)
--             simp [ZMod.val_fin]
--             rw [Fin.val_add_one]
--             split <;> simp
--             simp_arith
--             assumption
--           . apply Nat.lt_of_lt_of_eq hiu
--             simp [add_assoc]
--             rw [add_comm (b:=1)]
--         )
--         have := getElem_of_getElem?_some this
--         rw [MerkleTree.getElem_setAtFin_invariant_of_neq] at this
--         exact getElem?_some_of_getElem this
--         simp
--         rw [eq_comm]
--         apply Nat.ne_of_lt
--         apply Nat.lt_succ_of_le
--         assumption
--     . contradiction

-- theorem ix_bound {B : ℕ} {startIndex : F} {identities : Vector F B.succ} {proofs : Vector (Vector F D) B.succ}:
--   insertionRoundsSemantics startIndex tree identities proofs k →
--   startIndex.val + B < 2 ^ D := by
--   induction B generalizing startIndex tree with
--   | zero =>
--     intro hp
--     unfold insertionRoundsSemantics at hp
--     unfold insertionRoundSemantics at hp
--     split at hp
--     . simpa
--     . contradiction
--   | succ B ih =>
--     intro hp
--     unfold insertionRoundsSemantics at hp
--     unfold insertionRoundSemantics at hp
--     split at hp
--     . rename_i hi
--       rcases hp with ⟨-, -, hp⟩
--       have := ih hp
--       rw [ZMod.val_fin] at this hi
--       cases identities using Vector.casesOn with | cons id ids =>
--       cases proofs using Vector.casesOn with | cons proof proofs =>
--       rw [Fin.val_add_one_of_lt _] at this
--       . rw [ZMod.val_fin]
--         linarith
--       . rw [Fin.lt_iff_val_lt_val]
--         exact LT.lt.trans hi (by decide)
--     . contradiction

-- lemma treeTransform_get_lt {i : Nat} {B : ℕ} {startIndex : Nat}
--   {identities : Vector F B}:
--   treeTransformationSemantics tree identities startIndex = some tree' →
--   i < startIndex → tree[i]? = tree'[i]? := by
--   induction B generalizing startIndex tree tree' with
--   | zero =>
--     intro h _
--     cases identities using Vector.casesOn
--     injection h with h
--     rw [h]
--   | succ B ih =>
--     intro h hu
--     cases identities using Vector.casesOn
--     unfold treeTransformationSemantics at h
--     split at h
--     . rename_i hp'
--       have := ih h (by linarith)
--       rw [←this]
--       have ibound : i < 2^D := lt_trans hu hp'
--       repeat rw [getElem?_eq_some_getElem_of_valid_index (cont := MerkleTree _ _ _) ibound]
--       apply congrArg
--       rw [eq_comm]
--       apply MerkleTree.getElem_setAtFin_invariant_of_neq
--       apply Nat.ne_of_lt hu
--     . contradiction

-- lemma treeTransform_get_gt {i B startIndex : ℕ}
--   {identities : Vector F B}:
--   treeTransformationSemantics tree identities startIndex = some tree' →
--   i ≥ startIndex + B → tree[i]? = tree'[i]? := by
--   induction B generalizing startIndex tree tree' with
--   | zero =>
--     intro h _
--     cases identities using Vector.casesOn
--     injection h with h
--     rw [h]
--   | succ B ih =>
--     intro h hl
--     cases identities using Vector.casesOn
--     unfold treeTransformationSemantics at h
--     split at h
--     . cases Nat.lt_or_ge i (2^D) with
--       | inl ibound =>
--         rename_i sibound
--         have := ih h (by linarith)
--         rw [←ih h (by linarith)]
--         repeat rw [getElem?_eq_some_getElem_of_valid_index (cont := MerkleTree _ _ _) ibound]
--         apply congrArg
--         rw [eq_comm]
--         apply MerkleTree.getElem_setAtFin_invariant_of_neq
--         linarith
--       | inr h =>
--         repeat rw [getElem?_none_of_invalid_index]
--         all_goals exact not_lt_of_ge h
--     . contradiction

-- lemma treeTransform_get_inrange {i B startIndex : ℕ} {identities : Vector F B}
--   (hp : treeTransformationSemantics tree identities startIndex = some tree')
--   (inrange : i ∈ [0 : B]):
--   tree'[startIndex + i]? = identities[i]'inrange.2 := by
--   induction B generalizing startIndex i tree tree' with
--   | zero => cases inrange; exfalso; linarith
--   | succ B ih =>
--     have := treeTransformationSemantics_next hp
--     have bound := treeTransformationSemantics_some_index_bound hp
--     cases identities using Vector.casesOn with | cons id ids =>
--     cases i with
--     | zero =>
--       have := treeTransform_get_lt this (by linarith)
--       rw [getElem?_eq_some_getElem_of_valid_index (cont := MerkleTree _ _ _) bound] at this
--       simp
--       rw [←this]
--       apply congrArg
--       apply MerkleTree.read_after_insert_sound
--     | succ i =>
--       have inrange : i ∈ [0 : B] := by
--         cases inrange
--         apply And.intro <;> linarith
--       have := ih this inrange
--       simp
--       simp at this
--       rw [←this]
--       rw [Nat.succ_eq_one_add, add_assoc]
