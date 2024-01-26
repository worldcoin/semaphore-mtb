import ProvenZk

import FormalVerification
import FormalVerification.Utils
import FormalVerification.Poseidon

import FormalVerification.SemanticEquivalence.Verification

open SemaphoreMTB (F Order)

open SemaphoreMTB renaming DeletionRound_30_30 → gDeletionRound
open SemaphoreMTB renaming DeletionProof_4_4_30_4_4_30 → gDeletionProof
open SemaphoreMTB renaming VerifyProof_31_30 → gVerifyProof


-- theorem recover_binary_zmod'_snoc {n} {vs : Vector (ZMod (Nat.succ p)) n} {v}:
--   recover_binary_zmod' (Vector.snoc vs v) = recover_binary_zmod' vs + (2 ^ vs.length) * v.val := by
--   induction n generalizing v with
--   | zero =>
--     cases vs using Vector.casesOn
--     simp [recover_binary_zmod']
--   | succ n ih =>
--     cases vs using Vector.casesOn
--     unfold recover_binary_zmod'
--     simp [Vector.length, pow_succ, ih]
--     ring

-- lemma Fin.castNat_lt_pow {n k : ℕ} (h : n < 2^k) : ↑n = Fin.mk n h := by
--   apply Fin.eq_of_veq
--   exact Nat.mod_eq_of_lt h



namespace Deletion

def deletionRoundSemantics (Index Item : F) (Tree : MerkleTree F poseidon₂ D) (Proof : Vector F D) (k : MerkleTree F poseidon₂ D → Prop): Prop :=
  if Index.val < 2 ^ (D + 1)
    then if h : Index.val < 2 ^ D
      then Tree.itemAtFin ⟨Index.val, h⟩ = Item ∧
           Tree.proofAtFin ⟨Index.val, h⟩ = Proof.reverse ∧
           k (Tree.setAtFin ⟨Index.val, h⟩ 0)
      else k Tree
    else False
end Deletion
-- instance : Fact (Order > 2) := ⟨by decide⟩
-- def Fin.msb {d:ℕ} (v : Fin (2^d.succ)): Bool := v.val ≥ 2^d


-- @[simp]
-- theorem Fin.msb_false_of_lt {d:ℕ} {v : Fin (2^d.succ)} (h : v.val < 2^d): Fin.msb v = false := by
--   simpa [msb]

-- def Fin.lsbs {d:ℕ} (v : Fin (2^d.succ)): Fin (2^d) := ⟨v.val - (Fin.msb v).toNat * 2^d, prop⟩ where
--   prop := by
--     cases Nat.lt_or_ge v.val (2^d) with
--     | inl lt =>
--       simp [lt, Bool.toNat]
--     | inr ge =>
--       apply Nat.sub_lt_left_of_lt_add
--       . simp [msb, ge, Bool.toNat]
--       . have : 2^d + 2^d = 2^d.succ := by simp_arith [pow_succ]
--         simp [msb, ge, Bool.toNat, v.prop, this]

-- @[simp]
-- theorem Fin.lsbs_eq_val_of_lt {d:ℕ} {v : Fin (2^d.succ)} (h : v.val < 2^d): Fin.lsbs v = ⟨v, h⟩ := by
--   simp [lsbs, *, Bool.toNat]

-- theorem fin_to_bits_le_succ_eq_snoc {d : ℕ} {v : Fin (2^d.succ)}:
--   fin_to_bits_le v = (fin_to_bits_le (Fin.lsbs v)).snoc (Fin.msb v) := by

-- theorem fin_to_bits_le_succ_eq_snoc_zero_of_lt {d : ℕ} {v : Fin (2^d.succ)} (h : v.val < 2^d):
--   fin_to_bits_le v = (fin_to_bits_le ⟨v.val, h⟩).snoc false := by
--   simp [fin_to_bits_le_succ_eq_snoc, Fin.msb_false_of_lt h, Fin.lsbs_eq_of_lt h]

-- theorem fin_to_bits_le_succ_eq_snoc_one_of_ge {d : ℕ} {v : Fin (2^d.succ)} (h : v.val ≥ 2^d):
--   fin_to_bits_le v = (fin_to_bits_le ⟨v.val - 2^d, ((by sorry): v.val - 2^d < 2^d)⟩).snoc true := by sorry
--   -- simp [fin_to_bits_le_succ_eq_snoc, Fin.msb_zero_of_lt h, Fin.lsbs_eq_of_lt h]

-- @[simp]
-- theorem Bit.toZMod_zero {n:ℕ} : Bit.toZMod (n:=n) Bit.zero = 0 := by rfl

-- @[simp]
-- theorem Bit.toZMod_one {n:ℕ} : Bit.toZMod (n:=n) Bit.one = 1 := by rfl

@[simp]
theorem Gates.is_zero_sub_one_iff_eq {n:ℕ} [Fact (n > 1)] {a b : ZMod n}: Gates.is_zero (Gates.sub a b) 1 ↔ a = b := by
  simp [Gates.is_zero, Gates.sub]
  apply Iff.intro <;> intro hp
  . exact eq_of_sub_eq_zero hp
  . exact sub_eq_zero_of_eq hp

theorem exists_vector_succ_iff_exists_snoc {α d} {pred : Vector α (Nat.succ d) → Prop}:
  (∃v, pred v) ↔ ∃vs v, pred (Vector.snoc vs v) := by
  apply Iff.intro
  . rintro ⟨v, hp⟩
    cases v using Vector.revCasesOn
    apply Exists.intro
    apply Exists.intro
    assumption
  . rintro ⟨vs, v, hp⟩
    exists vs.snoc v

@[simp]
theorem exists_eq_left₂ {pred : α → β → Prop}:
  (∃a b, (a = c ∧ b = d) ∧ pred a b) ↔ pred c d := by
  simp [and_assoc]

@[simp]
theorem Gates.is_zero_def {N} {a out : ZMod N} : Gates.is_zero a out ↔ out = Bool.toZMod (a = 0) := by
  simp [Gates.is_zero]
  apply Iff.intro
  . rintro (_ | _) <;> simp [*]
  . rintro ⟨_⟩
    simp [Bool.toZMod, Bool.toNat]
    tauto

@[simp]
theorem Gates.eq_def : Gates.eq a b ↔ a = b := by simp [Gates.eq]

@[simp]
theorem Bool.toZMod_eq_one_iff_eq_one {n:ℕ} [Fact (n > 1)] : (Bool.toZMod a : ZMod n) = 1 ↔ a = true := by
  cases a <;> simp

@[simp]
theorem Vector.snoc_eq : Vector.snoc xs x = Vector.snoc ys y ↔ xs = ys ∧ x = y := by
  apply Iff.intro
  . intro h
    have := congrArg Vector.reverse h
    simp at this
    injection this with this
    injection this with h t
    simp [*]
    apply Vector.eq
    have := congrArg List.reverse t
    simpa [this]
  . intro ⟨_, _⟩
    simp [*]

theorem MerkleTree.root_set_eq_recover_proof {α H d item index} {tree : MerkleTree α H d}:
  (set tree index item).root = recover H index (tree.proof index) item := by
  sorry

namespace Deletion

theorem deletionRoundCircuit_eq_deletionRoundSemantics [Fact (CollisionResistant poseidon₂)]:
  gDeletionRound tree.root index item proof k ↔ deletionRoundSemantics index item tree proof (fun t => k t.root) := by
  unfold gDeletionRound
  unfold deletionRoundSemantics
  rw [exists_vector_succ_iff_exists_snoc]
  simp only [Vector.getElem_snoc_before_length, Vector.getElem_snoc_at_length]
  conv =>
    pattern (occs := *) _ ::ᵥ _
    . change item ::ᵥ Vector.ofFn proof.get
    . change Vector.ofFn vs.get
    . change 0 ::ᵥ Vector.ofFn proof.get
  simp_rw [Vector.ofFn_get, Gates.to_binary_iff_eq_fin_to_bits_le_of_pow_length_lt]
  unfold Fin.toBitsLE
  unfold Fin.toBitsBE
  cases Decidable.em (index.val < 2^(D+1)) with
  | inl hlt =>
    simp [hlt]
    cases Nat.lt_or_ge index.val (2^D) with
    | inl hlt =>
      simp [hlt, VerifyProof_uncps, Gates.sub, sub_eq_zero, ←MerkleTree.recover_equivalence, MerkleTree.setAtFin, MerkleTree.proofAtFin, MerkleTree.root_set_eq_recover_proof]
      unfold MerkleTree.itemAtFin
      apply Iff.intro
      . rintro ⟨⟨a, b⟩, c⟩
        simp [*]
      . intro ⟨_, _, _⟩
        simp [*] at *
        assumption
    | inr hge =>
      have : ¬index.val < 2 ^ D := by linarith
      simp [this, hge, Vector.snoc_eq, VerifyProof_uncps, Gates.sub, sub_eq_zero]
  | inr hge => simp [hge]

def deletionRoundsSemantics {b : Nat}
  (indices : Vector F b)
  (items : Vector F b)
  (proofs : Vector (Vector F D) b)
  (tree : MerkleTree F poseidon₂ D)
  (k : F → Prop): Prop := match b with
  | Nat.zero => k tree.root
  | Nat.succ _ =>
    deletionRoundSemantics (indices.head) (items.head) tree (proofs.head) (fun t => deletionRoundsSemantics indices.tail items.tail proofs.tail t k)

theorem deletionProofCircuit_eq_deletionRoundsSemantics [Fact (CollisionResistant poseidon₂)]:
  gDeletionProof indices tree.root idComms proofs k ↔ deletionRoundsSemantics indices idComms proofs tree k := by
  unfold gDeletionProof
  repeat unfold deletionRoundsSemantics
  repeat (
    cases indices using Vector.casesOn; rename_i _ indices
    cases idComms using Vector.casesOn; rename_i _ idComms
    cases proofs using Vector.casesOn; rename_i _ proofs
  )
  simp_rw [deletionRoundCircuit_eq_deletionRoundSemantics]
  rfl

def treeTransformationSemantics {B : ℕ}
  (tree : MerkleTree F poseidon₂ D)
  (indices : Vector F B): Option (MerkleTree F poseidon₂ D) := match B with
  | 0 => some tree
  | _ + 1 => if h : indices.head.val < 2 ^ D
    then treeTransformationSemantics (tree.setAtFin ⟨indices.head.val, h⟩ 0) indices.tail
    else if indices.head.val < 2 ^ (D + 1)
      then treeTransformationSemantics tree indices.tail
      else none

theorem deletionRounds_rootTransformation {B : ℕ} {indices idComms : Vector F B} {proofs : Vector (Vector F D) B} {tree : MerkleTree F poseidon₂ D} {k : F → Prop}:
  deletionRoundsSemantics indices idComms proofs tree k →
  ∃postTree, treeTransformationSemantics tree indices = some postTree ∧ k postTree.root := by
  intro hp
  induction B generalizing tree with
  | zero => exists tree
  | succ B ih =>
    unfold deletionRoundsSemantics at hp
    unfold deletionRoundSemantics at hp
    split at hp
    . split at hp
      . rcases hp with ⟨-, -, hp⟩
        replace hp := ih hp
        unfold treeTransformationSemantics
        simp [*]
      . unfold treeTransformationSemantics
        replace hp := ih hp
        simp [*]
    . contradiction

theorem treeTransform_get_absent {B : ℕ} {i : F} {indices : Vector F B} {tree tree' : MerkleTree F poseidon₂ D}:
  treeTransformationSemantics tree indices = some tree' → i ∉ indices → tree'[i.val]? = tree[i.val]? := by
  intro hp hn
  induction B generalizing tree tree' with
  | zero => unfold treeTransformationSemantics at hp; injection hp; simp [*]
  | succ B ih =>
    unfold treeTransformationSemantics at hp
    have i_tail : i ∉ indices.tail := by
      intro h
      apply hn
      apply Vector.mem_of_mem_tail
      assumption
    split at hp
    . replace hp := ih hp i_tail
      rw [hp]; clear hp
      cases Nat.lt_or_ge i.val (2^D) with
      | inl _ =>
        repeat rw [getElem?_eq_some_getElem_of_valid_index] <;> try assumption
        apply congrArg
        apply MerkleTree.getElem_setAtFin_invariant_of_neq
        intro hp
        apply hn
        replace hp := Fin.eq_of_veq hp
        rw [hp]
        apply Vector.head_mem
      | inr _ =>
        repeat rw [getElem?_none_of_invalid_index]
        all_goals (apply not_lt_of_ge; assumption)
    . split at hp
      . exact ih hp i_tail
      . contradiction

theorem treeTranform_get_present {B : ℕ} {i : F} {indices : Vector F B} {tree tree' : MerkleTree F poseidon₂ D}:
  treeTransformationSemantics tree indices = some tree' → i ∈ indices → tree'[i.val]! = 0 := by
  intro hp hi
  induction B generalizing tree tree' with
  | zero => cases indices using Vector.casesOn; cases hi
  | succ B ih =>
    unfold treeTransformationSemantics at hp
    cases indices using Vector.casesOn; rename_i hix tix
    split at hp
    . rename_i range
      cases Decidable.em (i ∈ tix.toList) with
      | inl h => exact ih hp h
      | inr h =>
        rw [getElem!_eq_getElem?_get!]
        rw [treeTransform_get_absent hp h]
        cases eq_or_ne i hix with
        | inl heq =>
          cases heq
          rw [getElem?_eq_some_getElem_of_valid_index] <;> try exact range
          apply MerkleTree.read_after_insert_sound
        | inr hne => cases hi <;> contradiction
    . rename_i invalid
      cases List.eq_or_ne_mem_of_mem hi with
      | inl heq =>
        rw [getElem!_eq_getElem?_get!, getElem?_none_of_invalid_index]
        . rfl
        . rw [heq]; exact invalid
      | inr h =>
        rcases h with ⟨-, range⟩
        split at hp
        . exact ih hp range
        . contradiction

end Deletion
