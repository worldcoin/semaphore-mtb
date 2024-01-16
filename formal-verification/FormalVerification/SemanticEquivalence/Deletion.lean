import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Misc

import FormalVerification
import FormalVerification.Utils
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness

import FormalVerification.SemanticEquivalence.Verification

open SemaphoreMTB (F Order)

open SemaphoreMTB renaming DeletionRound_30_30 → gDeletionRound
open SemaphoreMTB renaming DeletionProof_4_4_30_4_4_30 → gDeletionProof
open SemaphoreMTB renaming VerifyProof_31_30 → gVerifyProof


-- Deletion round semantic equivalence

-- def insertionRoundSemantics (Index Item : F) (Tree : MerkleTree F poseidon₂ D) (Proof : Vector F D) (k : MerkleTree F poseidon₂ D → Prop): Prop :=
--   if h : Index.val < 2 ^ D then
--     Tree.itemAtFin ⟨Index.val, h⟩ = 0 ∧
--     Tree.proofAtFin ⟨Index.val, h⟩ = Proof.reverse ∧
--     k (Tree.setAtFin ⟨Index.val, h⟩ Item)
--   else False

def deletionRoundSemantics (Index Item : F) (Tree : MerkleTree F poseidon₂ D) (Proof : Vector F D) (k : MerkleTree F poseidon₂ D → Prop): Prop :=
  if Index.val < 2 ^ (D + 1)
    then if h : Index.val < 2 ^ D
      then Tree.itemAtFin ⟨Index.val, h⟩ = Item ∧
           Tree.proofAtFin ⟨Index.val, h⟩ = Proof.reverse ∧
           k (Tree.setAtFin ⟨Index.val, h⟩ 0)
      else k Tree
    else False

theorem Gates.to_binary_rangecheck {a : F} {n out} (h: to_binary a n out): a.val < 2^n := by
  unfold to_binary at h
  rcases h with ⟨h, hbin⟩
  cases Nat.lt_or_ge (2^n) Order with
  | inl hp =>
    have h := congrArg ZMod.val h
    rw [recover_binary_zmod_bit hbin, binary_zmod_same_as_nat _ hp] at h
    rw [←h]
    exact binary_nat_lt _
  | inr hp =>
    calc
      a.val < Order := a.prop
      _ ≤ 2^n := by linarith

theorem recover_binary_nat_snoc {n} {vs : Vector Bit n} :
  recover_binary_nat (Vector.snoc vs v) = recover_binary_nat vs + (2 ^ vs.length) * v.toNat := by
  induction n generalizing v with
  | zero =>
    cases vs using Vector.casesOn
    cases v <;> rfl
  | succ n ih =>
    cases vs using Vector.casesOn
    unfold recover_binary_nat
    simp [ih, Vector.length, Nat.pow_succ]
    rw [add_assoc]
    apply congrArg
    rw [left_distrib]
    apply congrArg
    conv => lhs; rw [mul_comm, mul_assoc]
    rw [mul_assoc]
    apply congrArg
    rw [mul_comm]


theorem recover_binary_zmod'_snoc {n} {vs : Vector (ZMod (Nat.succ p)) n} {v}:
  recover_binary_zmod' (Vector.snoc vs v) = recover_binary_zmod' vs + (2 ^ vs.length) * v.val := by
  induction n generalizing v with
  | zero =>
    cases vs using Vector.casesOn
    simp [recover_binary_zmod']
  | succ n ih =>
    cases vs using Vector.casesOn
    unfold recover_binary_zmod'
    simp [Vector.length, pow_succ, ih]
    ring

-- theorem Vector.map_snoc {n} {α β} {f : α → β} {vs : Vector α n} {v : α} :
--   Vector.map f (Vector.snoc vs v) = Vector.snoc (Vector.map f vs) (f v) := by
--   induction n generalizing vs with
--   | zero =>
--     cases vs using Vector.casesOn
--     cases v <;> rfl
--   | succ n ih =>
--     cases vs using Vector.casesOn
--     simp [Vector.map]
--     rw [ih]
--     simp [Vector.map]

-- todo name
-- lemma recover_lemma_proof_det {α H d} [Fact (CollisionResistant H)] {tree : MerkleTree α H d} {proof ixbin ix item}:
--     MerkleTree.recover_tail H (Dir.create_dir_vec ixbin) proof item = tree.root →
--     proof = tree.proofAtFin ix := by sorry


lemma Fin.castNat_lt_pow {n k : ℕ} (h : n < 2^k) : ↑n = Fin.mk n h := by
  apply Fin.eq_of_veq
  exact Nat.mod_eq_of_lt h

lemma Vector.getElem_snoc_at_length {vs : Vector α n}: (vs.snoc v)[n]'(by simp_arith) = v := by
  sorry

lemma Vector.getElem_snoc_before_length {vs : Vector α n} {i : ℕ} (hp : i < n): (vs.snoc v)[i]'(by linarith) = vs[i]'hp := by
  sorry

lemma is_vector_binary_snoc {vs : Vector (ZMod (Nat.succ p)) n} {v}: is_vector_binary (vs.snoc v) ↔ is_vector_binary vs ∧ is_bit v := by sorry

-- lemma Vector.ofFn_get_castAdd {v : Vector α (a + b)} : Vector.ofFn (fun i => v.get (i.castAdd b)) = v.take a := by sorry

theorem deletionRoundCircuit_eq_deletionRoundSemantics [Fact (CollisionResistant poseidon₂)]:
  gDeletionRound tree.root index item proof k ↔ deletionRoundSemantics index item tree proof (fun t => k t.root) := by
  unfold gDeletionRound
  unfold deletionRoundSemantics
  apply Iff.intro
  . intro hp
    rcases hp with ⟨ixbin, hixbin, rest⟩
    cases ixbin using Vector.revCasesOn with | snoc ixbin ctrlBit =>
    simp only [Vector.getElem_snoc_at_length, Vector.getElem_snoc_before_length] at *
    conv at rest =>
      congr
      . change (item ::ᵥ  Vector.ofFn proof.get); simp only [Vector.ofFn_get]
      . change (Vector.ofFn ixbin.get); simp only [Vector.ofFn_get]
      . intro gate_1
        congr
        . change (0 ::ᵥ Vector.ofFn proof.get); simp only [Vector.ofFn_get]
        . change (Vector.ofFn ixbin.get); simp only [Vector.ofFn_get]
    split; rotate_left
    . have := Gates.to_binary_rangecheck hixbin
      contradiction
    . rcases hixbin with ⟨hIxRecover, hIxIsBin⟩
      rw [recover_binary_zmod'_snoc] at hIxRecover
      rw [is_vector_binary_snoc] at hIxIsBin
      rcases hIxIsBin with ⟨hIxIsBin, hCtrlBitIsBit⟩
      rw [VerifyProof_uncps] at rest
      rcases rest with ⟨-, rest⟩
      rw [VerifyProof_uncps] at rest
      rcases rest with ⟨-, rest⟩
      rcases rest with ⟨gate_3, gate_3_def, rest⟩
      simp only [gate_3_def] at rest
      clear gate_3_def gate_3
      rcases rest with ⟨gate_4, gate_4_def, gate_5, gate_5_def, gate_5_eq, gate_7, gate_7_def, hcont⟩
      cases hCtrlBitIsBit with
      | inl hz =>
        cases hz
        simp at hIxRecover
        have : index.val < 2^D := by
          rw [←hIxRecover, @recover_binary_zmod_bit _ _ ⟨by decide⟩ _ hIxIsBin, binary_zmod_same_as_nat _ (by decide)]
          exact binary_nat_lt _
        simp only [this, dite_true]
        simp at gate_7_def
        simp only [gate_7_def] at *
        clear gate_7_def gate_7
        simp at gate_5_def
        rcases gate_5_def with ⟨-, gate_5_def⟩
        simp only [gate_5_def] at *
        clear gate_5_def gate_5
        unfold Gates.eq at gate_5_eq
        simp only [gate_5_eq] at *
        clear gate_5_eq
        simp [Gates.is_zero, Gates.sub] at gate_4_def
        replace gate_4_def := eq_of_sub_eq_zero gate_4_def
        rw [MerkleTree.recover_tail_equals_recover_reverse, ←Dir.recover_binary_zmod'_to_dir this (by decide) hIxIsBin hIxRecover, Fin.castNat_lt_pow this] at gate_4_def hcont
        refine ⟨?_, ?_, ?_⟩
        . apply MerkleTree.proof_ceritfies_item
          exact gate_4_def
        . apply MerkleTree.recover_proof_reversible
          exact gate_4_def
        . unfold MerkleTree.setAtFin
          rw [←MerkleTree.proof_insert_invariant _ _ _ _ _ gate_4_def]
          exact hcont
      | inr hz => sorry
  . sorry
