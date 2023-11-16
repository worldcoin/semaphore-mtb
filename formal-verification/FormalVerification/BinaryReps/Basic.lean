import ProvenZk.Gates
import ProvenZk.Binary
import ProvenZk.Subvector
import ProvenZk.Ext.Vector
import ProvenZk.Misc
import FormalVerification
import FormalVerification.Utils

open SemaphoreMTB (F Order)

abbrev order_binary_le : SubVector F 256 is_bit := SubVector.lift vec![bOne,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bOne,bOne,bOne,bOne,bOne,bOne,bZero,bZero,bOne,bZero,bZero,bOne,bOne,bZero,bOne,bZero,bOne,bOne,bOne,bOne,bOne,bZero,bZero,bZero,bZero,bOne,bOne,bOne,bOne,bOne,bZero,bZero,bZero,bZero,bOne,bZero,bOne,bZero,bZero,bZero,bOne,bZero,bZero,bOne,bZero,bZero,bZero,bZero,bOne,bOne,bOne,bZero,bOne,bZero,bZero,bOne,bOne,bOne,bZero,bOne,bOne,bZero,bZero,bOne,bOne,bOne,bOne,bZero,bZero,bZero,bZero,bOne,bZero,bZero,bOne,bZero,bZero,bZero,bZero,bOne,bZero,bOne,bOne,bOne,bOne,bOne,bZero,bZero,bOne,bOne,bZero,bZero,bZero,bZero,bZero,bOne,bZero,bOne,bZero,bZero,bOne,bZero,bOne,bOne,bOne,bZero,bOne,bZero,bZero,bZero,bZero,bOne,bOne,bZero,bOne,bZero,bOne,bZero,bZero,bZero,bZero,bZero,bZero,bOne,bOne,bZero,bZero,bZero,bZero,bZero,bZero,bOne,bZero,bOne,bOne,bZero,bOne,bOne,bZero,bOne,bOne,bZero,bOne,bZero,bZero,bZero,bOne,bZero,bZero,bZero,bZero,bZero,bOne,bZero,bOne,bZero,bZero,bZero,bZero,bOne,bOne,bOne,bZero,bOne,bOne,bZero,bZero,bOne,bZero,bOne,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bOne,bZero,bOne,bOne,bZero,bZero,bZero,bOne,bOne,bZero,bZero,bOne,bZero,bZero,bZero,bZero,bOne,bOne,bOne,bZero,bOne,bZero,bZero,bOne,bOne,bOne,bZero,bZero,bOne,bOne,bOne,bZero,bZero,bOne,bZero,bZero,bZero,bOne,bZero,bZero,bOne,bOne,bZero,bZero,bZero,bZero,bZero,bOne,bOne,bZero,bZero]

def binary_comparison_with_constant
  (base arg : SubVector F n is_bit)
  (start_ix : Fin n)
  (succeeded : F)
  (failed : F): Prop :=
  match bitCases base[start_ix] with
  | Bit.zero =>
    ∃or, Gates.or arg[start_ix] failed or ∧
    ∃failed, Gates.select succeeded 0 or failed ∧
    match start_ix with
    | ⟨ 0, _⟩  => Gates.eq succeeded 1
    | ⟨Nat.succ ix, p⟩ => binary_comparison_with_constant base arg ⟨ix, Nat.lt_of_succ_lt p⟩ succeeded failed
  | Bit.one =>
    ∃bit_neg, bit_neg = Gates.sub 1 arg[start_ix] ∧
    ∃or, Gates.or bit_neg succeeded or ∧
    ∃succeeded, Gates.select failed 0 or succeeded ∧
    match start_ix with
    | ⟨0, _⟩ => Gates.eq succeeded 1
    | ⟨Nat.succ start_ix, p⟩ => binary_comparison_with_constant base arg ⟨start_ix, Nat.lt_of_succ_lt p⟩ succeeded failed

lemma binary_comparison_with_constant_unused_snoc {base arg : SubVector F n is_bit} {b a : Subtype is_bit} {i : Fin n}:
  binary_comparison_with_constant (base.snoc b) (arg.snoc a) i.castSucc succeeded failed ↔
  binary_comparison_with_constant base arg i succeeded failed := by
  cases n
  case zero => cases i using finZeroElim
  induction i using Fin.inductionOn generalizing succeeded failed with
  | h0 =>
    unfold binary_comparison_with_constant
    simp [SubVector.snoc, GetElem.getElem, Vector.head_snoc]
    rfl
  | hs i ih =>
    unfold binary_comparison_with_constant
    simp [SubVector.snoc, GetElem.getElem, Vector.head_snoc]
    conv at ih => intro succeeded failed; rhs; arg 3; whnf
    conv => rhs; simp [Fin.succ, ←ih]

lemma binary_comparison_failed_always_fails {base arg : SubVector F n is_bit}
  {i : Fin n}:
  ¬binary_comparison_with_constant base arg i 0 1 := by
  rcases i with ⟨i, p⟩
  induction i <;> {
    unfold binary_comparison_with_constant
    split <;> { simp [Gates.eq, *] }
  }

lemma binary_comparison_succeeded_always_succeeds {base arg : SubVector F n is_bit}
  {i : Fin n}:
  binary_comparison_with_constant base arg i 1 0 := by
  rcases i with ⟨i, p⟩
  induction i <;> {
    unfold binary_comparison_with_constant
    split <;> simp [Gates.eq, Subtype.property, *]
  }

lemma recover_binary_nat_snoc {n : Nat} {v : Vector Bit n} {b : Bit}:
  recover_binary_nat (v.snoc b) = recover_binary_nat v + 2^n * b.toNat := by
  induction n with
  | zero =>
    cases v using Vector.casesOn
    simp [recover_binary_nat]
  | succ n ih =>
    cases v using Vector.casesOn with | cons hd tl =>
    unfold recover_binary_nat
    simp [ih]
    rw [Nat.add_assoc,
        Nat.add_left_cancel_iff,
        Nat.mul_add,
        Nat.add_left_cancel_iff,
        Nat.mul_left_comm,
        ← Nat.mul_assoc,
        Nat.pow_succ
    ]

theorem binary_comparison_with_constant_is_comparison {base arg : SubVector F (Nat.succ n) is_bit }:
  recover_binary_nat (Vector.map bitCases base.lower) > recover_binary_nat (Vector.map bitCases arg.lower) ↔
  binary_comparison_with_constant base arg ⟨n, by simp⟩ 0 0 := by
  induction n with
  | zero =>
    unfold SubVector.lower
    unfold binary_comparison_with_constant
    simp [Gates.eq, Gates.sub, Vector.ofFn, recover_binary_nat]
    split
    . rename_i h
      simp [h, Bit.toNat]
    . rename_i h
      simp [h, Bit.toNat, Subtype.property]
      split <;> {
        simp only [bitCases_eq_0, bitCases_eq_1] at *
        simp [*]
      }
  | succ n ih =>
    cases base using SubVector.revCases with | snoc binit blast =>
    cases arg using SubVector.revCases with | snoc ainit alast =>
    unfold binary_comparison_with_constant
    have {p} : Fin.mk (n := n.succ.succ) n p = Fin.castSucc (Fin.last n) := by
      simp [Fin.castSucc, Fin.last]
    simp only [Subtype.property, this, binary_comparison_with_constant_unused_snoc]
    conv => lhs; simp only [SubVector.snoc_lower, Vector.map_snoc, recover_binary_nat_snoc]
    conv => rhs; simp only [GetElem.getElem, Fin.last_def, SubVector.snoc, Vector.vector_get_snoc_last]
    cases isBitCases blast with
    | inl =>
      cases isBitCases alast with
      | inl =>
        subst_vars
        simp [ih, Fin.last_def]
      | inr =>
        subst_vars
        simp [binary_comparison_failed_always_fails, Bit.toNat]
        calc
          recover_binary_nat (Vector.map bitCases (SubVector.lower binit)) ≤ 2 ^ Nat.succ n :=
            by apply le_of_lt; apply binary_nat_lt
          _ ≤ recover_binary_nat (Vector.map bitCases (SubVector.lower ainit)) + 2 ^ Nat.succ n :=
            by linarith
    | inr =>
      cases isBitCases alast with
      | inl =>
        subst_vars
        simp [Gates.sub, binary_comparison_succeeded_always_succeeds, Bit.toNat]
        calc
          recover_binary_nat (Vector.map bitCases (SubVector.lower ainit)) < 2 ^ Nat.succ n :=
            by apply binary_nat_lt
          _ ≤ recover_binary_nat (Vector.map bitCases (SubVector.lower binit)) + 2 ^ Nat.succ n :=
            by linarith
      | inr =>
        subst_vars
        simp [Gates.sub, ih, Fin.last_def]

theorem recover_order_binary_le_is_order :
  recover_binary_nat (Vector.map bitCases order_binary_le.lower) = Order := by
  rfl
