import FormalVerification
import FormalVerification.BinaryReps.Basic
import ProvenZk.Gates

open SemaphoreMTB (F Order)

variable [Fact (Nat.Prime Order)]

lemma and_iff (P Q R : Prop): (Q ↔ R) → (P ∧ Q ↔ P ∧ R) := by
  tauto

lemma ex_iff {P Q : α → Prop}: (∀x, P x ↔ Q x) → ((∃x, P x) ↔ ∃x, Q x) := by
  intro h;
  apply Iff.intro <;> {
    intro h1
    cases h1; rename_i witness prop
    exists witness
    try { rw [h witness]; assumption }
    try { rw [←h witness]; assumption }
  }

theorem allIxes_indexed' {v : SubVector α n prop} {i : Nat} {i_small : i < n}:
  prop (v.val[i]'i_small) ↔ True := by simp; exact v.prop ⟨i, i_small⟩

lemma lemma1 {v : SubVector F n is_bit} {i : Nat} {i_small : i < n}:
  (P ↔ Q) → (P ↔ Gates.is_bool (v.val[i]'i_small) ∧ Q) := by
  rw [is_bool_is_bit, allIxes_indexed' (prop := is_bit), true_and]
  exact id

theorem ReducedModRCheck_256_Fold :
  ∀ (v : SubVector F 256 is_bit), binary_comparison_with_constant order_binary_le v ⟨255, by decide⟩  0 0 ↔ SemaphoreMTB.ReducedModRCheck_256 v := by
  intro v
  unfold SemaphoreMTB.ReducedModRCheck_256

  repeat (
    apply lemma1
    repeat (apply ex_iff; intro _; apply and_iff)
  )

  tauto
