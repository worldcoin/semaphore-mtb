import FormalVerification
import FormalVerification.ReducedCheck.Basic
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

lemma and_t {P : Prop}: P ↔ (P ∧ True) := by
  tauto

theorem ReducedModRCheck_256_Fold :
  ∀ (v : Vector F 256), binary_comparison_with_constant order_binary_le 255 (by decide) 0 0 v ↔ SemaphoreMTB.ReducedModRCheck_256 v := by
  intro v
  unfold SemaphoreMTB.ReducedModRCheck_256

  repeat (
    unfold binary_comparison_with_constant
    apply and_iff
    repeat (apply ex_iff; intro _; apply and_iff)
  )

  apply and_t


