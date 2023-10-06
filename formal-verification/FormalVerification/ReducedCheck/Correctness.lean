import FormalVerification.ReducedCheck.Basic
import FormalVerification.ReducedCheck.SemanticEquivalence
import ProvenZk.Gates
import FormalVerification

open SemaphoreMTB (F Order)
variable [Fact (Nat.Prime Order)]

lemma old_vec_binary_equiv : vector_binary v ↔ is_vector_binary v := by
  induction v using Vector.inductionOn with
  | h_nil =>
    simp [is_vector_binary, vector_binary]
    intro i p
    cases p; rename_i _ r; cases r
  | @h_cons _ h t ih =>
    simp [is_vector_binary, ←ih]
    tauto

lemma to_binary_reduced_unique:
  Gates.to_binary v 256 out₁ →
  SemaphoreMTB.ReducedModRCheck_256 out₁ →
  Gates.to_binary v 256 out₂ →
  SemaphoreMTB.ReducedModRCheck_256 out₂ →
  out₁ = out₂ := by
  intro bin₁ red₁ bin₂ red₂

  have : vector_binary out₁ := by
    cases bin₁
    simp [*, old_vec_binary_equiv]

  simp [←ReducedModRCheck_256_Fold] at *
  rw [binary_comp_ix_free_simp _ _ this] at red₁
  rw [←bit_comparison] at red₁



theorem reducedBigEndianUnique:
  SemaphoreMTB.ToReducedBigEndian_256 v (fun x => x = α) →
  SemaphoreMTB.ToReducedBigEndian_256 v (fun x => x = β) →
  α = β := by sorry
  -- simp [SemaphoreMTB.ToReducedBigEndian_256]

