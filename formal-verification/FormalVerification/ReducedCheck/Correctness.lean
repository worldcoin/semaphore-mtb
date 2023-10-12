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
    intro _ ⟨_, p⟩
    cases p
  | h_cons ih =>
    simp [is_vector_binary, ←ih]
    tauto

lemma nat_to_bit_zmod_val_eq_iff { v₁ v₂ : F } { bin₁ : is_bit v₁ } {bin₂ : is_bit v₂}:
  nat_to_bit v₁.val = nat_to_bit v₂.val ↔ v₁ = v₂ := by
  cases bin₁ <;> {
    cases bin₂ <;> {
      subst_vars; tauto
    }
  }

lemma vector_zmod_to_bit_eq_iff {v₁ v₂ : Vector F n} {bin₁ : is_vector_binary v₁} {bin₂ : is_vector_binary v₂}:
  vector_zmod_to_bit v₁ = vector_zmod_to_bit v₂ ↔ v₁ = v₂ := by
  induction v₁, v₂ using Vector.inductionOn₂ with
  | nil => simp
  | cons ih =>
    rw [is_vector_binary_cons] at bin₁ bin₂
    simp [Vector.eq_cons_iff]
    rw [ih (bin₁ := bin₁.2) (bin₂ := bin₂.2)]
    simp; intro
    cases bin₁.1 <;> { cases bin₂.1 <;> { subst_vars; tauto }}

lemma to_binary_reduced_unique:
  Gates.to_binary v 256 out₁ →
  SemaphoreMTB.ReducedModRCheck_256 out₁ →
  Gates.to_binary v 256 out₂ →
  SemaphoreMTB.ReducedModRCheck_256 out₂ →
  out₁ = out₂ := by
  rw [←ReducedModRCheck_256_Fold, ←ReducedModRCheck_256_Fold]
  intro ⟨rec₁, bin₁⟩ le₁ ⟨rec₂, bin₂⟩ le₂
  rw [binary_comp_unfold, order_binary_le_is_order] at le₁ le₂
  rw [recover_binary_zmod_bit bin₁, ←binary_nat_zmod_equiv] at rec₁
  rw [recover_binary_zmod_bit bin₂, ←binary_nat_zmod_equiv] at rec₂
  have rec₁ := congrArg ZMod.val rec₁
  have rec₂ := congrArg ZMod.val rec₂
  rw [ZMod.val_cast_of_lt (LT.lt.gt le₁)] at rec₁
  rw [ZMod.val_cast_of_lt (LT.lt.gt le₂)] at rec₂
  rw [←vector_zmod_to_bit_eq_iff (bin₁ := bin₁) (bin₂ := bin₂)]
  apply binary_nat_unique
  simp [*]
  all_goals (rw [old_vec_binary_equiv]; assumption)

def permute (fn : Fin n → Fin n) (v : Vector α n): Vector α n :=
  Vector.ofFn (fun i => v[fn i])

theorem permute_eq_iff {fn : Fin n → Fin n} { fun_inv : ∀i, ∃j, fn j = i } {v₁ v₂ : Vector α n}:
  permute fn v₁ = permute fn v₂ ↔ v₁ = v₂ := by
  apply Iff.intro
  . intro h
    ext i
    rcases fun_inv i with ⟨j, i_inv⟩
    have : (permute fn v₁).get j = (permute fn v₂).get j := by rw [h]
    simp [permute, getElem] at this
    subst_vars
    assumption
  . intros; congr

lemma mod_div_mul {i k : Nat}: i / k.succ * k.succ = i - i%k.succ := by
  apply Eq.symm
  apply Nat.sub_eq_of_eq_add
  apply Eq.symm
  rw [add_comm]
  apply Nat.mod_add_div'

def rev_ix (i : Nat) := 248 - (i / 8) * 8 + i % 8

theorem rev_ix_ok: rev_ix i < 256 := by
  unfold rev_ix
  calc
    248 - i/8*8 + i % 8 ≤ 248 + i % 8 := by simp_arith
    _ ≤ 248 + 7 := by simp_arith; apply Nat.le_of_lt_succ; apply Nat.mod_lt; trivial
    _ < 256 := by trivial

theorem sub_of_sub {a b c : Nat}: c ≤ b → b - c ≤ a → a - (b - c) = a + c - b := by
  intro h₁ h₂;
  induction c generalizing b with
  | zero => rfl
  | succ c ih =>
    cases b with
    | zero => cases h₁
    | succ b =>
      rw [Nat.succ_sub_succ] at *
      rw [ih, Nat.add_succ, Nat.succ_sub_succ]
      . simp_arith at h₁; assumption
      . assumption

theorem rev_rev_ix : i < 256 → rev_ix (rev_ix i) = i := by
  intro hp
  unfold rev_ix
  simp [mod_div_mul]
  simp_arith
  have i_div_8 : i / 8 ≤ 31 := by
    rw [Nat.div_le_iff_le_mul_add_pred (by simp)]
    simp_arith
    simp_arith at hp
    assumption
  have i_div_8_mul_8 : 8 * (i / 8) ≤ 248 := by
    apply Nat.mul_le_mul_left 8 i_div_8
  have : 248 - (i - i % 8) = 248 + i % 8 - i := by
    apply sub_of_sub
    . apply Nat.mod_le
    . rw [←mod_div_mul]
      simp_arith
      calc
        8 * (i / 8)  ≤ 8 * 31 := Nat.mul_le_mul_left 8 i_div_8
        _ = 248 := by simp
  simp_arith [this]
  have : 248 + i % 8 ≥ i := by
    conv => rhs; rw [←Nat.mod_add_div i 8]
    simp_arith [*]
  rw [Nat.sub_add_cancel this]
  rw [Nat.add_mod]
  have : 248 % 8 = 0 := by trivial
  simp [this]
  rw [sub_of_sub]
  simp
  rw [Nat.add_sub_add_left]
  rw [Nat.sub_add_cancel]
  . apply Nat.mod_le
  . apply GE.ge.le; assumption
  . rw [Nat.sub_le_iff_le_add]
    simp
    apply Nat.mod_le

def bytewise_be_transform (v : Vector α 256): Vector α 256 :=
  permute (fun i => ⟨rev_ix i, rev_ix_ok⟩) v

def bytewise_be_eq_iff {v₁ v₂ : Vector α 256}:
  bytewise_be_transform v₁ = bytewise_be_transform v₂ ↔ v₁ = v₂ := by
  apply permute_eq_iff
  intro i
  exists ⟨rev_ix i.val, rev_ix_ok⟩
  simp [rev_rev_ix]

lemma ToReducedBigEndian256_uncps v :
  SemaphoreMTB.ToReducedBigEndian_256 v k ↔
  ∃out, Gates.to_binary v 256 out ∧
  SemaphoreMTB.ReducedModRCheck_256 out ∧
  k (bytewise_be_transform out) := by
  unfold SemaphoreMTB.ToReducedBigEndian_256
  unfold bytewise_be_transform
  tauto

theorem to_reduced_big_endian_unique:
  SemaphoreMTB.ToReducedBigEndian_256 v (fun x => x = α) →
  SemaphoreMTB.ToReducedBigEndian_256 v (fun x => x = β) →
  α = β := by
  rw [ToReducedBigEndian256_uncps, ToReducedBigEndian256_uncps]
  intro ⟨out₁, bin₁, check₁, be₁⟩ ⟨out₂, bin₂, check₂, be₂⟩
  rw [←be₁, ←be₂, bytewise_be_eq_iff]
  exact to_binary_reduced_unique bin₁ check₁ bin₂ check₂