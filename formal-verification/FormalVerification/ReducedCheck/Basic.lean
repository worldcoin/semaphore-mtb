import ProvenZk.Gates
import ProvenZk.Binary
import FormalVerification

open SemaphoreMTB (F Order)
variable [Fact (Nat.Prime Order)]

abbrev order_binary_le : Vector Bool 256 := vec![true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,false,false,true,false,false,true,true,false,true,false,true,true,true,true,true,false,false,false,false,true,true,true,true,true,false,false,false,false,true,false,true,false,false,false,true,false,false,true,false,false,false,false,true,true,true,false,true,false,false,true,true,true,false,true,true,false,false,true,true,true,true,false,false,false,false,true,false,false,true,false,false,false,false,true,false,true,true,true,true,true,false,false,true,true,false,false,false,false,false,true,false,true,false,false,true,false,true,true,true,false,true,false,false,false,false,true,true,false,true,false,true,false,false,false,false,false,false,true,true,false,false,false,false,false,false,true,false,true,true,false,true,true,false,true,true,false,true,false,false,false,true,false,false,false,false,false,true,false,true,false,false,false,false,true,true,true,false,true,true,false,false,true,false,true,false,false,false,false,false,false,false,true,false,true,true,false,false,false,true,true,false,false,true,false,false,false,false,true,true,true,false,true,false,false,true,true,true,false,false,true,true,true,false,false,true,false,false,false,true,false,false,true,true,false,false,false,false,false,true,true,false,false]

def binary_comparison_with_constant
  (base : Vector Bool n)
  (start_ix : Nat)
  (ix_ok : start_ix < n)
  (succeeded : F)
  (failed : F)
  (arg : Vector F n): Prop :=
  Gates.is_bool arg[start_ix] ∧
  match base[start_ix] with
  | false =>
    ∃or, Gates.or arg[start_ix] failed or ∧
    ∃failed, Gates.select succeeded 0 or failed ∧
    match start_ix with
    | 0 => Gates.eq succeeded 1
    | Nat.succ start_ix => binary_comparison_with_constant base start_ix (Nat.lt_of_succ_lt ix_ok) succeeded failed arg
  | true =>
    ∃bit_neg, bit_neg = Gates.sub 1 arg[start_ix] ∧
    ∃or, Gates.or bit_neg succeeded or ∧
    ∃succeeded, Gates.select failed 0 or succeeded ∧
    match start_ix with
    | 0 => Gates.eq succeeded 1
    | Nat.succ start_ix => binary_comparison_with_constant base start_ix (Nat.lt_of_succ_lt ix_ok) succeeded failed arg

def binary_comparison_with_constant'
  (base : Vector Bool n)
  (start_ix : Nat)
  (ix_ok : start_ix < n)
  (succeeded : F)
  (failed : F)
  (arg : Vector F n): Prop :=
  Gates.is_bool arg[start_ix] ∧
  match base[start_ix] with
  | false =>
    let failed := if succeeded = 1 ∨ (failed = 0 ∧ arg[start_ix] = 0) then 0 else 1
    match start_ix with
    | 0 => succeeded = 1
    | Nat.succ start_ix => binary_comparison_with_constant' base start_ix (Nat.lt_of_succ_lt ix_ok) succeeded failed arg
  | true =>
    let succeeded' := if failed = 1 ∨ (succeeded = 0 ∧ arg[start_ix] = 1) then 0 else 1
    match start_ix with
    | 0 => succeeded' = 1
    | Nat.succ start_ix => binary_comparison_with_constant' base start_ix (Nat.lt_of_succ_lt ix_ok) succeeded' failed arg

theorem or_rw (a b out : F) : Gates.or a b out ↔
  (Gates.is_bool a ∧ Gates.is_bool b ∧
  ( (out = 1 ∧ (a = 1 ∨ b = 1) ∨
    (out = 0 ∧ a = 0 ∧ b = 0)))) := by
  unfold Gates.or
  unfold Gates.is_bool
  simp
  intro ha hb
  cases ha <;> cases hb <;> { subst_vars; simp }

@[simp]
lemma is_bool_1 : Gates.is_bool (1: F) := by
  unfold Gates.is_bool
  simp

@[simp]
lemma is_bool_0 : Gates.is_bool (0: F) := by
  unfold Gates.is_bool
  simp

lemma x {a : F}: 1 - a = 0 ↔ a = 1 := by
  rw [sub_eq_zero]; tauto


@[simp]
lemma is_bool_neg {a : F}: Gates.is_bool (1 - a) ↔ Gates.is_bool a := by
  unfold Gates.is_bool
  apply Iff.intro
  . intro h; cases h <;> (simp [sub_eq_zero, sub_eq_self] at *; tauto)
  . intro h; cases h <;> (subst_vars; tauto)

def binary_comparison_simpl {n} {base : Vector Bool n} {arg : Vector F n} {ix_ok : start_ix < n} {isbs : Gates.is_bool succeeded} {isbf : Gates.is_bool failed}:
  binary_comparison_with_constant base start_ix ix_ok succeeded failed arg ↔ binary_comparison_with_constant' base start_ix ix_ok succeeded failed arg := by
  induction start_ix generalizing succeeded failed with
  | zero =>
    unfold binary_comparison_with_constant
    unfold binary_comparison_with_constant'
    simp
    intro isb
    cases base[0] <;> {
      cases isb <;> {
        cases isbf <;> {
          cases isbs <;> {
            simp [*, or_rw, Gates.select, Gates.sub, Gates.eq]
          }
        }
      }
    }
  | succ ix ih =>
    unfold binary_comparison_with_constant
    unfold binary_comparison_with_constant'
    simp
    intro isb
    cases base[ix.succ] <;> {
      cases isb <;> {
        cases isbf <;> {
          cases isbs <;> {
            simp [*, or_rw, Gates.select, Gates.sub]
          }
        }
      }
    }

theorem failed_fails : ¬binary_comparison_with_constant base ix ix_ok 0 1 arg := by
  simp [binary_comparison_simpl]
  induction ix with
  | zero =>
    simp [binary_comparison_with_constant'];
    cases base[0] <;> { simp }
  | succ n ih =>
    rw [binary_comparison_with_constant'];
    cases base[Nat.succ n] <;> {
      simp [ih]
    }

@[simp]
lemma i_in_singleton : i ∈ [n:n + 1] ↔ i = n := by
  apply Iff.intro
  . intro h
    cases h
    linarith
  . intro h; apply And.intro <;> linarith

@[simp]
lemma for_i_in_singleton {P : (i : Nat) → i ∈ [0:1] → Prop} : (∀ i, (p : i ∈ [0:1]) → P i p)
  ↔ P 0 (by apply And.intro <;> linarith) := by
  apply Iff.intro
  . intro h; apply h 0
  . intro h i p; cases p; rename_i _ p; cases p
    . assumption
    . contradiction

-- @[simp]
lemma for_i_in_succ {n : Nat} { P : (i : Nat) → i ∈ [0 : n.succ + 1] → Prop} : (∀i, (p : i ∈ [0:n.succ + 1]) → P i p)
  ↔ ((P (n + 1) (by apply And.intro <;> linarith)) ∧
     (∀i, (p : i ∈ [0:n+1]) → P i (by cases p; apply And.intro <;> linarith))) := by
  apply Iff.intro
  . intro p;
    apply And.intro
    . exact p (n+1) (by apply And.intro <;> linarith)
    . intro i range
      apply p i (by cases range; apply And.intro <;> linarith)
  . intro h i range
    cases h ; rename_i hmax hrest
    cases range; rename_i range_bot range_top
    cases range_top
    . apply hmax
    . apply hrest
      apply And.intro
      . linarith
      . simp at *; linarith

theorem suceeded_suceeds {arg : Vector F n} : binary_comparison_with_constant base ix ix_ok 1 0 arg ↔ ∀ i, (p: i ∈ [0:ix+1]) → Gates.is_bool (arg[i]'(by cases p; linarith)) := by
  simp [binary_comparison_simpl]
  induction ix with
  | zero =>
    unfold binary_comparison_with_constant'
    cases base[0] <;> simp
  | succ n ih =>
    unfold binary_comparison_with_constant'
    cases base[Nat.succ n] <;> simp [ih, for_i_in_succ]

theorem only_binary {arg : Vector F n} :
  Gates.is_bool s →
  Gates.is_bool f →
  binary_comparison_with_constant base ix ix_ok s f arg →
  ∀ i, (p: i ∈ [0:ix+1]) → Gates.is_bool (arg[i]'(by cases p; linarith)) := by
  intro bools boolf
  rw [binary_comparison_simpl] <;> try assumption
  induction ix generalizing s f with
  | zero =>
    unfold binary_comparison_with_constant'
    cases base[0] <;> {simp; tauto}
  | succ n ih =>
    unfold binary_comparison_with_constant'
    cases base[Nat.succ n] <;> {
      intro recur
      simp at recur; cases recur; rename_i _ recur
      simp [for_i_in_succ]
      apply And.intro
      . assumption
      . apply ih
        case a => exact recur
        all_goals ((try split) <;> simp [*])
    }

def bit_cmp (base_bit : Bool) (arg_bit : F): Option Ordering := match base_bit with
  | false => match arg_bit with
    | 0 => some Ordering.eq
    | 1 => some Ordering.lt
    | _ => none
  | true => match arg_bit with
    | 0 => some Ordering.gt
    | 1 => some Ordering.eq
    | _ => none

-- -- def binary_comparison_ctrl_flow (base : Vector Bool n) (start_ix : Nat) (ix_ok : start_ix < n) := sorry

def binary_comparison_ix_free (base : Vector Bool n) (arg : Vector F n): Prop := match n with
| 0 => False
| Nat.succ _ => match bit_cmp base.head arg.head with
  | none => False
  | some Ordering.lt => False
  | some Ordering.gt => True
  | some Ordering.eq => binary_comparison_ix_free base.tail arg.tail

-- @[simp]
-- theorem reverse_nil : Vector.reverse (Vector.nil : Vector α 0) = Vector.nil := by
--   rfl

-- @[simp]
-- theorem vector_get_head : (v ::ᵥ vs)[0] = v := by
--   rfl

-- @[simp]
-- theorem vector_get_next (vs : Vector α (Nat.succ n)) : (v ::ᵥ vs)[Nat.succ n] = vs[n] := by
--   rfl

-- @[simp]
-- lemma snoc_get_last {n : Nat} (vs : Vector α n) : (vs.snoc v)[n] = v := by
--   induction n with
--   | zero =>
--     cases vs using Vector.casesOn
--     rfl
--   | succ n ih =>
--     cases vs using Vector.casesOn
--     simp [ih]

-- theorem binary_comp_cf : ∀ (base : Vector Bool (Nat.succ n)) (arg : Vector F (Nat.succ n)),
--   binary_comparison_with_constant base n (by simp) 0 0 arg ↔
--   (binary_comparison_ix_free base.reverse arg.reverse ∧ ∀ i, (i_ok : i ∈ [0 : (Nat.succ n)]) →  Gates.is_bool (arg[i]'(by cases i_ok; linarith))) := by
--   induction n with
--   | zero =>
--     intro base arg
--     cases base using Vector.casesOn; rename_i bhd btl
--     cases btl using Vector.casesOn
--     cases arg using Vector.casesOn; rename_i ahd atl
--     cases atl using Vector.casesOn
--     simp [binary_comparison_with_constant, binary_comparison_ix_free]
--     apply Iff.intro
--     . intro h
--       cases h; rename_i bool cmp
--       cases bool <;>  {
--         rename_i bool;
--         conv at bool => lhs; whnf
--         subst_vars
--         conv at cmp => whnf
--         cases bhd <;> simp at cmp
--         . casesm* (∃ _, _), (_ ∧ _), Gates.eq _ _
--         . unfold bit_cmp
--           conv => whnf
--           sorry
--       }
--     . intro h
--       cases ahd; rename_i v p;
--       cases bhd with
--       | false => cases v with
--         | zero => simp [bit_cmp] at h
--         | succ v => cases v with
--           | zero => sorry
--           | succ _ => sorry
--       | true => cases v with
--        | zero => sorry
--        | succ v => sorry

--   | succ n ih =>
--     intro base arg
--     cases base using Vector.revCasesOn; rename_i bhd btl
--     cases arg using Vector.revCasesOn; rename_i ahd atl
--     rw [binary_comparison_ix_free, binary_comparison_with_constant]
--     simp [←ih]



