import ProvenZk.Gates
import ProvenZk.Binary
import FormalVerification

open SemaphoreMTB (F Order)
variable [Fact (Nat.Prime Order)]

abbrev order_binary_le : Vector Bit 256 := vec![Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.one,Bit.one,Bit.one,Bit.one,Bit.one,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.one,Bit.one,Bit.zero,Bit.one,Bit.zero,Bit.one,Bit.one,Bit.one,Bit.one,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.one,Bit.one,Bit.one,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.one,Bit.one,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.one,Bit.one,Bit.one,Bit.zero,Bit.one,Bit.one,Bit.zero,Bit.zero,Bit.one,Bit.one,Bit.one,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.one,Bit.one,Bit.one,Bit.one,Bit.one,Bit.zero,Bit.zero,Bit.one,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.one,Bit.one,Bit.one,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.one,Bit.zero,Bit.one,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.one,Bit.one,Bit.zero,Bit.one,Bit.one,Bit.zero,Bit.one,Bit.one,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.one,Bit.one,Bit.zero,Bit.one,Bit.one,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.one,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.one,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.one,Bit.one,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.one,Bit.one,Bit.one,Bit.zero,Bit.zero,Bit.one,Bit.one,Bit.one,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.zero,Bit.zero,Bit.one,Bit.one,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.zero,Bit.one,Bit.one,Bit.zero,Bit.zero]

instance : DecidableEq Bit
| Bit.zero, Bit.zero => isTrue rfl
| Bit.one, Bit.one   => isTrue rfl
| Bit.zero, Bit.one  => isFalse (fun h => by cases h)
| Bit.one, Bit.zero  => isFalse (fun h => by cases h)


def binary_comparison_with_constant
  (base : Vector Bit n)
  (start_ix : Nat)
  (ix_ok : start_ix < n)
  (succeeded : F)
  (failed : F)
  (arg : Vector F n): Prop :=
  Gates.is_bool arg[start_ix] ∧
  match base[start_ix] with
  | Bit.zero =>
    ∃or, Gates.or arg[start_ix] failed or ∧
    ∃failed, Gates.select succeeded 0 or failed ∧
    match start_ix with
    | 0 => Gates.eq succeeded 1
    | Nat.succ start_ix => binary_comparison_with_constant base start_ix (Nat.lt_of_succ_lt ix_ok) succeeded failed arg
  | Bit.one =>
    ∃bit_neg, bit_neg = Gates.sub 1 arg[start_ix] ∧
    ∃or, Gates.or bit_neg succeeded or ∧
    ∃succeeded, Gates.select failed 0 or succeeded ∧
    match start_ix with
    | 0 => Gates.eq succeeded 1
    | Nat.succ start_ix => binary_comparison_with_constant base start_ix (Nat.lt_of_succ_lt ix_ok) succeeded failed arg

def binary_comparison_with_constant'
  (base : Vector Bit n)
  (start_ix : Nat)
  (ix_ok : start_ix < n)
  (succeeded : Bool)
  (failed : Bool)
  (arg : Vector Bit n): Prop :=
  match base[start_ix] with
  | Bit.zero =>
    let failed := ¬succeeded ∧ (failed ∨ arg[start_ix] = Bit.one)
    match start_ix with
    | 0 => succeeded
    | Nat.succ start_ix => binary_comparison_with_constant' base start_ix (Nat.lt_of_succ_lt ix_ok) succeeded failed arg
  | Bit.one =>
    let succeeded := ¬failed ∧ (succeeded ∨ arg[start_ix] = Bit.zero)
    match start_ix with
    | 0 => succeeded
    | Nat.succ start_ix => binary_comparison_with_constant' base start_ix (Nat.lt_of_succ_lt ix_ok) succeeded failed arg

-- @[simp]
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

@[simp]
lemma is_bool_1_sub {a : F}: Gates.is_bool (Gates.sub 1 a) ↔ Gates.is_bool a := by
  unfold Gates.is_bool
  unfold Gates.sub
  apply Iff.intro
  . intro h; cases h <;> (simp [sub_eq_zero, sub_eq_self] at *; tauto)
  . intro h; cases h <;> (subst_vars; tauto)

abbrev bool_to_F : Bool → F
| false => 0
| true => 1

abbrev bit_to_F : Bit → F
| Bit.zero => 0
| Bit.one => 1

@[simp]
lemma bool_is_bool (b : Bool) : Gates.is_bool (bool_to_F b) := by
  cases b <;> simp [bool_to_F, Gates.is_bool]

@[simp]
lemma bit_is_bool (b : Bit) : Gates.is_bool (bit_to_F b) := by
  cases b <;> simp [bit_to_F, Gates.is_bool]

@[simp]
theorem vector_get_next (vs : Vector α (Nat.succ n)) : (v ::ᵥ vs)[Nat.succ n] = vs[n] := by
  rfl

@[simp]
theorem vector_get_cons_succ {vs : Vector α n} { ix_ok : Nat.succ i < Nat.succ n}:
  (v ::ᵥ vs)[Nat.succ i]'ix_ok = vs[i]'(by linarith) := by
  rfl

-- theorem succ_lt_succ : Nat.succ a < Nat.succ b ↔ a < b := by
--   apply Iff.intro <;> { intro h; linarith}

@[simp]
lemma vector_map_get {v : Vector α n} {ix_ok : i < n} : (v.map f)[i] = f (v[i]) := by
  induction v using Vector.inductionOn generalizing i with
  | h_nil => cases ix_ok
  | h_cons ih =>
    cases i with
    | zero => rfl
    | succ i => simp [ih]

@[simp]
lemma sub_is_not : Gates.sub 1 (bool_to_F b) = bool_to_F ¬b := by
  cases b <;> simp [Gates.sub, bool_to_F]

def flip_bit (b : Bit) : Bit := match b with
  | Bit.zero => Bit.one
  | Bit.one => Bit.zero

@[simp]
lemma sub_is_bit_not : Gates.sub 1 (bit_to_F b) = bit_to_F (flip_bit b) := by
  cases b <;> simp [Gates.sub, bit_to_F, flip_bit]

@[simp]
lemma flip_bit_one : flip_bit a = Bit.one ↔ a = Bit.zero := by
  cases a <;> simp [flip_bit]

@[simp]
lemma flip_bit_zero : flip_bit a = Bit.zero ↔ a = Bit.one := by
  cases a <;> simp [flip_bit]

@[simp]
lemma bool_to_F_eq_1 : bool_to_F b = 1 ↔ b = true := by
  cases b <;> simp [bool_to_F]

@[simp]
lemma bool_to_F_eq_0 : bool_to_F b = 0 ↔ b = false := by
  cases b <;> simp [bool_to_F]

@[simp]
lemma bit_to_F_eq_1 : bit_to_F b = 1 ↔ b = Bit.one := by
  cases b <;> simp [bit_to_F]

@[simp]
lemma bit_to_F_eq_0 : bit_to_F b = 0 ↔ b = Bit.zero := by
  cases b <;> simp [bit_to_F]

@[simp]
lemma select_bool : Gates.select (bool_to_F b) ifT ifF out ↔ out = if b then ifT else ifF := by
  cases b <;> simp [Gates.select, bool_to_F]

@[simp]
lemma gates_eq : Gates.eq a b ↔ a = b := by simp [Gates.eq]

@[simp]
lemma exists_gates_or {k : F -> Prop} : (∃or, Gates.or a b or ∧ k or) ↔ (Gates.is_bool a ∧ Gates.is_bool b ∧ k (if (a = 0 ∧ b = 0) then 0 else 1)) := by
  sorry

def binary_comparison_simpl {n} {base arg : Vector Bit n} {ix_ok : start_ix < n}:
  binary_comparison_with_constant base start_ix ix_ok (bool_to_F succeeded) (bool_to_F failed) (arg.map bit_to_F) ↔
  binary_comparison_with_constant' base start_ix ix_ok succeeded failed arg := by
  induction start_ix generalizing succeeded failed with
  | zero =>
    unfold binary_comparison_with_constant
    unfold binary_comparison_with_constant'
    rw [exists_gates_or]
    split
    . simp
    . simp; split
      . 

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

-- theorem failed_fails : ¬binary_comparison_with_constant' base ix ix_ok 0 1 arg := by
--   induction ix with
--   | zero =>
--     simp [binary_comparison_with_constant'];
--     cases base[0] <;> { simp }
--   | succ n ih =>
--     rw [binary_comparison_with_constant'];
--     cases base[Nat.succ n] <;> {
--       simp [ih]
--     }

-- @[simp]
-- lemma i_in_singleton : i ∈ [n:n + 1] ↔ i = n := by
--   apply Iff.intro
--   . intro h
--     cases h
--     linarith
--   . intro h; apply And.intro <;> linarith

-- @[simp]
-- lemma for_i_in_singleton {P : (i : Nat) → i ∈ [0:1] → Prop} : (∀ i, (p : i ∈ [0:1]) → P i p)
--   ↔ P 0 (by apply And.intro <;> linarith) := by
--   apply Iff.intro
--   . intro h; apply h 0
--   . intro h i p; cases p; rename_i _ p; cases p
--     . assumption
--     . contradiction

-- -- @[simp]
-- lemma for_i_in_succ {n : Nat} { P : (i : Nat) → i ∈ [0 : n.succ + 1] → Prop} : (∀i, (p : i ∈ [0:n.succ + 1]) → P i p)
--   ↔ ((P (n + 1) (by apply And.intro <;> linarith)) ∧
--      (∀i, (p : i ∈ [0:n+1]) → P i (by cases p; apply And.intro <;> linarith))) := by
--   apply Iff.intro
--   . intro p;
--     apply And.intro
--     . exact p (n+1) (by apply And.intro <;> linarith)
--     . intro i range
--       apply p i (by cases range; apply And.intro <;> linarith)
--   . intro h i range
--     cases h ; rename_i hmax hrest
--     cases range; rename_i range_bot range_top
--     cases range_top
--     . apply hmax
--     . apply hrest
--       apply And.intro
--       . linarith
--       . simp at *; linarith

-- theorem suceeded_suceeds {arg : Vector F n} : binary_comparison_with_constant' base ix ix_ok 1 0 arg ↔ ∀ i, (p: i ∈ [0:ix+1]) → Gates.is_bool (arg[i]'(by cases p; linarith)) := by
--   induction ix with
--   | zero =>
--     unfold binary_comparison_with_constant'
--     cases base[0] <;> simp
--   | succ n ih =>
--     unfold binary_comparison_with_constant'
--     cases base[Nat.succ n] <;> simp [ih, for_i_in_succ]

-- theorem only_binary {arg : Vector F n} :
--   Gates.is_bool s →
--   Gates.is_bool f →
--   binary_comparison_with_constant base ix ix_ok s f arg →
--   ∀ i, (p: i ∈ [0:ix+1]) → Gates.is_bool (arg[i]'(by cases p; linarith)) := by
--   intro bools boolf
--   rw [binary_comparison_simpl] <;> try assumption
--   induction ix generalizing s f with
--   | zero =>
--     unfold binary_comparison_with_constant'
--     cases base[0] <;> {simp; tauto}
--   | succ n ih =>
--     unfold binary_comparison_with_constant'
--     cases base[Nat.succ n] <;> {
--       intro recur
--       simp at recur; cases recur; rename_i _ recur
--       simp [for_i_in_succ]
--       apply And.intro
--       . assumption
--       . apply ih
--         case a => exact recur
--         all_goals ((try split) <;> simp [*])
--     }

-- def bit_cmp (base_bit : Bit) (arg_bit : F): Option Ordering := match base_bit with
--   | Bit.zero => match arg_bit with
--     | 0 => some Ordering.eq
--     | 1 => some Ordering.lt
--     | _ => none
--   | Bit.one => match arg_bit with
--     | 0 => some Ordering.gt
--     | 1 => some Ordering.eq
--     | _ => none

-- def binary_comparison_ix_free (base : Vector Bit n) (arg : Vector F n): Prop := match n with
-- | 0 => False
-- | Nat.succ _ => match bit_cmp base.head arg.head with
--   | none => False
--   | some Ordering.lt => False
--   | some Ordering.gt => True
--   | some Ordering.eq => binary_comparison_ix_free base.tail arg.tail


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
-- theorem vector_get_snoc_last { vs : Vector α n }:
--   (vs.snoc v)[n]'(by linarith) = v := by
--   induction n with
--   | zero =>
--     cases vs using Vector.casesOn; rfl
--   | succ n ih =>
--     cases vs using Vector.casesOn
--     simp [ih]

-- @[simp]
-- theorem vector_get_cons_succ {vs : Vector α n} { ix_ok : i < n}:
--   (v ::ᵥ vs)[Nat.succ i]'(by linarith) = vs[i]'ix_ok := by
--   rfl

-- @[simp]
-- lemma snoc_get_not_last {vs : Vector α (Nat.succ n) } {ix_small : ix ≤ n}: (vs.snoc v)[ix]'(by linarith) = vs[ix]'(by linarith) := by
--   induction ix generalizing vs n with
--   | zero =>
--     cases vs using Vector.casesOn; rename_i hd tl
--     simp
--   | succ ix ih =>
--     cases vs using Vector.casesOn; rename_i hd tl
--     simp
--     rw [vector_get_cons_succ] <;> try linarith
--     rw [vector_get_cons_succ] <;> try linarith
--     cases n with
--     | zero => cases ix_small
--     | succ _ =>
--       apply ih
--       linarith

-- theorem binary_comp_snoc (base : Vector Bit (Nat.succ n)) (arg : Vector F (Nat.succ n)) (ix_ok : i ≤ n):
--   binary_comparison_with_constant' (base.snoc b) i (by linarith) s f (arg.snoc a) ↔
--   binary_comparison_with_constant' base i (by linarith) s f arg := by
--   induction i generalizing s f with
--   | zero =>
--     simp [binary_comparison_with_constant']
--   | succ i ih =>
--     unfold binary_comparison_with_constant'
--     simp
--     rw [ih, ih]
--     rw [snoc_get_not_last] <;> try linarith
--     rw [snoc_get_not_last]
--     linarith

-- theorem binary_comp_ix_free_simp (base : Vector Bit (Nat.succ n)) (arg : Vector F (Nat.succ n)):
--   (∀i, (p : i ∈ [0:Nat.succ n]) → Gates.is_bool (arg[i]'(by cases p; linarith))) →
--   (binary_comparison_with_constant base n (by simp) 0 0 arg ↔ binary_comparison_ix_free base.reverse arg.reverse) := by
--   intro range_checks
--   simp [binary_comparison_simpl]
--   induction n with
--   | zero =>
--     cases base using Vector.casesOn; rename_i bhd btl
--     cases btl using Vector.casesOn
--     cases arg using Vector.casesOn; rename_i ahd atl
--     cases atl using Vector.casesOn
--     simp [binary_comparison_with_constant', binary_comparison_ix_free] at *
--     cases range_checks <;> { subst_vars; cases bhd <;> { simp [bit_cmp]; tauto } }
--   | succ n ih =>
--     cases base using Vector.revCasesOn; rename_i bhd btl
--     cases arg using Vector.revCasesOn; rename_i ahd atl
--     unfold binary_comparison_ix_free
--     simp
--     rw [←ih]
--     . rw [binary_comparison_with_constant']
--       simp
--       simp [for_i_in_succ] at range_checks
--       cases range_checks ; rename_i ahdbool atlbool
--       simp [*]
--       cases ahdbool <;> cases bhd
--       all_goals (
--         subst_vars
--         simp [bit_cmp, binary_comp_snoc]
--         conv => rhs; whnf
--       )
--       . rw [suceeded_suceeds]
--         simp
--         intro i p
--         have := atlbool i p
--         rw [snoc_get_not_last] at this
--         . assumption
--         . cases p; linarith
--       . simp [failed_fails]
--     . intro i p
--       have := range_checks i (by cases p; apply And.intro <;> linarith)
--       rw [snoc_get_not_last] at this
--       . assumption
--       . cases p; linarith

