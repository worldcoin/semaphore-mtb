import ProvenZk.Gates
import ProvenZk.Binary

def allIxes (f : α → Prop) : Vector α n → Prop := fun v => ∀(i : Fin n), f v[i]

@[simp]
theorem allIxes_cons : allIxes f (v ::ᵥ vs) ↔ f v ∧ allIxes f vs := by
  simp [allIxes, GetElem.getElem]
  apply Iff.intro
  . intro h
    exact ⟨h 0, fun i => h i.succ⟩
  . intro h i
    cases i using Fin.cases
    . simp [h.1]
    . simp [h.2]

@[simp]
theorem allIxes_nil : allIxes f Vector.nil := by
  simp [allIxes]

@[simp]
theorem is_bool_is_bit (a : ZMod n) [Fact (Nat.Prime n)]: Gates.is_bool a = is_bit a := by rfl

@[simp]
theorem vector_get_zero {vs : Vector i n} : (v ::ᵥ vs)[0] = v := by rfl

@[simp]
theorem vector_get_succ_fin {vs : Vector i n} {i : Fin n} : (v ::ᵥ vs)[i.succ] = vs[i] := by rfl

@[simp]
theorem vector_get_succ_nat {vs : Vector i n} {i : Nat} {h : i.succ < n.succ } : (v ::ᵥ vs)[i.succ]'h = vs[i]'(by linarith) := by rfl

abbrev SubVector α n prop := Subtype (α := Vector α n) (allIxes prop)

namespace Fin

theorem castSucc_succ_eq_succ_castSucc : Fin.castSucc (Fin.succ i) = Fin.succ (Fin.castSucc i) := by
  rfl

theorem last_succ_eq_succ_last : Fin.last (Nat.succ n) = Fin.succ (Fin.last n) := by
  rfl

theorem last_def : Fin.mk (n := Nat.succ n) n (by simp) = Fin.last n := by
  rfl

theorem castSucc_def {i : Fin n} :
  Fin.mk (n := Nat.succ n) (i.val) (by cases i; linarith) = i.castSucc := by
  rfl

theorem cast_last {n : Nat} : ↑n = Fin.last n := by
  conv => lhs; whnf
  conv => rhs; whnf
  simp

end Fin

@[simp]
theorem vector_get_snoc_last { vs : Vector α n }:
  (vs.snoc v).get (Fin.last n) = v := by
  induction n with
  | zero =>
    cases vs using Vector.casesOn; rfl
  | succ n ih =>
    cases vs using Vector.casesOn
    rw [Fin.last_succ_eq_succ_last, Vector.snoc_cons, Vector.get_cons_succ, ih]

@[simp]
lemma snoc_get_castSucc {vs : Vector α n}: (vs.snoc v).get (Fin.castSucc i) = vs.get i := by
  cases n
  case zero => cases i using finZeroElim
  case succ n =>
  induction n with
  | zero =>
    cases i using Fin.cases with
    | H0 => cases vs using Vector.casesOn with | cons hd tl => simp
    | Hs i => cases i using finZeroElim
  | succ n ih =>
    cases vs using Vector.casesOn with | cons hd tl =>
    cases i using Fin.cases with
    | H0 => simp
    | Hs i => simp [Fin.castSucc_succ_eq_succ_castSucc, ih]

theorem vector_get_val_getElem {v : Vector α n} {i : Fin n}: v[i.val]'(i.prop) = v.get i := by
  rfl

theorem getElem_def {v : Vector α n} {i : Nat} {prop}: v[i]'prop = v.get ⟨i, prop⟩ := by
  rfl

@[simp]
lemma vector_get_snoc_fin_prev {vs : Vector α n} {v : α} {i : Fin n}:
  (vs.snoc v)[i.val]'(by (have := i.prop); linarith) = vs[i.val]'(i.prop) := by
  simp [vector_get_val_getElem, getElem_def, Fin.castSucc_def]

theorem ofFn_snoc' { fn : Fin (Nat.succ n) → α }:
  Vector.ofFn fn = Vector.snoc (Vector.ofFn (fun (x : Fin n) => fn (Fin.castSucc x))) (fn n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    conv => lhs; rw [Vector.ofFn, ih]
    simp [Vector.ofFn]
    congr
    simp [Fin.succ]
    congr
    simp [Nat.mod_eq_of_lt]

namespace SubVector

def nil : SubVector α 0 prop := ⟨Vector.nil, by simp⟩

def snoc (vs: SubVector α n prop) (v : Subtype prop): SubVector α n.succ prop :=
  ⟨vs.val.snoc v.val, by
    intro i
    cases i using Fin.lastCases with
    | hlast => simp [GetElem.getElem, Fin.last_def, Subtype.property]
    | hcast i =>
      have := vs.prop i
      simp at this
      simp [*]
  ⟩

-- def cons {prop : α → Prop} (v : Subtype prop) (vs : SubVector α n prop): SubVector α n.succ prop :=
--   ⟨vs.val.cons v.val, by
--     sorry
--   ⟩


-- @[elab_as_elim]
-- def revInduction {C : ∀ {n:Nat}, SubVector α n prop → Sort _} {n : Nat} (v : SubVector α n prop)
--   (nil : C nil)
--   (snoc : ∀ {n : Nat} (vs : SubVector α n prop) (v : Subtype prop), (ih : C vs) → C (snoc vs v)): C v := by
--   rcases v with ⟨v, h⟩
--   induction v using Vector.revInductionOn with
--   | nil => exact nil
--   | snoc vs v ih => sorry

@[elab_as_elim]
def revCases {C : ∀ {n:Nat}, SubVector α n prop → Sort _} (v : SubVector α n prop)
  (nil : C nil)
  (snoc : ∀ {n : Nat} (vs : SubVector α n prop) (v : Subtype prop), C (vs.snoc v)): C v := by
  rcases v with ⟨v, h⟩
  cases v using Vector.revCasesOn with
  | nil => exact nil
  | snoc vs v =>
    refine snoc ⟨vs, ?vsp⟩ ⟨v, ?vp⟩
    case vsp =>
      intro i
      have := h i.castSucc
      simp at this
      simp [this]
    case vp =>
      have := h (Fin.last _)
      simp [GetElem.getElem, Fin.last_def] at this
      exact this

-- @[elab_as_elim]
-- def cases {C : ∀ {n:Nat}, SubVector α n prop → Sort _} (v : SubVector α n prop)
--   (nil : C nil)
--   (cons : ∀ {n : Nat} (v : Subtype prop) (vs : SubVector α n prop), C (cons v vs)): C v := by sorry

instance : GetElem (SubVector α n prop) (Fin n) (Subtype prop) (fun _ _ => True) where
  getElem v i _ := ⟨v.val.get i, v.prop i⟩

def lower (v: SubVector α n prop): Vector {v : α // prop v} n :=
  Vector.ofFn fun i => v[i]

def lift {prop : α → Prop} (v : Vector (Subtype prop) n): SubVector α n prop :=
  ⟨v.map Subtype.val, by
    intro i
    simp [GetElem.getElem, Subtype.property]⟩

theorem snoc_lower {vs : SubVector α n prop} {v : Subtype prop}:
  (vs.snoc v).lower = vs.lower.snoc v := by
  unfold lower
  rw [ofFn_snoc']
  congr
  . funext i
    cases n with
    | zero => cases i using finZeroElim
    | _ => simp [GetElem.getElem, snoc]
  . simp [GetElem.getElem, snoc, Fin.cast_last]

end SubVector


@[simp]
theorem is_bit_zero : is_bit (0 : ZMod n) := by tauto
@[simp]
theorem is_bit_one : is_bit (1 : ZMod n) := by tauto
abbrev bOne : {v : ZMod n // is_bit v} := ⟨1, by simp⟩
abbrev bZero : {v : ZMod n // is_bit v} := ⟨0, by simp⟩

@[elab_as_elim]
def bitCases' {n : Nat} {C : Subtype (α := ZMod n.succ.succ) is_bit → Sort _} (v : Subtype (α := ZMod n.succ.succ) is_bit)
  (zero : C bZero)
  (one : C bOne): C v := by
  rcases v with ⟨v, h⟩
  rcases v with ⟨v, _⟩
  cases v with
  | zero => exact zero
  | succ v => cases v with
    | zero => exact one
    | succ v =>
      apply False.elim
      rcases h with h | h <;> {
        injection h with h
        simp at h
      }

theorem isBitCases (b : Subtype (α := ZMod n) is_bit): b = bZero ∨ b = bOne := by
  cases b with | mk _ prop =>
  cases prop <;> {subst_vars ; tauto }

-- theorem ofFn_snoc' { fn : Fin (Nat.succ n) → α }: Vector.ofFn fn = Vector.snoc (Vector.ofFn (fun (x : Fin n) => fn x)) (fn n) := by
--   induction n with
--   | zero => rfl
--   | succ n ih =>
--     conv => lhs; rw [Vector.ofFn, ih]
--     simp [Vector.ofFn]
--     congr
--     . funext i;
--       congr
--       conv => lhs; whnf
--       conv => rhs; whnf
--       congr
--       rcases i with ⟨i, _⟩
--       simp [Nat.mod_eq_of_lt]
--       rw [Nat.mod_eq_of_lt]
--       linarith
--     . conv => lhs; whnf
--       conv => rhs; whnf
--       congr
--       simp [Nat.mod_eq_of_lt]

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


def bitCases : { v : ZMod (Nat.succ (Nat.succ n)) // is_bit v} → Bit
  | ⟨0, _⟩ => Bit.zero
  | ⟨1, _⟩ => Bit.one
  | ⟨⟨Nat.succ (Nat.succ i), _⟩, h⟩ => False.elim (by
      cases h <;> {
        rename_i h
        injection h with h;
        rw [Nat.mod_eq_of_lt] at h
        . injection h; try (rename_i h; injection h)
        . simp
      }
    )

@[simp] lemma ne_1_0 {n:Nat}: ¬(1 : ZMod (n.succ.succ)) = (0 : ZMod (n.succ.succ)) := by
  intro h;
  conv at h => lhs; whnf
  conv at h => rhs; whnf
  injection h with h
  injection h

@[simp] lemma ne_0_1 {n:Nat}: ¬(0 : ZMod (n.succ.succ)) = (1 : ZMod (n.succ.succ)) := by
  intro h;
  conv at h => lhs; whnf
  conv at h => rhs; whnf
  injection h with h
  injection h


@[simp]
lemma bitCases_eq_0 : bitCases b = Bit.zero ↔ b = bZero := by
  cases b with | mk val prop =>
  cases prop <;> {
    subst_vars
    conv => lhs; lhs; whnf
    simp
  }

@[simp]
lemma bitCases_eq_1 : bitCases b = Bit.one ↔ b = bOne := by
  cases b with | mk val prop =>
  cases prop <;> {
    subst_vars
    conv => lhs; lhs; whnf
    simp
  }

@[simp]
lemma bitCases_bZero {n:Nat}: bitCases (@bZero (n + 2)) = Bit.zero := by rfl

@[simp]
lemma bitCases_bOne {n:Nat}: bitCases (@bOne (n+2)) = Bit.one := by rfl

section Gates

variable {Order : Nat}
variable [Fact (Nat.Prime Order)]
-- abbrev F := ZMod Order

@[simp]
theorem gates_select_0 {a b r : ZMod Order}: Gates.select 0 a b r = (r = b) := by
  simp [Gates.select]

@[simp]
theorem gates_select_1 {a b r : ZMod Order}: Gates.select 1 a b r = (r = a) := by
  simp [Gates.select]

@[simp]
theorem gates_or_0 { a r : ZMod Order}: Gates.or a 0 r = (is_bit a ∧ r = a) := by
  simp [Gates.or]

@[simp]
theorem gates_0_or { a r : ZMod Order}: Gates.or 0 a r = (is_bit a ∧ r = a) := by
  simp [Gates.or]

@[simp]
theorem gates_1_or { a r : ZMod Order}: Gates.or 1 a r = (is_bit a ∧ r = 1) := by
  simp [Gates.or]

@[simp]
theorem gates_or_1 { a r : ZMod Order}: Gates.or a 1 r = (is_bit a ∧ r = 1) := by
  simp [Gates.or]

@[simp]
theorem gates_is_bit_one_sub {a : ZMod Order}: is_bit (Gates.sub 1 a) ↔ is_bit a := by
  simp [Gates.sub, is_bit, sub_eq_zero]
  tauto

end Gates
