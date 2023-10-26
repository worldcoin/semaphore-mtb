import FormalVerification
import ProvenZK
import Mathlib

open SemaphoreMTB (F Order)

variable [Fact (Nat.Prime Order)]

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
theorem is_bool_is_bit (a : F) : Gates.is_bool a = is_bit a := by rfl

@[simp]
theorem vector_get_zero {vs : Vector i n} : (v ::ᵥ vs)[0] = v := by rfl

@[simp]
theorem vector_get_succ_fin {vs : Vector i n} {i : Fin n} : (v ::ᵥ vs)[i.succ] = vs[i] := by rfl

@[simp]
theorem vector_get_succ_nat {vs : Vector i n} {i : Nat} {h : i.succ < n.succ } : (v ::ᵥ vs)[i.succ]'h = vs[i]'(by linarith) := by rfl

def IsConstant (f : (β → Prop) → Prop) (range : β → Prop): Prop := ∃(c : Subtype range), ∀k, f k ↔ k c

theorem IsConstant_compose { f: (β → Prop) → Prop } {g : β → (γ → Prop) → Prop} {range : γ → Prop}
  (f_constant : IsConstant f dom) (g_constant : ∀(c : Subtype dom), IsConstant (g c) range):
  IsConstant (fun k => f (λx ↦ g x k)) range := by
  rcases f_constant with ⟨c, _⟩
  rcases g_constant c with ⟨g, _⟩
  exists g
  simp [*]

def gateAndFunc (a b : F) (k : F → Prop) : Prop :=
  ∃r, Gates.and a b r ∧ k r

theorem gateAndFunc_def : (∃r, Gates.and a b r ∧ k r) ↔ gateAndFunc a b k := by
  rfl

theorem allIxes_indexed {v : {v : Vector α n // allIxes prop v}} {i : Nat} {i_small : i < n}:
  prop (v.val[i]'i_small) := v.prop ⟨i, i_small⟩

theorem allIxes_indexed₃ {v : {v : Vector (Vector (Vector α a) b) c // allIxes (allIxes (allIxes prop)) v}}
  {i : Nat} {i_small : i < c}
  {j : Nat} {j_small : j < b}
  {k : Nat} {k_small : k < a}:
  prop (((v.val[i]'i_small)[j]'j_small)[k]'k_small) :=
  v.prop ⟨i, i_small⟩ ⟨j, j_small⟩ ⟨k, k_small⟩

theorem Rot_64_1_deterministic : ∀{i: Subtype (allIxes dom)}, IsConstant (SemaphoreMTB.Rot_64_1 i.val) (allIxes dom) := by
  intro i
  refine ⟨⟨?_, ?dom⟩, ?prop⟩
  case prop =>
    intro _
    simp
    rfl
  case dom => simp [allIxes_indexed]

theorem getElem_allIxes {v : { v: Vector α n // allIxes prop v  }} {i : Nat} { i_small : i < n}:
  v.val[i]'i_small = ↑(Subtype.mk (v.val.get ⟨i, i_small⟩) (v.prop ⟨i, i_small⟩)) := by rfl

theorem getElem_allIxes₂ {v : { v: Vector (Vector α m) n // allIxes (allIxes prop) v  }} {i j: Nat} { i_small : i < n} { j_small : j < m}:
  (v.val[i]'i_small)[j]'j_small = ↑(Subtype.mk ((v.val.get ⟨i, i_small⟩).get ⟨j, j_small⟩) (v.prop ⟨i, i_small⟩ ⟨j, j_small⟩)) := by rfl

theorem const_deterministic {v : Subtype prop}:
  IsConstant (fun k => k v.val) prop := by
  exists v; simp

def gateSubFunc (a b : F) (k : F → Prop) : Prop :=
  ∃r, r = Gates.sub a b ∧ k r

theorem gateSubFunc_def : (∃r, r = Gates.sub a b ∧ k r) ↔ gateSubFunc a b k := by
  rfl

theorem not_deterministic { v : {v : F // is_bit v}}:
  IsConstant (gateSubFunc 1 v.val) is_bit := by
  unfold gateSubFunc
  cases v.prop <;> {
    refine ⟨⟨?_, ?_⟩, ?_⟩
    rotate_right
    . intro k; simp; rfl
    . simp [Gates.sub, is_bit, *]
  }

def gateXorFunc (a b : F) (k : F → Prop) : Prop :=
  ∃r, Gates.xor a b r ∧ k r

theorem gateXorFunc_def : (∃r, Gates.xor a b r ∧ k r) ↔ gateXorFunc a b k := by
  rfl

theorem xor_deterministic {v1 v2 : {v : F // is_bit v}}:
  IsConstant (gateXorFunc v1 v2) is_bit := by
  unfold gateXorFunc
  unfold Gates.xor
  cases v1.prop <;> {
    cases v2.prop <;> {
      simp only [*]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      rotate_right
      . intro k; simp; rfl
      . simp [Gates.xor, is_bit, *]; try tauto
    }
  }

theorem xor_deterministic' {v1 v2 : F} (v1_prop : is_bit v1) (v2_prop : is_bit v2):
  IsConstant (gateXorFunc v1 v2) is_bit := xor_deterministic (v1 := ⟨v1, v1_prop⟩) (v2 := ⟨v2, v2_prop⟩)


theorem and_deterministic {v1 v2 : {v : F // is_bit v}}:
  IsConstant (gateAndFunc v1 v2) is_bit := by
  unfold gateAndFunc
  unfold Gates.and
  cases v1.prop <;> {
    cases v2.prop <;> {
      simp only [*]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      rotate_right
      . intro k; simp; rfl
      . simp [Gates.and, is_bit, *]
    }
  }

theorem Xor5Round_deterministic {v1 v2 v3 v4 v5 : {v: F // is_bit v}}:
  IsConstant (SemaphoreMTB.Xor5Round v1.val v2.val v3.val v4.val v5.val) is_bit := by
  unfold SemaphoreMTB.Xor5Round
  repeat (
    conv => enter [1, k]; rw [gateXorFunc_def]
    apply IsConstant_compose
    apply xor_deterministic
    intro _
  )
  apply const_deterministic

theorem Xor5_64_64_64_64_64_deterministic {v1 v2 v3 v4 v5 : {v: Vector F 64 // allIxes is_bit v}}:
  IsConstant (SemaphoreMTB.Xor5_64_64_64_64_64 v1.val v2.val v3.val v4.val v5.val) (allIxes is_bit) := by
  unfold SemaphoreMTB.Xor5_64_64_64_64_64

  repeat (
    apply IsConstant_compose
    repeat rw [getElem_allIxes]
    apply Xor5Round_deterministic
    intro _
  )
  refine ⟨⟨?_, ?_⟩, ?_⟩
  rotate_right
  . intro k; simp; rfl
  . simp [Subtype.property]


theorem Xor_64_64_deterministic {v1 v2 : {v: Vector F 64 // allIxes is_bit v}}:
  IsConstant (SemaphoreMTB.Xor_64_64 v1.val v2.val) (allIxes is_bit) := by
  unfold SemaphoreMTB.Xor_64_64
  repeat (
    conv => enter [1, k]; rw [gateXorFunc_def]
    apply IsConstant_compose
    rw [getElem_allIxes, getElem_allIxes]
    apply xor_deterministic
    intro _
  )

  refine ⟨⟨?_, ?_⟩, ?_⟩
  rotate_right
  . intro k; simp; rfl
  . simp [Subtype.property]

theorem And_64_64_deterministic {v1 v2 : {v: Vector F 64 // allIxes is_bit v}}:
  IsConstant (SemaphoreMTB.And_64_64 v1.val v2.val) (allIxes is_bit) := by
  unfold SemaphoreMTB.And_64_64
  conv => enter [1, k]; rw [gateAndFunc_def]
  apply IsConstant_compose
  rw [getElem_allIxes, getElem_allIxes]
  apply and_deterministic
  intro _
  repeat (
    conv => enter [1, k]; rw [gateAndFunc_def]
    apply IsConstant_compose
    rw [getElem_allIxes, getElem_allIxes]
    apply and_deterministic
    intro _
  )

  refine ⟨⟨?_, ?_⟩, ?_⟩
  rotate_right
  . intro k; simp; rfl
  . simp [Subtype.property]

theorem Not_64_deterministic {v : {v: Vector F 64 // allIxes is_bit v}}:
  IsConstant (SemaphoreMTB.Not_64 v.val) (allIxes is_bit) := by
  unfold SemaphoreMTB.Not_64
  simp only [gateSubFunc_def]
  repeat rw [getElem_allIxes]
  repeat (
    apply IsConstant_compose
    apply not_deterministic
    intro _
  )

  refine ⟨⟨?_, ?_⟩, ?_⟩
  rotate_right
  . intro k; simp; rfl
  . simp [Subtype.property]


theorem KeccakRound_64_5_5_64_deterministic
  { state : {v : Vector (Vector (Vector F 64) 5) 5 // allIxes (allIxes (allIxes is_bit)) v} }
  { rc : { v : Vector F 64 // allIxes is_bit v } }:
  IsConstant (SemaphoreMTB.KeccakRound_64_5_5_64 state.val rc.val) (allIxes (allIxes (allIxes is_bit))) := by

  unfold SemaphoreMTB.KeccakRound_64_5_5_64
  repeat rw [getElem_allIxes₂]
  repeat (
    apply IsConstant_compose
    apply Xor5_64_64_64_64_64_deterministic
    intro _
  )
  repeat (
    apply IsConstant_compose
    apply Rot_64_1_deterministic
    intro _
    apply IsConstant_compose
    apply Xor_64_64_deterministic
    intro _
  )

  repeat (
    apply IsConstant_compose
    apply Xor_64_64_deterministic
    intro _
  )

  apply IsConstant_compose (dom := allIxes is_bit)
  unfold SemaphoreMTB.Rot_64_0
  apply Exists.intro
  intro k; simp; rfl
  intro _

  repeat (
    apply IsConstant_compose (dom := allIxes is_bit)
    . refine ⟨⟨?_, ?_⟩, ?_⟩
      rotate_right
      . intro _
        simp
        rfl
      . simp [allIxes_indexed]
    intro _
  )

  repeat (
    apply IsConstant_compose (dom := allIxes is_bit)
    apply Not_64_deterministic
    intro _
    apply IsConstant_compose (dom := allIxes is_bit)
    apply And_64_64_deterministic
    intro _
    apply IsConstant_compose (dom := allIxes is_bit)
    apply Xor_64_64_deterministic
    intro _
  )

  apply IsConstant_compose (dom := allIxes is_bit)
  apply Xor_64_64_deterministic
  intro _

  refine ⟨⟨?_, ?_⟩, ?_⟩
  rotate_right
  . intro k; simp; rfl
  . simp [Subtype.property]

theorem KeccakF_64_5_5_64_24_24_deterministic
  { state : {v : Vector (Vector (Vector F 64) 5) 5 // allIxes (allIxes (allIxes is_bit)) v} }
  { rc : { v : Vector (Vector F 64) 24 // allIxes (allIxes is_bit) v } }:
  IsConstant (fun k => SemaphoreMTB.KeccakF_64_5_5_64_24_24 state.val rc.val k) (allIxes (allIxes (allIxes is_bit))) := by
  unfold SemaphoreMTB.KeccakF_64_5_5_64_24_24
  repeat rw [getElem_allIxes]
  repeat (
    apply IsConstant_compose
    apply KeccakRound_64_5_5_64_deterministic
    intro _
  )
  apply const_deterministic

theorem KeccakF_64_5_5_64_24_24_deterministic'
  { state : Vector (Vector (Vector F 64) 5) 5 }
  { rc : Vector (Vector F 64) 24 }
  (state_prop : allIxes (allIxes (allIxes is_bit)) state)
  (rc_prop :  allIxes (allIxes is_bit) rc):
  IsConstant (SemaphoreMTB.KeccakF_64_5_5_64_24_24 state rc) (allIxes (allIxes (allIxes is_bit))) :=
  KeccakF_64_5_5_64_24_24_deterministic (state := ⟨state, state_prop⟩) (rc := ⟨rc, rc_prop⟩)


@[simp]
theorem is_bit_zero : is_bit (0 : F) := by tauto
@[simp]
theorem is_bit_one : is_bit (1 : F) := by tauto


theorem KeccakGadget_640_64_24_640_256_24_1088_1_deterministic
  { input : { v : Vector F 640 // allIxes is_bit v}}
  { rc : { v : Vector (Vector F 64) 24 // allIxes (allIxes is_bit) v } }:
  IsConstant (SemaphoreMTB.KeccakGadget_640_64_24_640_256_24_1088_1 input.val rc.val) (allIxes is_bit) := by
  unfold SemaphoreMTB.KeccakGadget_640_64_24_640_256_24_1088_1
  simp only [gateXorFunc_def]
  apply IsConstant_compose
  apply xor_deterministic' <;> tauto
  intro _
  apply IsConstant_compose
  apply KeccakF_64_5_5_64_24_24_deterministic'
  simp only [allIxes_cons, allIxes_nil, allIxes_indexed, is_bit_zero, is_bit_one, true_and, and_true, Subtype.property]
  apply Subtype.property
  intro _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  rotate_right
  . intro _
    simp
    rfl
  . simp [allIxes_indexed₃]

-- abbrev expected_result: Vector F 256 := vec![0,0,1,1,1,0,1,0,0,1,1,1,0,0,0,0,1,0,0,1,0,0,1,1,0,0,0,0,0,0,0,1,1,1,1,1,0,1,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,1,1,0,1,0,0,1,0,0,0,1,0,1,1,1,1,1,0,0,0,1,1,1,1,0,1,0,0,0,0,0,0,1,1,0,1,1,1,0,0,0,1,0,0,0,0,0,1,0,0,1,1,0,1,1,0,0,0,0,0,1,1,1,0,1,1,1,1,0,1,0,1,0,0,1,1,1,1,1,0,0,1,1,1,0,0,1,0,1,0,0,0,0,1,0,0,1,1,1,1,0,0,1,1,0,0,1,1,1,1,1,1,0,1,1,0,0,1,0,0,1,0,0,1,0,1,1,1,0,0,1,0,0,0,1,0,0,1,1,0,1,0,0,0,0,0,0,0,1,1,1,0,1,1,0,0,1,1,1,0,1,0,0,1,0,1,0,0,1,0,0,1,1,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,1,0,1,1,0,0,0,1,0,0,1,0,0,1,1]
--
-- abbrev rc: Vector (Vector F 64) 24 := vec![vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]
