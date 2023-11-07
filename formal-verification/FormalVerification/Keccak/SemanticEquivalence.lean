import FormalVerification
import ProvenZK
import Mathlib
import FormalVerification.Utils

open SemaphoreMTB (F Order)

-- variable [Fact (Nat.Prime Order)]

axiom order_prime : Nat.Prime Order
instance order_prime' : Fact (Nat.Prime Order) := ⟨order_prime⟩

-- TODO MOVE UTILS

theorem getElem_allIxes {v : { v: Vector α n // allIxes prop v  }} {i : Nat} { i_small : i < n}:
  v.val[i]'i_small = ↑(Subtype.mk (v.val.get ⟨i, i_small⟩) (v.prop ⟨i, i_small⟩)) := by rfl

theorem getElem_allIxes₂ {v : { v: Vector (Vector α m) n // allIxes (allIxes prop) v  }} {i j: Nat} { i_small : i < n} { j_small : j < m}:
  (v.val[i]'i_small)[j]'j_small = ↑(Subtype.mk ((v.val.get ⟨i, i_small⟩).get ⟨j, j_small⟩) (v.prop ⟨i, i_small⟩ ⟨j, j_small⟩)) := by rfl

theorem allIxes_indexed {v : {v : Vector α n // allIxes prop v}} {i : Nat} {i_small : i < n}:
  prop (v.val[i]'i_small) := v.prop ⟨i, i_small⟩

theorem allIxes_indexed₂ {v : {v : Vector (Vector (Vector α a) b) c // allIxes (allIxes prop) v}}
  {i : Nat} {i_small : i < c}
  {j : Nat} {j_small : j < b}:
  prop ((v.val[i]'i_small)[j]'j_small) :=
  v.prop ⟨i, i_small⟩ ⟨j, j_small⟩

theorem allIxes_indexed₃ {v : {v : Vector (Vector (Vector α a) b) c // allIxes (allIxes (allIxes prop)) v}}
  {i : Nat} {i_small : i < c}
  {j : Nat} {j_small : j < b}
  {k : Nat} {k_small : k < a}:
  prop (((v.val[i]'i_small)[j]'j_small)[k]'k_small) :=
  v.prop ⟨i, i_small⟩ ⟨j, j_small⟩ ⟨k, k_small⟩

-- END MOVE

structure UniqueSolution (f : α → Prop) (range : α → Prop) where
  val : Subtype range
  uniq : ∀x, f x ↔ x = val

def xor_unique (a b : {f : F // is_bit f}): UniqueSolution (fun x => Gates.xor a.val b.val x) is_bit := by
  cases a using bitCases' with
  | zero => cases b using bitCases' with
    | zero =>
      apply UniqueSolution.mk bZero
      simp [Gates.xor]
    | one =>
      apply UniqueSolution.mk bOne
      simp [Gates.xor]
  | one => cases b using bitCases' with
    | zero =>
      apply UniqueSolution.mk bOne
      simp [Gates.xor]
    | one =>
      apply UniqueSolution.mk bZero
      simp [Gates.xor]

def and_unique (a b : {f : F // is_bit f}): UniqueSolution (fun x => Gates.and a.val b.val x) is_bit := by
  cases a using bitCases' with
  | zero => cases b using bitCases' with
    | zero =>
      apply UniqueSolution.mk bZero
      simp [Gates.and]
    | one =>
      apply UniqueSolution.mk bZero
      simp [Gates.and]
  | one => cases b using bitCases' with
    | zero =>
      apply UniqueSolution.mk bZero
      simp [Gates.and]
    | one =>
      apply UniqueSolution.mk bOne
      simp [Gates.and]

def or_unique (a b : {f : F // is_bit f}): UniqueSolution (fun x => Gates.or a.val b.val x) is_bit := by
  cases a using bitCases' with
  | zero => cases b using bitCases' with
    | zero =>
      apply UniqueSolution.mk bZero
      simp
    | one =>
      apply UniqueSolution.mk bOne
      simp
  | one => cases b using bitCases' with
    | zero =>
      apply UniqueSolution.mk bOne
      simp
    | one =>
      apply UniqueSolution.mk bOne
      simp

def not_unique (a : {f : F // is_bit f}): UniqueSolution (fun x => x = Gates.sub (1:F) a) is_bit := by
  cases a using bitCases' with
  | zero =>
    apply UniqueSolution.mk bOne
    simp
  | one =>
    apply UniqueSolution.mk bZero
    simp

structure ConstantOf (f : (β → Prop) → Prop) (range : β → Prop) where
  val : Subtype range
  equiv : ∀k, f k = k val

def ConstantOf_constant {x : α} {range : α → Prop} (hp : range x): ConstantOf (fun k => k x) range :=
  ⟨⟨x, hp⟩, fun _ => rfl⟩

def ConstantOf_compose { f: (β → Prop) → Prop } {g : β → (γ → Prop) → Prop} {range : γ → Prop}
  (f_constant : ConstantOf f dom) (g_constant : ∀(c : Subtype dom), ConstantOf (g c) range):
  ConstantOf (fun k => f (λx ↦ g x k)) range := by
  rcases f_constant with ⟨c, _⟩
  rcases g_constant c with ⟨g, _⟩
  exists g
  simp [*]

def ConstantOf_compose_existential { f : α → Prop } {g : α → (β → Prop) → Prop} {range : β → Prop}
  (f_uniq : UniqueSolution f dom) (g_constant : ∀(c : Subtype dom), ConstantOf (g c) range):
  ConstantOf (fun k => ∃x, f x ∧ g x k) range := by
  rcases f_uniq with ⟨c, _⟩
  rcases g_constant c with ⟨g, _⟩
  exists g
  simp [*]

def Xor_64_64_constant (v1 v2 : SubVector F 64 is_bit):
  ConstantOf (SemaphoreMTB.Xor_64_64 v1.val v2.val) (allIxes is_bit) := by
  repeat (
    apply ConstantOf_compose_existential
    rw [getElem_allIxes, getElem_allIxes]
    apply xor_unique
    intro _
  )
  apply ConstantOf_constant
  simp [Subtype.property]

def Xor_64_64_constant' (v₁ v₂ : Vector F 64) {prop₁ : allIxes is_bit v₁} {prop₂ : allIxes is_bit v₂}:
  ConstantOf (SemaphoreMTB.Xor_64_64 v₁ v₂) (allIxes is_bit) :=
  Xor_64_64_constant ⟨v₁, prop₁⟩ ⟨v₂, prop₂⟩

def And_64_64_constant (v1 v2 : SubVector F 64 is_bit):
  ConstantOf (SemaphoreMTB.And_64_64 v1.val v2.val) (allIxes is_bit) := by
  repeat (
    apply ConstantOf_compose_existential
    rw [getElem_allIxes, getElem_allIxes]
    apply and_unique
    intro _
  )
  apply ConstantOf_constant
  simp [Subtype.property]

def Not_64_64_constant (v1 : SubVector F 64 is_bit):
  ConstantOf (SemaphoreMTB.Not_64 v1.val) (allIxes is_bit) := by
  repeat (
    apply ConstantOf_compose_existential
    rw [getElem_allIxes]
    apply not_unique
    intro _
  )
  apply ConstantOf_constant
  simp [Subtype.property]

def Xor5Round_constant {v1 v2 v3 v4 v5 : {v: F // is_bit v}}:
  ConstantOf (SemaphoreMTB.Xor5Round v1.val v2.val v3.val v4.val v5.val) is_bit := by
  repeat (
    apply ConstantOf_compose_existential
    apply xor_unique
    intro _
  )
  apply ConstantOf_constant
  apply Subtype.property

def Xor5_64_64_64_64_64_constant {v1 v2 v3 v4 v5 : SubVector F 64 is_bit}:
  ConstantOf (SemaphoreMTB.Xor5_64_64_64_64_64 v1.val v2.val v3.val v4.val v5.val) (allIxes is_bit) := by
  unfold SemaphoreMTB.Xor5_64_64_64_64_64
  repeat (
    apply ConstantOf_compose
    repeat rw [getElem_allIxes]
    apply Xor5Round_constant
    intro _
  )
  apply ConstantOf_constant
  simp [Subtype.property]

def KeccakRound_64_5_5_64_constant
  { state : {v : Vector (Vector (Vector F 64) 5) 5 // allIxes (allIxes (allIxes is_bit)) v} }
  { rc : SubVector F 64 is_bit }:
  ConstantOf (SemaphoreMTB.KeccakRound_64_5_5_64 state.val rc.val) (allIxes (allIxes (allIxes is_bit))) := by
  unfold SemaphoreMTB.KeccakRound_64_5_5_64
  repeat rw [getElem_allIxes₂]

  repeat (
    apply ConstantOf_compose
    apply Xor5_64_64_64_64_64_constant
    intro _
  )

  repeat (
    apply ConstantOf_compose (dom := allIxes is_bit)
    apply ConstantOf_constant
    simp [allIxes_indexed]
    intro _
    apply ConstantOf_compose
    apply Xor_64_64_constant
    intro _
  )

  repeat (
    apply ConstantOf_compose
    apply Xor_64_64_constant
    intro _
  )

  repeat (
    apply ConstantOf_compose (dom := allIxes is_bit)
    apply ConstantOf_constant
    simp [allIxes_indexed, Subtype.property]
    intro _
  )

  repeat (
    apply ConstantOf_compose
    apply Not_64_64_constant
    intro _
    apply ConstantOf_compose
    apply And_64_64_constant
    intro _
    apply ConstantOf_compose
    apply Xor_64_64_constant
    intro _
  )

  apply ConstantOf_compose
  apply Xor_64_64_constant
  intro _

  apply ConstantOf_constant
  simp [allIxes_indexed₃, Subtype.property]

def KeccakF_64_5_5_64_24_24_constant
  { state : {v : Vector (Vector (Vector F 64) 5) 5 // allIxes (allIxes (allIxes is_bit)) v} }
  { rc : { v : Vector (Vector F 64) 24 // allIxes (allIxes is_bit) v } }:
  ConstantOf (fun k => SemaphoreMTB.KeccakF_64_5_5_64_24_24 state.val rc.val k) (allIxes (allIxes (allIxes is_bit))) := by
  unfold SemaphoreMTB.KeccakF_64_5_5_64_24_24
  repeat (
    apply ConstantOf_compose
    rw [getElem_allIxes]
    apply KeccakRound_64_5_5_64_constant
    intro _
  )
  apply ConstantOf_constant
  apply Subtype.property

def KeccakF_64_5_5_64_24_24_constant'
  ( state : Vector (Vector (Vector F 64) 5) 5)
  ( state_prop : allIxes (allIxes (allIxes is_bit)) state)
  ( rc : Vector (Vector F 64) 24)
  ( rc_prop :  allIxes (allIxes is_bit) rc):
  ConstantOf (SemaphoreMTB.KeccakF_64_5_5_64_24_24 state rc) (allIxes (allIxes (allIxes is_bit))) := by
  apply KeccakF_64_5_5_64_24_24_constant (state := ⟨state, state_prop⟩) (rc := ⟨rc, rc_prop⟩)

def KeccakGadget_640_64_24_640_256_24_1088_1_constant
  (input : { v : Vector F 640 // allIxes is_bit v})
  ( rc : { v : Vector (Vector F 64) 24 // allIxes (allIxes is_bit) v } ):
  ConstantOf (SemaphoreMTB.KeccakGadget_640_64_24_640_256_24_1088_1 input.val rc.val) (allIxes is_bit) := by
  unfold SemaphoreMTB.KeccakGadget_640_64_24_640_256_24_1088_1
  apply ConstantOf_compose_existential
  apply xor_unique (a := bZero) (b := bOne)
  intro _
  apply ConstantOf_compose
  apply KeccakF_64_5_5_64_24_24_constant'
  simp only [allIxes_cons, allIxes_nil, allIxes_indexed, is_bit_zero, is_bit_one, true_and, and_true, Subtype.property]
  apply Subtype.property
  intro _
  apply ConstantOf_constant
  simp [allIxes_indexed₃]

def KeccakGadget_1568_64_24_1568_256_24_1088_1_constant
  (input : { v : Vector F 1568 // allIxes is_bit v})
  ( rc : { v : Vector (Vector F 64) 24 // allIxes (allIxes is_bit) v } ):
  ConstantOf (SemaphoreMTB.KeccakGadget_1568_64_24_1568_256_24_1088_1 input.val rc.val) (allIxes is_bit) := by
  unfold SemaphoreMTB.KeccakGadget_1568_64_24_1568_256_24_1088_1
  apply ConstantOf_compose_existential
  apply xor_unique (a := bZero) (b := bOne)
  intro _
  apply ConstantOf_compose
  apply KeccakF_64_5_5_64_24_24_constant'
  . simp only [allIxes_cons, allIxes_nil, allIxes_indexed, is_bit_zero, is_bit_one, true_and, and_true, Subtype.property]
  . apply Subtype.property
  repeat (
    intro _
    apply ConstantOf_compose
    apply Xor_64_64_constant'
    . simp only [allIxes_cons, allIxes_nil, allIxes_indexed₂, is_bit_zero, is_bit_one, true_and, and_true, Subtype.property]
    . simp only [allIxes_cons, allIxes_nil, allIxes_indexed, is_bit_zero, is_bit_one, true_and, and_true, Subtype.property]
  )
  intro _
  apply ConstantOf_compose
  apply KeccakF_64_5_5_64_24_24_constant'
  . simp only [allIxes_cons, allIxes_nil, allIxes_indexed₂, is_bit_zero, is_bit_one, true_and, and_true, Subtype.property]
  . apply Subtype.property
  intro _
  apply ConstantOf_constant
  simp [allIxes_indexed₃]





  -- apply Subtype.property
  -- intro _
  -- apply ConstantOf_constant
  -- simp [allIxes_indexed₃]
