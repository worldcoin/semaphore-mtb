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

def mapCollectCont {n : Nat} : (Fin n → (α → β) → β) → (Vector α n → β) → β :=
  match n with
  | 0 => fun _ k => k Vector.nil
  | Nat.succ _ => fun prod k => prod 0 fun r => mapCollectCont (fun i => prod i.succ) (fun i => k (r ::ᵥ i))

def finSuccCases {n : Nat} (i : Fin (Nat.succ n)) : i = 0 ∨ ∃(j : Fin n), i = j.succ :=
  match i with
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨j+1, h⟩ => Or.inr ⟨⟨j, Nat.lt_of_succ_lt_succ h⟩, rfl⟩

theorem mapCollectCont_uncps {n : Nat} {prod : Fin n → (α → Prop) → Prop} {prod_uncps : Fin n → α} {prod_prop : Fin n → Prop} {k : Vector α n → Prop}:
  (∀ (i : Fin n) (k : α → Prop), prod i k = (prod_prop i ∧ k (prod_uncps i))) → mapCollectCont prod k = ((∀(i : Fin n), prod_prop i) ∧ k (Vector.ofFn prod_uncps)) := by
  intro h
  induction n with
  | zero => simp [mapCollectCont, Vector.ofFn]
  | succ n ih =>
    unfold mapCollectCont
    rw [h, Vector.ofFn]
    rw [ih (prod_prop := fun i => prod_prop i.succ) (prod_uncps := fun i => prod_uncps i.succ)]
    . apply propext
      apply Iff.intro
      . intro ⟨prop₀, propᵣ, rewrite⟩
        refine ⟨?_, rewrite⟩
        intro i
        cases i using Fin.cases
        . assumption
        . apply propᵣ
      . intro ⟨prop, rewrite⟩
        exact ⟨prop 0, (fun i => prop i.succ), rewrite⟩
    . exact (fun i k => h i.succ k)

def andCont (a b : Vector F n) (k : Vector F n → Prop) : Prop :=
  mapCollectCont (fun i (k : F → Prop) => ∃r, Gates.and a[i] b[i] r ∧ k r) k

theorem and_cont {A B : Vector F 64} : SemaphoreMTB.And_64_64 A B = andCont A B := by rfl

theorem forall_fin_succ {P : Fin (Nat.succ n) → Prop} : (∀i, P i) ↔ (P 0 ∧ ∀(i : Fin n), P i.succ) := by
  apply Iff.intro
  . intro h
    refine ⟨h 0, fun i => h i.succ⟩
  . intro ⟨_, _⟩
    intro i
    cases i using Fin.cases
    . assumption
    . tauto

@[simp]
theorem vector_get_zero {vs : Vector i n} : (v ::ᵥ vs)[0] = v := by rfl

@[simp]
theorem vector_get_succ_fin {vs : Vector i n} {i : Fin n} : (v ::ᵥ vs)[i.succ] = vs[i] := by rfl

@[simp]
theorem vector_get_succ_nat {vs : Vector i n} {i : Nat} {h : i.succ < n.succ } : (v ::ᵥ vs)[i.succ]'h = vs[i]'(by linarith) := by rfl

theorem is_vector_binary_indexed {n}  : is_vector_binary (d := n) (n := Order) = allIxes is_bit := by
  funext v
  induction v using Vector.inductionOn with
  | h_nil => simp [is_vector_binary]
  | h_cons ih => simp [is_vector_binary_cons, ih]

theorem is_vector_binary_indexed₂ {n : Nat} {v₁ v₂ : Vector F n} : (is_vector_binary v₁ ∧ is_vector_binary v₂) ↔ ∀(i: Fin n), is_bit v₁[i] ∧ is_bit v₂[i] := by
  simp [is_vector_binary_indexed, forall_and]

def bitAnd : Bit → Bit → Bit
| Bit.one, Bit.one => Bit.one
| _, _ => Bit.zero

instance : HAnd Bit Bit Bit := ⟨bitAnd⟩


instance and_rw {a b r : F} : Gates.and a b r ↔ is_bit a ∧ is_bit b ∧ r = Bit.toZMod (zmod_to_bit a &&& zmod_to_bit b) := by
  unfold Gates.and
  unfold Gates.is_bool
  apply Iff.intro <;> {
    intro ⟨a, b, r⟩
    cases a <;> {
      cases b <;> {
        subst_vars
        tauto
      }
    }
  }

theorem and_uncps {A B : Vector F 64}:
  SemaphoreMTB.And_64_64 A B k ↔
  is_vector_binary A ∧
  is_vector_binary B ∧
  k (Vector.ofFn (fun i => Bit.toZMod $ (zmod_to_bit A[i]) &&& (zmod_to_bit B[i]))) := by
  rw [and_cont, andCont]
  rw [mapCollectCont_uncps (prod_uncps := fun i => Bit.toZMod $ (zmod_to_bit A[i]) &&& (zmod_to_bit B[i]))
                           (prod_prop := fun i => is_bit A[i] ∧ is_bit B[i])]
  . simp [forall_and, and_assoc, is_vector_binary_indexed]
  . intro i k
    conv => lhs; arg 1; intro; rw [and_rw]

    apply propext
    apply Iff.intro
    . intro ⟨_, h⟩
      rw [and_rw] at h
      rcases h with ⟨⟨ _, _, _⟩, _⟩
      subst_vars
      tauto
    . intro ⟨⟨ _,_⟩, _⟩
      apply Exists.intro
      rw [and_rw]
      tauto

def IsConstant (f : (β → Prop) → Prop) (range : β → Prop): Prop := ∃(c : Subtype range), ∀k, f k ↔ k c

def IsFunctional (f : α → (β → Prop) → Prop) (domain : α → Prop) (range : β → Prop): Prop :=
  ∃(g : Subtype domain → Subtype range), ∀(a: Subtype domain) k, f a k ↔ k (g a)

theorem IsFunctional_of_IsConstant {f : α → (β → Prop) → Prop} {domain : α → Prop} {range : β → Prop}
  (constants : ∀(i:Subtype domain), IsConstant (f i) range):
  IsFunctional f domain range := by
  exists (fun a => (constants a).choose)
  intro a k
  exact (constants a).choose_spec k

theorem IsConstant_of_IsFunctional {f : α → (β → Prop) → Prop} {domain : α → Prop} {range : β → Prop}
  {functional : IsFunctional f domain range} (a: Subtype domain): IsConstant (f a) range := by
  rcases functional with ⟨f, _⟩
  exists f a
  simp [*]

theorem IsConstant_of_IsFunctional' {f : α → (β → Prop) → Prop} {domain : α → Prop} {range : β → Prop}
  {functional : IsFunctional f domain range} {a: α} {is_dom : domain a}: IsConstant (f a) range := by
  rcases functional with ⟨f, hf⟩
  exists f ⟨a, is_dom⟩
  simp [←hf]

theorem IsConstant_compose { f: (β → Prop) → Prop } {g : β → (γ → Prop) → Prop} {range : γ → Prop}
  (f_constant : IsConstant f dom) (g_constant : ∀(c : Subtype dom), IsConstant (g c) range):
  IsConstant (fun k => f (λx ↦ g x k)) range := by
  rcases f_constant with ⟨c, _⟩
  rcases g_constant c with ⟨g, _⟩
  exists g
  simp [*]

theorem IsFunctional_compose {f : α → (β → Prop) → Prop} {g : β → (γ → Prop) → Prop}
  (f_functional : IsFunctional f domain range) (g_functional : IsFunctional g range g_range):
  IsFunctional (fun a k => f a (λx ↦ g x k)) domain g_range := by
  rcases f_functional with ⟨fr, _⟩
  rcases g_functional with ⟨gr, _⟩
  exists (fun a => gr (fr a))
  simp [*]

def ofFnCont : (Fin n → (α → Prop) → Prop) → (Vector α n → Prop) → Prop :=
  match n with
  | 0 => fun _ k => k Vector.nil
  | Nat.succ _ => fun gen k => gen 0 fun r => ofFnCont (fun i => gen i.succ) (fun i => k (r ::ᵥ i))

def ofFnMap {n} (gen : α → (β → Prop) → Prop) : Vector α n → (Vector β n → Prop) → Prop :=
  fun v => ofFnCont (fun i k => gen v[i] k)

theorem ofFnMap_functional {gen : α → (β → Prop) → Prop} (gen_functional : IsFunctional gen domain range):
  IsFunctional (ofFnMap (n := n) gen) (allIxes domain) (allIxes range) := by
  unfold ofFnMap
  induction n with
  | zero =>
    exists (fun _ => Vector.nil)
    simp [ofFnCont]
  | succ _ ih =>
    rcases gen_functional with ⟨head_fn, head_prop⟩
    rcases ih with ⟨tail_fn, tail_prop⟩
    exists (fun v => head_fn v[0] ::ᵥ tail_fn v.tail)
    intro a k dom
    unfold ofFnCont
    simp at tail_prop
    cases a using Vector.casesOn; rename_i hd tl
    simp at dom
    rcases dom with ⟨hhd, htl⟩
    simp
    rw [(head_prop _ _ _).1, (tail_prop _ _ _).1]
    simp
    apply And.intro
    apply (head_prop _ (fun _ => True) hhd).2
    apply (tail_prop _ (fun _ => True) htl).2
    exact htl
    exact hhd

theorem arg_transform_functional {f : β → (γ → Prop) → Prop} {g : α → β} {dom₂ : α → Prop}
  (f_functional : IsFunctional f dom range) (dom_preserved : ∀{a}, dom₂ a → dom (g a)):
  IsFunctional (fun a => f (g a)) dom₂ range := by
  rcases f_functional with ⟨f, hf⟩
  exists (fun a => f (g a))
  intro a k dom
  have := dom_preserved dom
  simp
  apply And.intro
  apply (hf _ _ this).1
  apply (hf _ (fun _ => True) this).2

def gateAndFunc (a b : F) (k : F → Prop) : Prop :=
  ∃r, Gates.and a b r ∧ k r

theorem gateAndFunc_def : (∃r, Gates.and a b r ∧ k r) ↔ gateAndFunc a b k := by
  rfl

theorem and_functional :
  IsFunctional gateAndFunc (fun (a : F×F) => Gates.is_bool a.1 ∧ Gates.is_bool a.2) Gates.is_bool:= by
  exists (fun a => a.1 * a.2)
  intro ⟨a, b⟩ k ⟨doma, domb⟩
  simp at doma domb
  unfold gateAndFunc
  unfold Gates.and
  simp
  apply And.intro
  . apply Iff.intro
    . simp; intros; subst_vars; assumption
    . simp
      intros
      exists a * b
  . cases doma <;> {
      cases domb <;> {
        subst_vars; tauto
      }
    }

def and_64_64Func (a : Vector F 64 × Vector F 64) :=
  ofFnMap gateAndFunc (Vector.ofFn (n := 64) (fun i => (a.1[i], a.2[i])))

theorem and_64_64_def : SemaphoreMTB.And_64_64 A B k = and_64_64Func (A,B) k := by rfl

inductive IsReorgOf (source : Vector α n): Vector α m →  Prop
| nil : IsReorgOf source Vector.nil
| cons : ∀{i : Nat} {tail : Vector α m} {p : i < n}, IsReorgOf source tail → IsReorgOf source (source[i]'p ::ᵥ tail)

theorem allIxes_of_reorg : IsReorgOf source target → allIxes dom source → allIxes dom target := by
  intro reorg doms
  induction reorg with
  | nil => simp
  | cons _ ih =>
    simp
    apply And.intro
    . apply doms ⟨_, _⟩; assumption
    . exact ih

theorem allIxes_of_reorg_subtype {source : {v : Vector α n // allIxes dom v}} : IsReorgOf source.val target → allIxes dom target :=
  fun reorg => allIxes_of_reorg reorg source.property


theorem  Rot_64_1_functional {dom} : IsFunctional SemaphoreMTB.Rot_64_1 (allIxes dom) (allIxes dom) := by
  apply IsFunctional_of_IsConstant
  intro i
  refine ⟨⟨?_, ?dom⟩, ?prop⟩
  case prop =>
    intro _
    simp
    rfl
  case dom =>
    apply allIxes_of_reorg _ i.prop
    repeat apply IsReorgOf.cons
    apply IsReorgOf.nil

theorem Rot_64_1_deterministic : ∀{i: Subtype (allIxes dom)}, IsConstant (SemaphoreMTB.Rot_64_1 i.val) (allIxes dom) := by
  intro i
  refine ⟨⟨?_, ?dom⟩, ?prop⟩
  case prop =>
    intro _
    simp
    rfl
  case dom =>
    apply allIxes_of_reorg _ i.prop
    repeat apply IsReorgOf.cons
    apply IsReorgOf.nil

theorem and_64_64_functional : IsFunctional and_64_64Func (fun (a, b) => is_vector_binary a ∧ is_vector_binary b) is_vector_binary := by
  simp [and_64_64Func]
  apply arg_transform_functional
  rw [is_vector_binary_indexed]
  apply ofFnMap_functional
  apply and_functional
  intro ⟨a, b⟩
  simp [is_vector_binary_indexed₂, GetElem.getElem, allIxes]

-- theorem

-- def KeccakRound_64_5_5_64 (A: Vector (Vector (Vector F 64) 5) 5) (RC: Vector F 64) (k: Vector (Vector (Vector F 64) 5) 5 -> Prop)

def xor5 (a : Vector (Vector F 64) 5) (k : Vector F 64 → Prop): Prop :=
  SemaphoreMTB.Xor5_64_64_64_64_64 a[0] a[1] a[2] a[3] a[4] k

theorem IsFunctional_xor5 : IsFunctional xor5 (allIxes (allIxes is_bit)) (allIxes is_bit) := by sorry

theorem xor5_def : xor5 a = SemaphoreMTB.Xor5_64_64_64_64_64 a[0] a[1] a[2] a[3] a[4] := by rfl

abbrev KeccakState := Vector (Vector (Vector F 64) 5) 5 × Vector F 64

theorem prop_of_allIxes {v : Vector α n} : allIxes prop v → ∀ {i : Nat} {h : i < n}, prop (v[i]'h) := by
  intro all i h
  apply all ⟨i, h⟩

-- theorem IsConstant_compose { f: (β → Prop) → Prop } {g : β → (γ → Prop) → Prop} {range : γ → Prop}
--   (f_constant : IsConstant f dom) (g_constant : ∀(c : Subtype dom), IsConstant (g c) range):
--   IsConstant (fun k => f (λx ↦ g x k)) range := by

theorem Rot_64_1_compose {next : Vector F 64 → (β → Prop) → Prop} (next_determined : ∀(v : Subtype (allIxes dom)), IsConstant (next v.val) range):
  ∀(v : Subtype (allIxes dom)), IsConstant (fun k => SemaphoreMTB.Rot_64_1 v.val (fun v => next v k)) range := by
  intro v
  apply IsConstant_compose
  apply IsConstant_of_IsFunctional'
  apply Rot_64_1_functional
  . exact dom
  . exact v.prop
  . assumption

theorem Xor_64_64_compose {next : Vector F 64 → (β → Prop) → Prop} (next_determined : ∀(v : Subtype (allIxes dom)), IsConstant (next v.val) range):
  ∀(v w: Subtype (allIxes dom)), IsConstant (fun k => SemaphoreMTB.Xor_64_64 v.val w.val (fun v => next v k)) range := by
  sorry
  -- intro v
  -- apply IsConstant_compose
  -- apply IsConstant_of_IsFunctional'
  -- apply Rot_64_1_functional
  -- . exact dom
  -- . exact v.prop
  -- . assumption

theorem getElem_allIxes {v : { v: Vector α n // allIxes prop v  }} {i : Nat} { i_small : i < n}:
  v.val[i]'i_small = ↑(Subtype.mk (v.val.get ⟨i, i_small⟩) (v.prop ⟨i, i_small⟩)) := by rfl

theorem getElem_allIxes₂ {v : { v: Vector (Vector α m) n // allIxes (allIxes prop) v  }} {i j: Nat} { i_small : i < n} { j_small : j < m}:
  (v.val[i]'i_small)[j]'j_small = ↑(Subtype.mk ((v.val.get ⟨i, i_small⟩).get ⟨j, j_small⟩) (v.prop ⟨i, i_small⟩ ⟨j, j_small⟩)) := by rfl

theorem subtype_allIxes_cons_nil {prop : α → Prop} {h : Subtype prop} : h.val ::ᵥ Vector.nil = (Subtype.mk (p := allIxes prop) (h.val ::ᵥ Vector.nil) (by simp; apply Subtype.property)).val
  := by rfl

theorem subtype_allIxes_cons {prop : α → Prop} {h : Subtype prop} {v : {v : Vector α n // allIxes prop v}}:
 h.val ::ᵥ v.val = (Subtype.mk (p := allIxes prop) (h.val ::ᵥ v.val) (by simp; apply And.intro <;> apply Subtype.property)).val
  := by rfl

theorem const_deterministic {v : Subtype prop}:
  IsConstant (fun k => k v.val) prop := by
  exists v; simp

theorem allIxes_indexed {v : {v : Vector α n // allIxes prop v}} {i : Nat} {i_small : i < n}:
  prop (v.val[i]'i_small) := v.prop ⟨i, i_small⟩

theorem allIxes_indexed₃ {v : {v : Vector (Vector (Vector α a) b) c // allIxes (allIxes (allIxes prop)) v}}
  {i : Nat} {i_small : i < c}
  {j : Nat} {j_small : j < b}
  {k : Nat} {k_small : k < a}:
  prop (((v.val[i]'i_small)[j]'j_small)[k]'k_small) :=
  v.prop ⟨i, i_small⟩ ⟨j, j_small⟩ ⟨k, k_small⟩

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


theorem zero_replicate : 0 ::ᵥ Vector.nil = Vector.replicate 1 (0 : F) := by rfl
theorem next_replicate : (0 : F) ::ᵥ Vector.replicate n (0 : F) = Vector.replicate (n + 1) 0 := by rfl

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

abbrev expected_result: Vector F 256 := vec![0,0,1,1,1,0,1,0,0,1,1,1,0,0,0,0,1,0,0,1,0,0,1,1,0,0,0,0,0,0,0,1,1,1,1,1,0,1,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,1,1,0,1,0,0,1,0,0,0,1,0,1,1,1,1,1,0,0,0,1,1,1,1,0,1,0,0,0,0,0,0,1,1,0,1,1,1,0,0,0,1,0,0,0,0,0,1,0,0,1,1,0,1,1,0,0,0,0,0,1,1,1,0,1,1,1,1,0,1,0,1,0,0,1,1,1,1,1,0,0,1,1,1,0,0,1,0,1,0,0,0,0,1,0,0,1,1,1,1,0,0,1,1,0,0,1,1,1,1,1,1,0,1,1,0,0,1,0,0,1,0,0,1,0,1,1,1,0,0,1,0,0,0,1,0,0,1,1,0,1,0,0,0,0,0,0,0,1,1,1,0,1,1,0,0,1,1,1,0,1,0,0,1,0,1,0,0,1,0,0,1,1,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,1,0,1,1,0,0,0,1,0,0,1,0,0,1,1]

abbrev rc: Vector (Vector F 64) 24 := vec![vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

theorem vector_get_replicate {i : Nat} {i_small : i < n} : (Vector.replicate n a)[i]'i_small = a := by
  induction n generalizing i with
  | zero => contradiction
  | succ n ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp [ih (i := i) (i_small := by linarith)]

@[simp]
theorem gateXorFunc_0_1_compute:
  gateXorFunc (0 : F) (1 : F) k = k 1 := by
  simp [gateXorFunc, Gates.xor]

-- theorem KeccakGadget_640_of_zero:
--   ∀k, SemaphoreMTB.KeccakGadget_640_64_24_640_256_24_1088_1 (Vector.replicate 640 (0 : F)) rc k = k expected_result := by
--   intro k
--   unfold SemaphoreMTB.KeccakGadget_640_64_24_640_256_24_1088_1
--   simp only [vector_get_replicate, gateXorFunc_def, gateXorFunc_0_1_compute]
--   conv => lhs; whnf
