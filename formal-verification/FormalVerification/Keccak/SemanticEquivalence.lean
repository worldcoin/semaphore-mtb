import FormalVerification
import ProvenZK
import Mathlib

open SemaphoreMTB (F Order)

-- def Order : ℕ := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
-- abbrev F := ZMod Order

variable [Fact (Nat.Prime Order)]

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

theorem is_vector_binary_indexed {n : Nat} {v : Vector F n} : is_vector_binary v ↔ ∀(i: Fin n), is_bit v[i] := by
  induction v using Vector.inductionOn with
  | h_nil => simp [is_vector_binary]
  | h_cons ih => simp [is_vector_binary_cons, ih, forall_fin_succ]

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

def IsFunctional (f : α → (β → Prop) → Prop) (domain : α → Prop) (range : β → Prop): Prop :=
  ∃(g : α → β), ∀a k, domain a → (f a k ↔ k (g a)) ∧ range (g a)

-- def HasRange (f : α → (β → Prop) → Prop)

def ofFnCont : (Fin n → (α → Prop) → Prop) → (Vector α n → Prop) → Prop :=
  match n with
  | 0 => fun _ k => k Vector.nil
  | Nat.succ _ => fun gen k => gen 0 fun r => ofFnCont (fun i => gen i.succ) (fun i => k (r ::ᵥ i))

def ofFnMap {n} (gen : α → (β → Prop) → Prop) : Vector α n → (Vector β n → Prop) → Prop :=
  fun v => ofFnCont (fun i k => gen v[i] k)

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

theorem ofFnMap_functional {gen : α → (β → Prop) → Prop} (gen_functional : IsFunctional gen domain range):
  IsFunctional (ofFnMap (n := n) gen) (allIxes domain) (allIxes range) := by
  unfold ofFnMap
  induction n with
  | zero =>
    exists (fun _ => Vector.nil)
    simp [ofFnCont, allIxes]
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

def gateAndFunc (a : F × F) (k : F → Prop) : Prop :=
  ∃r, Gates.and a.1 a.2 r ∧ k r

theorem gateAndFunc_def : (∃r, Gates.and a b r ∧ k r) ↔ gateAndFunc (a, b) k := by
  rfl

theorem and_functional :
  IsFunctional gateAndFunc (fun (a : F×F) => Gates.is_bool a.1 ∧ Gates.is_bool a.2) Gates.is_bool:= by
  exists (fun a => a.1 * a.2)
  intro ⟨a, b⟩ k dom
  unfold gateAndFunc
  unfold Gates.and
  apply Iff.intro
  . simp; intros; subst_vars; assumption
  . simp at dom
    simp
    intros
    exists a * b
    tauto

def and_64_64Func (a : Vector F 64 × Vector F 64) :=
  ofFnMap gateAndFunc (Vector.ofFn (n := 64) (fun i => (a.1[i], a.2[i])))

theorem and_64_64_def : SemaphoreMTB.And_64_64 A B k = and_64_64Func (A,B) k := by rfl

theorem and_64_64_functional : IsFunctional and_64_64Func (fun (a, b) => is_vector_binary a ∧ is_vector_binary b) := by
  simp [and_64_64Func]
  apply arg_transform_functional
  apply ofFnMap_functional
  apply and_functional
  intro _
  simp [is_vector_binary_indexed₂, GetElem.getElem]

theorem IsFunctional_compose {f : α → (β → Prop)} {g : β → (γ → Prop)}:
  -- IsFunctional f → IsFunctional g → IsFunctional (fun a k => ∃b, f a (λx ↦ g x b ∧ k b)) := by
  -- intro ⟨f, hf⟩ ⟨g, hg⟩
  -- exists (fun a => let ⟨b, _⟩ := hf a (λx ↦ True)
  --                  g b)
  -- intro a k
  -- rw [hf, hg]
  -- apply propext
  -- apply Iff.intro
  -- . intro ⟨b, ⟨_, _⟩, _⟩
  --   exact ⟨b, _⟩
  -- . intro ⟨b, _⟩
  --   exact ⟨b, ⟨_, _⟩, _⟩ )}

structure IsFunction (f : α → (β → Prop) → Prop) : Prop :=
  deterministic : ∀ a p q, f a (λx ↦ x = p) ∧ f a (λx ↦ x = q) → p = q
  total : ∀ a, ∃ p, f a (λx ↦ x = p)
  returns : ∀ a, ¬f a (λ_ ↦ False)

theorem IsFunction_exists {f : α → (β → Prop) → Prop} :
  IsFunction f → ∃(g : α → β), ∀ a k, f a k ↔ k (g a) := by
  intro Hf
  exists (fun a => let (r, _) := (Hf.total a).choose)
  intro a k

-- theorem IsFunction_compose {}
