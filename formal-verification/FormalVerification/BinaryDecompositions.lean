import FormalVerification
import FormalVerification.Common
import FormalVerification.ReducednessCheck
import ProvenZk

open SemaphoreMTB (F Order)

lemma ReducedToBinary_256_iff_Fin_toBitsLE {f : F} {v : Vector F 256}:
  Gates.to_binary f 256 v ∧ SemaphoreMTB.ReducedModRCheck_256 v ↔
  v = (Fin.toBitsLE ⟨f.val, Nat.lt_trans (Fin.is_lt f) (by decide)⟩).map Bool.toZMod := by
  rw [Gates.to_binary_iff_eq_Fin_ofBitsLE]
  apply Iff.intro
  . intro ⟨bin, red⟩
    rcases bin with ⟨v, a, b⟩
    subst_vars
    rw [ReducedModRCheck_256_semantics] at red
    have {h} : Fin.mk (ZMod.val ((Fin.ofBitsLE v).val : F)) h = Fin.ofBitsLE v := by
      simp [ZMod.val_cast_of_lt, red]
    simp [this]
  . rintro ⟨_⟩
    simp [ReducedModRCheck_256_semantics, ZMod.val_lt]

def rev_ix_256 (i : Fin 256): Fin 256 := 248 - (i / 8) * 8 + i % 8
def rev_ix_32 (i : Fin 32): Fin 32 := 24 - (i / 8) * 8 + i % 8

theorem rev_ix_256_surj : Function.Surjective rev_ix_256 := by
  intro i
  exists rev_ix_256 i
  revert i
  decide

theorem rev_ix_32_surj : Function.Surjective rev_ix_32 := by
  intro i
  exists rev_ix_32 i
  revert i
  decide

theorem ToReducedBigEndian_256_uncps {f k}:
  SemaphoreMTB.ToReducedBigEndian_256 f k ↔ k (Vector.permute rev_ix_256 ((Fin.toBitsLE ⟨f.val, Nat.lt_trans (Fin.is_lt f) (by decide)⟩).map Bool.toZMod)) := by
  unfold SemaphoreMTB.ToReducedBigEndian_256
  conv =>
    pattern _ ::ᵥ _
    change Vector.permute rev_ix_256 gate_0
  apply Iff.intro
  . intro ⟨g, a, b, c⟩
    rw [ReducedToBinary_256_iff_Fin_toBitsLE.mp ⟨a, b⟩] at c
    assumption
  . intro _
    simp_rw [←and_assoc, ReducedToBinary_256_iff_Fin_toBitsLE]
    simp [*]

theorem ToReducedBigEndian_32_uncps {f k}:
  SemaphoreMTB.ToReducedBigEndian_32 f k ↔ ∃(h : f.val < 2^32), k (Vector.permute rev_ix_32 ((Fin.toBitsLE ⟨f.val, h⟩).map Bool.toZMod)) := by
  unfold SemaphoreMTB.ToReducedBigEndian_32
  unfold SemaphoreMTB.ReducedModRCheck_32
  conv =>
    pattern _ ::ᵥ _
    change Vector.permute rev_ix_32 gate_0
  simp_rw [Gates.to_binary_iff_eq_fin_to_bits_le_of_pow_length_lt]
  apply Iff.intro
  . rintro ⟨_, ⟨_, ⟨_⟩⟩, _, cont⟩
    simp [*]
  . rintro ⟨_, _⟩
    simp [*]

theorem FromBinaryBigEndian_256_uncps {f k}:
  SemaphoreMTB.FromBinaryBigEndian_256 (Vector.map Bool.toZMod f) k ↔ k (Fin.ofBitsLE (Vector.permute rev_ix_256 f)).val := by
  unfold SemaphoreMTB.FromBinaryBigEndian_256
  conv =>
    pattern _ ::ᵥ _
    change Vector.permute rev_ix_256 (f.map Bool.toZMod)
  simp [←Vector.map_permute, Gates.from_binary_iff_eq_ofBitsLE_mod_order]

-- def ReducedToBinary_256_unique (f : F) :
--   UniqueSolution (fun x => Gates.to_binary f 256 x ∧ SemaphoreMTB.ReducedModRCheck_256 x) (Vector.map Bool.toZMod) := by
--   exists (Fin.toBitsLE ⟨f.val, Nat.lt_trans (Fin.is_lt f) (by decide)⟩)
--   intro x
--   rw [Gates.to_binary_iff_eq_Fin_ofBitsLE]
--   apply Iff.intro
--   . intro ⟨bin, red⟩
--     rcases bin with ⟨v, a, b⟩
--     subst_vars
--     rw [ReducedModRCheck_256_semantics] at red
--     have {h} : Fin.mk (ZMod.val ((Fin.ofBitsLE v).val : F)) h = Fin.ofBitsLE v := by
--       simp [ZMod.val_cast_of_lt, red]
--     simp [this]
--   . rintro ⟨_⟩
--     simp [ReducedModRCheck_256_semantics, ZMod.val_lt]

-- -- theorem inj_of_comp_inj (proj : β → γ) (fn : α → β) (h : Function.Injective (proj ∘ fn)):
-- --   Function.Injective fn := by
-- --   intro x y h'
-- --   apply h
-- --   simp [h']

-- -- theorem Vector.map_inj (h : Function.Injective f):
-- --   Function.Injective (Vector.map f (n := n)) := by
-- --   intro x y h
-- --   induction n with
-- --   | zero => cases x using Vector.casesOn; cases y using Vector.casesOn; rfl
-- --   | succ n ih =>
-- --     cases x using Vector.casesOn
-- --     cases y using Vector.casesOn
-- --     simp_rw [map_cons, eq_cons_iff, tail_cons, head_cons] at h
-- --     cases h
-- --     congr
-- --     . apply h; assumption
-- --     . apply ih; assumption

-- -- theorem SubVector_lift_inj {prop : α → Prop}:
-- --   Function.Injective (SubVector.lift (prop := prop) (n := n)) := by
-- --   unfold SubVector.lift
-- --   apply inj_of_comp_inj (proj := Subtype.val)
-- --   apply Vector.map_inj
-- --   apply Subtype.eq

-- -- lemma embedBit_inj : Function.Injective (@embedBit Order):= by
-- --   intro x y h
-- --   cases x <;> {cases y <;> cases h; rfl}

-- -- lemma castLE_inj : Function.Injective (Fin.castLE prop) := by
-- --   intro _ _ h
-- --   injection h with h;
-- --   apply Fin.eq_of_veq
-- --   assumption

-- -- theorem fin_to_bits_le_inj : Function.Injective (fin_to_bits_le (d := d)) := by
-- --   apply Function.LeftInverse.injective (g := fun x => ⟨recover_binary_nat x, binary_nat_lt _⟩)
-- --   intro
-- --   simp


-- theorem ReducedToBinary_256_inj: Function.Injective (fun x => (ReducedToBinary_256_unique x).val) := by
--   unfold ReducedToBinary_256_unique
--   intro x y h
--   simp [Fin.toBitsLE] at h
--   apply Fin.eq_of_veq h


-- -- def ConstantOf_compose_existential₂ { f : α → Prop } {embf : α' → α} {g : α → (β → Prop) → Prop} {embg : β' → β}
-- --   (f_uniq : UniqueSolution f embf) (g_constant : ∀c, ConstantOf (g (embf c)) embg):
-- --   ConstantOf (fun k => ∃x, f x ∧ g x k) embg := by
-- --   rcases f_uniq with ⟨c, _⟩
-- --   rcases g_constant c with ⟨g, _⟩
-- --   exists g
-- --   simp [*]

-- -- def ConstantOf_compose_existential₂ { f₁ : α → Prop } { f₂ : α → Prop } {g : α → (β → Prop) → Prop} {range : β → Prop}
-- --   (f_uniq : UniqueSolution (fun x => f₁ x ∧ f₂ x) dom) (g_constant : ∀(c : Subtype dom), ConstantOf (g c) range):
-- --   ConstantOf (fun k => ∃x, f₁ x ∧ f₂ x ∧ g x k) range := by
-- --   rcases f_uniq with ⟨c, funiq⟩
-- --   rcases g_constant c with ⟨g, gconst⟩
-- --   exists g
-- --   intro k
-- --   simp
-- --   apply Iff.intro
-- --   . intro h'
-- --     rcases h' with ⟨x, _, _, r⟩
-- --     rw [←gconst k]
-- --     rw [←(funiq x).mp] <;> tauto
-- --   . intro h
-- --     exists c.val
-- --     have := funiq c.val
-- --     simp at this
-- --     cases this
-- --     have := gconst k
-- --     rw [this]
-- --     tauto

-- -- theorem ConstantOf_compose_inj
-- --   {p₁ p₂ : α → β → Prop}
-- --   {g : β → (γ → Prop) → Prop}
-- --   {f_uniq : ∀(a:α), UniqueSolution (fun x => p₁ a x ∧ p₂ a x) dom}
-- --   {g_constant : ∀(c : Subtype dom), ConstantOf (g c) range}
-- --   (f_uniq_inj : Function.Injective (fun x => (f_uniq x).val))
-- --   (g_constant_inj : Function.Injective (fun x => (g_constant x).val)):
-- --   Function.Injective (fun x => (ConstantOf_compose_existential₂ (f_uniq x) g_constant).val) := by
-- --   intro _ _ h
-- --   apply f_uniq_inj
-- --   apply g_constant_inj
-- --   exact h

-- -- theorem ConstantOf_compose_inj
-- --   { f : α → Prop } {embf : α' → α} {g : α → (β → Prop) → Prop} {embg : β' → β}
-- --   { f_uniq : UniqueSolution f embf} {g_constant : ∀c, ConstantOf (g (embf c)) embg}




-- --   (f_uniq : UniqueSolution f embf) (g_constant : ∀c, ConstantOf (g (embf c)) embg)


-- def permute (fn : Fin m → Fin n) (v : Vector α n): Vector α m :=
--   Vector.ofFn (fun i => v[fn i])

-- -- theorem allElems_permute {fn : Fin m → Fin n} {v : Vector α n} (hp : Vector.allElems prop v): Vector.allElems prop (permute fn v) := by
-- --   intro a ha
-- --   have := (Vector.mem_iff_get _ _).mp ha
-- --   rcases this with ⟨i, hi⟩
-- --   simp [permute, GetElem.getElem] at hi
-- --   cases hi
-- --   apply hp
-- --   simp

-- def rev_ix_256 (i : Fin 256): Fin 256 := 248 - (i / 8) * 8 + i % 8

-- theorem rev_ix_256_surj : Function.Surjective rev_ix_256 := by
--   intro i
--   exists rev_ix_256 i
--   revert i
--   decide

-- theorem Vector.map_permute {p : Fin m → Fin n} {f : α → β} {v : Vector α n}:
--   Vector.map f (permute p v) = permute p (v.map f) := by
--   simp [permute]

-- -- def ToReducedBigEndian_256_constant (f : F):
-- --   ConstantOf (fun k => SemaphoreMTB.ToReducedBigEndian_256 f k) (Vector.map Bool.toZMod) := by
-- --   exists (permute rev_ix_256 (Fin.toBitsLE ⟨f.val, Nat.lt_trans (ZMod.val_lt f) (by decide)⟩))
-- --   unfold SemaphoreMTB.ToReducedBigEndian_256
-- --   conv =>
-- --     pattern _ ::ᵥ _
-- --     change permute rev_ix_256 gate_0
-- --   intro k
-- --   apply Iff.to_eq
-- --   apply Iff.intro
-- --   .



--   -- unfold SemaphoreMTB.ToReducedBigEndian_256
--   -- simp_rw [←and_assoc]
--   -- apply ConstantOf_compose_existential
--   -- . apply ReducedToBinary_256_unique
--   -- intro x
--   -- exists (permute rev_ix_256 x)
--   -- intro k
--   -- apply congrArg
--   -- rw [Vector.map_permute]
--   -- rfl

-- -- theorem Vector.permute_inj {n : Nat} {fn : Fin m → Fin n} (perm_surj : Function.Surjective fn): Function.Injective (permute (α := α) fn) := by
-- --   intro v₁ v₂ h
-- --   ext i
-- --   rcases perm_surj i with ⟨j, i_inv⟩
-- --   have : (permute fn v₁).get j = (permute fn v₂).get j := by rw [h]
-- --   simp [permute, GetElem.getElem] at this
-- --   subst_vars
-- --   assumption

-- -- theorem subtype_inj {α β : Type} {prop : β → Prop} {f : α → Subtype prop }:
-- --   Function.Injective (fun x => (f x).val) → Function.Injective f  := by
-- --   intro h _ _ heq
-- --   apply h
-- --   simp [heq]

-- -- theorem ToReducedBigEndian_256_injective: Function.Injective (fun k => (ToReducedBigEndian_256_constant k).val) := by
-- --   unfold ToReducedBigEndian_256_constant



--   apply ConstantOf_compose_inj
--   . apply ReducedToBinary_256_inj
--   . conv => arg 1; intro x; whnf
--     apply subtype_inj
--     apply Function.Injective.comp (f := Subtype.val) (g := permute rev_ix_256)
--     . apply permute_inj
--       intro i
--       exists rev_ix_256 i
--       revert i
--       decide
--     . intros i j _; cases i; cases j; simpa [*]



-- def Gates_to_binary_unique {d : Nat} (d_small : 2 ^ d < Order) (f : {f : F // f.val < 2 ^ d}):
--   UniqueSolution (fun x => Gates.to_binary f.val d x) (Vector.allElems is_bit) := by
--   let r := SubVector.lift (Vector.map (fun x => @embedBit Order x) (fin_to_bits_le (d := d) ⟨Fin.val f.val, f.prop⟩))
--   exists r
--   intro x
--   unfold Gates.to_binary
--   have res_binary : is_vector_binary r.val := by
--     simp [is_vector_binary, SubVector.lift, Subtype.property]
--   have res_lt_order : recover_binary_nat (Vector.map bitCases (SubVector.lower r)) < Order := by
--     simp
--     exact f.val.prop

--   apply Iff.intro
--   . intro ⟨bin_rec, is_bin⟩

--     have is_bin' := is_bin
--     let y := Subtype.mk x is_bin
--     have : x = y.val := rfl
--     generalize y = z at this
--     subst this
--     clear y is_bin

--     rw [recover_binary_zmod_bit is_bin', ←binary_nat_zmod_equiv] at bin_rec
--     rcases f with ⟨⟨_, _⟩, _⟩
--     apply_fun Fin.val at bin_rec
--     have res_small : recover_binary_nat (vector_zmod_to_bit z.val) < Order :=
--       LT.lt.trans (binary_nat_lt _) d_small
--     rw [Fin.val_cast_of_lt res_small] at bin_rec
--     subst bin_rec
--     simp_rw [ fin_to_bits_le_recover_binary_nat
--             , vector_zmod_to_bit
--             , Vector.map_map
--             , SubVector_map_cast_lower
--             , embedBit_zmod_to_bit
--             , Vector.map_id'
--             , SubVector_lower_lift
--             ]
--   . intro h; subst h
--     refine ⟨?_, res_binary⟩
--     rw [recover_binary_zmod_bit res_binary, ←binary_nat_zmod_equiv]
--     rw [vector_zmod_to_bit_bitCases]
--     apply Fin.eq_of_val_eq
--     rw [Fin.val_cast_of_lt res_lt_order]
--     simp

-- def Gates_to_binary_domain {f : F} : Gates.to_binary f d out → Fin.val f < 2 ^ d := by
--   unfold Gates.to_binary
--   intro ⟨rec_zmod, is_bin⟩
--   rw [recover_binary_zmod_bit is_bin, ←binary_nat_zmod_equiv] at rec_zmod
--   cases f
--   injection rec_zmod with rec_zmod
--   subst rec_zmod
--   cases (lt_or_le (2^d) Order) with
--   | inl h =>
--     have : recover_binary_nat (vector_zmod_to_bit out) < Order := by
--       apply LT.lt.trans (binary_nat_lt _) h
--     unfold Order at this
--     simp_rw [Nat.mod_eq_of_lt this]
--     apply binary_nat_lt
--   | inr h =>
--     apply lt_of_lt_of_le _ h
--     apply Nat.mod_lt
--     decide

-- def Gates_to_binary_inj (d_small : 2 ^ d < Order):
--   Function.Injective (fun (x : {x : F // x.val < 2 ^ d}) => (Gates_to_binary_unique d_small x).val) := by
--   apply Function.Injective.comp SubVector_lift_inj
--   apply Function.Injective.comp (g := Vector.map embedBit)
--   apply Vector.map_inj
--   apply embedBit_inj
--   apply Function.Injective.comp (g := fin_to_bits_le)
--   apply fin_to_bits_le_inj
--   intro i j h
--   rcases i with ⟨⟨i, _⟩, _⟩
--   rcases j with ⟨⟨j, _⟩, _⟩
--   simp at h
--   subst h
--   rfl

-- def rev_ix_32 (i : Fin 32): Fin 32 := 24 - (i / 8) * 8 + i % 8

-- def ToReducedBigEndian_32_constant (f : {f : F // Fin.val f < 2 ^ 32}): ConstantOf (fun k => SemaphoreMTB.ToReducedBigEndian_32 f.val k) (Vector.allElems is_bit) :=
--   ConstantOf_compose_existential₂
--     ⟨(Gates_to_binary_unique (by decide) f).val, by simp [SemaphoreMTB.ReducedModRCheck_32, (Gates_to_binary_unique (by decide) f).uniq]⟩
--     (fun x => ConstantOf_constant (x := permute rev_ix_32 x.val) (by apply allElems_permute; apply x.prop))

-- theorem ToReducedBigEndian_32_domain {f : F}:
--   ∀k, SemaphoreMTB.ToReducedBigEndian_32 f k → Fin.val f < 2 ^ 32 := by
--   unfold SemaphoreMTB.ToReducedBigEndian_32
--   intro k
--   intro ⟨_, to_bin, _⟩
--   exact Gates_to_binary_domain to_bin

-- theorem constant_domain_rw {g : α → (β → Prop) → Prop}
--   (const : (∀x : Subtype prop, ConstantOf (fun k => g x.val k) range))
--   (dom : ∀ k, g x k → prop x):
--   (h : g x k) → k (const ⟨x, dom _ h⟩).val := by
--   intro h
--   rwa [←(const ⟨x, dom _ h⟩).equiv k]

-- theorem ToReducedBigEndian_32_inj : Function.Injective (fun x => (ToReducedBigEndian_32_constant x).val) := by
--   apply ConstantOf_compose_inj
--   . simp; apply Gates_to_binary_inj
--   . conv => arg 1; intro x; whnf
--     apply subtype_inj
--     apply Function.Injective.comp (f := Subtype.val) (g := permute rev_ix_32)
--     . apply permute_inj
--       intro i
--       exists rev_ix_32 i
--       revert i
--       decide
--     . intros i j _; cases i; cases j; simpa [*]

-- def Gates.from_binary_unique (v : Vector F d):
--   UniqueSolution (fun x => Gates.from_binary v x) (fun _ => True) := by
--   unfold from_binary
--   simp [UniqueSolution]
--   exists Subtype.mk (recover_binary_zmod' v) True.intro
--   intro
--   apply Iff.intro <;> {intro ; simp [*]}

-- def FromBinaryBigEndian_256_constant (f : Vector F 256):
--   ConstantOf (fun k => SemaphoreMTB.FromBinaryBigEndian_256 f k) (fun _ => True) :=
--   ConstantOf_compose_existential
--     (Gates.from_binary_unique (permute rev_ix_256 f))
--     (fun _ => ConstantOf_constant True.intro)
