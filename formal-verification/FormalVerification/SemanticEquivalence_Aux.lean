import FormalVerification
import FormalVerification.BinaryReps.Basic
import FormalVerification.BinaryReps.SemanticEquivalence
import FormalVerification.Keccak.SemanticEquivalence
import ProvenZk.Gates

open SemaphoreMTB (F Order)

-- variable [Fact (Nat.Prime Order)]
axiom ord_prime : Nat.Prime Order
instance : Fact (Nat.Prime Order) := ⟨ord_prime⟩

def RC : Vector (Fin (2 ^ 64)) 24 := vec![0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A, 0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A, 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

def RCBits : SubVector (Vector F 64) 24 (allIxes is_bit):=
  SubVector.lift (Vector.map (fun x => SubVector.lift (Vector.map embedBit (fin_to_bits_le x))) RC)

def ofFnGet (v : Vector F d) : Vector F d := Vector.ofFn fun i => v[i.val]'i.prop
instance : HAppend (Vector α d₁) (Vector α d₂) (Vector α (d₁ + d₂)) := ⟨Vector.append⟩

def DeletionMbuCircuit_4_4_30_4_4_30_Fold (InputHash: F) (DeletionIndices: Vector F 4) (PreRoot: F) (PostRoot: F) (IdComms: Vector F 4) (MerkleProofs: Vector (Vector F 30) 4): Prop :=
    SemaphoreMTB.ToReducedBigEndian_32 DeletionIndices[0] fun gate_0 =>
    SemaphoreMTB.ToReducedBigEndian_32 DeletionIndices[1] fun gate_1 =>
    SemaphoreMTB.ToReducedBigEndian_32 DeletionIndices[2] fun gate_2 =>
    SemaphoreMTB.ToReducedBigEndian_32 DeletionIndices[3] fun gate_3 =>
    SemaphoreMTB.ToReducedBigEndian_256 PreRoot fun gate_4 =>
    SemaphoreMTB.ToReducedBigEndian_256 PostRoot fun gate_5 =>
    SemaphoreMTB.KeccakGadget_640_64_24_640_256_24_1088_1
      (ofFnGet gate_0 ++ ofFnGet gate_1 ++ ofFnGet gate_2 ++ ofFnGet gate_3 ++ ofFnGet gate_4 ++ ofFnGet gate_5) RCBits.val fun gate_6 =>
    SemaphoreMTB.FromBinaryBigEndian_256 gate_6 fun gate_7 =>
    Gates.eq InputHash gate_7 ∧
    SemaphoreMTB.DeletionProof_4_4_30_4_4_30 DeletionIndices PreRoot IdComms MerkleProofs fun gate_9 =>
    Gates.eq gate_9 PostRoot ∧
    True

theorem DeletionCircuit_folded {InputHash PreRoot PostRoot : F} {DeletionIndices IdComms : Vector F 4} {MerkleProofs: Vector (Vector F 30) 4}:
  SemaphoreMTB.DeletionMbuCircuit_4_4_30_4_4_30 InputHash DeletionIndices PreRoot PostRoot IdComms MerkleProofs =
  DeletionMbuCircuit_4_4_30_4_4_30_Fold InputHash DeletionIndices PreRoot PostRoot IdComms MerkleProofs := by rfl

@[simp]
theorem ofFnGet_id : ofFnGet v = v := by simp [ofFnGet, GetElem.getElem]

@[simp]
theorem Vector.hAppend_toList {v₁ : Vector α d₁} {v₂ : Vector α d₂}:
  (v₁ ++ v₂).toList = v₁.toList ++ v₂.toList := by rfl

theorem Vector.append_inj {v₁ w₁ : Vector α d₁} {v₂ w₂ : Vector α d₂}:
  v₁ ++ v₂ = w₁ ++ w₂ → v₁ = w₁ ∧ v₂ = w₂ := by
  intro h
  induction v₁, w₁ using Vector.inductionOn₂ with
  | nil =>
    apply And.intro rfl
    apply Vector.eq
    have := congrArg toList h
    simp at this
    assumption
  | cons ih =>
    have := congrArg toList h
    simp at this
    rcases this with ⟨h₁, h₂⟩
    rw [←hAppend_toList, ←hAppend_toList] at h₂
    have := Vector.eq _ _ h₂
    have := ih this
    cases this
    subst_vars
    apply And.intro <;> rfl

theorem allIxes_toList : allIxes prop v ↔ ∀ i, prop (v.toList.get i) := by
  unfold allIxes
  apply Iff.intro
  . intro h i
    rcases i with ⟨i, p⟩
    simp at p
    simp [GetElem.getElem, Vector.get] at h
    have := h ⟨i, p⟩
    conv at this => arg 1; whnf
    exact this
  . intro h i
    simp [GetElem.getElem, Vector.get]
    rcases i with ⟨i, p⟩
    have := h ⟨i, by simpa⟩
    conv at this => arg 1; whnf
    exact this

theorem allIxes_append {v₁ : Vector α n₁} {v₂ : Vector α n₂} : allIxes prop (v₁ ++ v₂) ↔ allIxes prop v₁ ∧ allIxes prop v₂ := by
  simp [allIxes_toList]
  apply Iff.intro
  . intro h
    apply And.intro
    . intro i
      rcases i with ⟨i, hp⟩
      simp at hp
      rw [←List.get_append]
      exact h ⟨i, (by simp; apply Nat.lt_add_right; assumption)⟩
    . intro i
      rcases i with ⟨i, hp⟩
      simp at hp
      have := h ⟨n₁ + i, (by simpa)⟩
      rw [List.get_append_right] at this
      simp at this
      exact this
      . simp
      . simpa
  . intro ⟨l, r⟩
    intro ⟨i, hi⟩
    simp at hi
    cases lt_or_ge i n₁ with
    | inl hp =>
      rw [List.get_append _ (by simpa)]
      exact l ⟨i, (by simpa)⟩
    | inr hp =>
      rw [List.get_append_right]
      have := r ⟨i - n₁, (by simp; apply Nat.sub_lt_left_of_lt_add; exact LE.le.ge hp; assumption )⟩
      simp at this
      simpa
      . simp; exact LE.le.ge hp
      . simp; apply Nat.sub_lt_left_of_lt_add; exact LE.le.ge hp; assumption

theorem SubVector_append {v₁ : Vector α d₁} {prop₁ : allIxes prop v₁ } {v₂ : Vector α d₂} {prop₂ : allIxes prop v₂}:
  (Subtype.mk v₁ prop₁).val ++ (Subtype.mk v₂ prop₂).val =
  (Subtype.mk (v₁ ++ v₂) (allIxes_append.mpr ⟨prop₁, prop₂⟩)).val := by eq_refl

def KeccakGadget_640_64_24_640_256_24_1088_1_constant'
  (input : Vector F 640)
  (prop_input : allIxes is_bit input)
  ( rc : { v : Vector (Vector F 64) 24 // allIxes (allIxes is_bit) v } ):
  ConstantOf (SemaphoreMTB.KeccakGadget_640_64_24_640_256_24_1088_1 input rc.val) (allIxes is_bit) :=
  KeccakGadget_640_64_24_640_256_24_1088_1_constant ⟨input, prop_input⟩ rc

theorem Deletion_InputHash_deterministic :
  SemaphoreMTB.DeletionMbuCircuit_4_4_30_4_4_30 InputHash₁ DeletionIndices PreRoot PostRoot IdComms₁ MerkleProofs₁ ∧
  SemaphoreMTB.DeletionMbuCircuit_4_4_30_4_4_30 InputHash₂ DeletionIndices PreRoot PostRoot IdComms₂ MerkleProofs₂ →
  InputHash₁ = InputHash₂ := by
  repeat rw [DeletionCircuit_folded]
  unfold DeletionMbuCircuit_4_4_30_4_4_30_Fold
  intro ⟨h₁, h₂⟩
  repeat have h₁ := constant_domain_rw ToReducedBigEndian_32_constant ToReducedBigEndian_32_domain h₁
  repeat have h₂ := constant_domain_rw ToReducedBigEndian_32_constant ToReducedBigEndian_32_domain h₂
  rw [ (ToReducedBigEndian_256_constant _).equiv
     , (ToReducedBigEndian_256_constant _).equiv
     , (KeccakGadget_640_64_24_640_256_24_1088_1_constant' _ (by simp [ofFnGet_id, allIxes_append, Subtype.property]) _).equiv
     , (FromBinaryBigEndian_256_constant _).equiv
     ] at h₁ h₂
  rcases h₁ with ⟨h₁, _⟩
  rcases h₂ with ⟨h₂, _⟩
  rw [h₁, h₂]

def reducedKeccak640 (v : SubVector F 640 is_bit) : F :=
  (FromBinaryBigEndian_256_constant ↑(KeccakGadget_640_64_24_640_256_24_1088_1_constant' v.val v.prop RCBits).val).val.val

theorem reducedKeccak640_zeros :
  reducedKeccak640 (SubVector.lift (Vector.replicate 640 bZero)) = 4544803827027086362579185658884299814463816764684804205918064517636252260498 := by
  native_decide

theorem reducedKeccak640_ones :
  reducedKeccak640 (SubVector.lift (Vector.replicate 640 bOne)) = 1953461151768174703550518710286555794214949287664819893310466469381641334512 := by
  native_decide

def ReducedKeccak_640_collision_resistance : Prop :=
  ∀{v₁ v₂ : SubVector F 640 is_bit},
   reducedKeccak640 v₁ = reducedKeccak640 v₂ →
   v₁ = v₂

lemma ReducedKeccak_640_collision_rw :
  ReducedKeccak_640_collision_resistance →
  ∀{v₁ v₂ : Vector F 640} {prop₁ : allIxes is_bit v₁} {prop₂ : allIxes is_bit v₂},
   (FromBinaryBigEndian_256_constant ↑(KeccakGadget_640_64_24_640_256_24_1088_1_constant' v₁ prop₁ RCBits).val).val.val =
   (FromBinaryBigEndian_256_constant ↑(KeccakGadget_640_64_24_640_256_24_1088_1_constant' v₂ prop₂ RCBits).val).val.val →
   v₁ = v₂ := by
  intro kr _ _ _ _ h
  simp [ReducedKeccak_640_collision_resistance, reducedKeccak640] at kr
  simp [KeccakGadget_640_64_24_640_256_24_1088_1_constant'] at h
  apply kr
  exact h
  all_goals assumption

theorem Deletion_InputHash_injective :
  ReducedKeccak_640_collision_resistance →
  SemaphoreMTB.DeletionMbuCircuit_4_4_30_4_4_30 InputHash DeletionIndices₁ PreRoot₁ PostRoot₁ IdComms₁ MerkleProofs₁ ∧
  SemaphoreMTB.DeletionMbuCircuit_4_4_30_4_4_30 InputHash DeletionIndices₂ PreRoot₂ PostRoot₂ IdComms₂ MerkleProofs₂ →
  DeletionIndices₁ = DeletionIndices₂ ∧ PreRoot₁ = PreRoot₂ ∧ PostRoot₁ = PostRoot₂ := by
  intro kr
  repeat rw [DeletionCircuit_folded]
  unfold DeletionMbuCircuit_4_4_30_4_4_30_Fold
  intro ⟨h₁, h₂⟩
  repeat have h₁ := constant_domain_rw ToReducedBigEndian_32_constant ToReducedBigEndian_32_domain h₁
  repeat have h₂ := constant_domain_rw ToReducedBigEndian_32_constant ToReducedBigEndian_32_domain h₂
  simp only [ofFnGet_id] at h₁ h₂
  rw [ (ToReducedBigEndian_256_constant _).equiv
     , (ToReducedBigEndian_256_constant _).equiv
     , (KeccakGadget_640_64_24_640_256_24_1088_1_constant' _ (by simp [ofFnGet_id, allIxes_append, Subtype.property]) _).equiv
     , (FromBinaryBigEndian_256_constant _).equiv
     ] at h₁ h₂
  rcases h₁ with ⟨h₁, _⟩
  rcases h₂ with ⟨h₂, _⟩
  have := Eq.trans (Eq.symm h₁) h₂
  have := ReducedKeccak_640_collision_rw kr this
  have := Vector.append_inj this
  rcases this with ⟨this, hPostRoot⟩
  have := Vector.append_inj this
  rcases this with ⟨this, hPreRoot⟩
  have := Vector.append_inj this
  rcases this with ⟨this, d₃⟩
  have := Vector.append_inj this
  rcases this with ⟨this, d₂⟩
  have := Vector.append_inj this
  rcases this with ⟨d₀, d₁⟩
  have hPostRoot := ToReducedBigEndian_256_injective (Subtype.eq hPostRoot)
  have hPreRoot := ToReducedBigEndian_256_injective (Subtype.eq hPreRoot)
  refine ⟨?_, hPreRoot, hPostRoot⟩
  have d₀ := ToReducedBigEndian_32_inj (Subtype.eq d₀)
  have d₁ := ToReducedBigEndian_32_inj (Subtype.eq d₁)
  have d₂ := ToReducedBigEndian_32_inj (Subtype.eq d₂)
  have d₃ := ToReducedBigEndian_32_inj (Subtype.eq d₃)
  simp [GetElem.getElem] at d₀ d₁ d₂ d₃
  ext i
  fin_cases i <;> simpa

def InsertionMbuCircuit_4_30_4_4_30_Fold (InputHash: F) (StartIndex: F) (PreRoot: F) (PostRoot: F) (IdComms: Vector F 4) (MerkleProofs: Vector (Vector F 30) 4): Prop :=
    SemaphoreMTB.ToReducedBigEndian_32 StartIndex fun gate_0 =>
    SemaphoreMTB.ToReducedBigEndian_256 PreRoot fun gate_1 =>
    SemaphoreMTB.ToReducedBigEndian_256 PostRoot fun gate_2 =>
    SemaphoreMTB.ToReducedBigEndian_256 IdComms[0] fun gate_3 =>
    SemaphoreMTB.ToReducedBigEndian_256 IdComms[1] fun gate_4 =>
    SemaphoreMTB.ToReducedBigEndian_256 IdComms[2] fun gate_5 =>
    SemaphoreMTB.ToReducedBigEndian_256 IdComms[3] fun gate_6 =>
    SemaphoreMTB.KeccakGadget_1568_64_24_1568_256_24_1088_1
        (ofFnGet gate_0 ++ ofFnGet gate_1 ++ ofFnGet gate_2 ++ ofFnGet gate_3 ++ ofFnGet gate_4 ++ ofFnGet gate_5 ++ ofFnGet gate_6) RCBits.val fun gate_7 =>
    SemaphoreMTB.FromBinaryBigEndian_256 gate_7 fun gate_8 =>
    Gates.eq InputHash gate_8 ∧
    SemaphoreMTB.InsertionProof_4_30_4_4_30 StartIndex PreRoot IdComms MerkleProofs fun gate_10 =>
    Gates.eq gate_10 PostRoot ∧
    True

theorem InsertionMbuCircuit_4_30_4_4_30_folded:
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash StartIndex PreRoot PostRoot IdComms MerkleProofs =
  InsertionMbuCircuit_4_30_4_4_30_Fold InputHash StartIndex PreRoot PostRoot IdComms MerkleProofs := by rfl

def KeccakGadget_1568_64_24_1568_256_24_1088_1_constant'
  (input : Vector F 1568)
  (prop_input : allIxes is_bit input)
  ( rc : { v : Vector (Vector F 64) 24 // allIxes (allIxes is_bit) v } ):
  ConstantOf (SemaphoreMTB.KeccakGadget_1568_64_24_1568_256_24_1088_1 input rc.val) (allIxes is_bit) :=
  KeccakGadget_1568_64_24_1568_256_24_1088_1_constant ⟨input, prop_input⟩ rc

theorem Insertion_InputHash_deterministic :
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash₁ StartIndex PreRoot PostRoot IdComms MerkleProofs₁ ∧
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash₂ StartIndex PreRoot PostRoot IdComms MerkleProofs₂ →
  InputHash₁ = InputHash₂ := by
  repeat rw [InsertionMbuCircuit_4_30_4_4_30_folded]
  unfold InsertionMbuCircuit_4_30_4_4_30_Fold
  intro ⟨h₁, h₂⟩
  have h₁ := constant_domain_rw ToReducedBigEndian_32_constant ToReducedBigEndian_32_domain h₁
  have h₂ := constant_domain_rw ToReducedBigEndian_32_constant ToReducedBigEndian_32_domain h₂
  repeat rw [(ToReducedBigEndian_256_constant _).equiv] at h₁ h₂
  rw [ (KeccakGadget_1568_64_24_1568_256_24_1088_1_constant' _ (by simp [ofFnGet_id, allIxes_append, Subtype.property]) _).equiv
     , (FromBinaryBigEndian_256_constant _).equiv
     ] at h₁ h₂
  rcases h₁ with ⟨h₁, _⟩
  rcases h₂ with ⟨h₂, _⟩
  rw [h₁, h₂]

def reducedKeccak1568 (v : SubVector F 1568 is_bit) : F :=
  (FromBinaryBigEndian_256_constant ↑(KeccakGadget_1568_64_24_1568_256_24_1088_1_constant' v.val v.prop RCBits).val).val.val

theorem reducedKeccak1568_zeros :
  reducedKeccak1568 (SubVector.lift (Vector.replicate 1568 bZero)) = 0x2872693cd1edb903471cf4a03c1e436f32dccf7ffa2218a4e0354c2514004511 := by
  native_decide

theorem reducedKeccak1568_ones :
  reducedKeccak1568 (SubVector.lift (Vector.replicate 1568 bOne)) = 0x1d7add23b253ac47705200179f6ea5df39ba965ccda0a213c2afc112bc842a5 := by
  native_decide

def ReducedKeccak_1568_collision_resistance : Prop :=
  ∀{v₁ v₂ : SubVector F 1568 is_bit},
   reducedKeccak1568 v₁ = reducedKeccak1568 v₂ →
   v₁ = v₂

lemma ReducedKeccak_1568_collision_rw :
  ReducedKeccak_1568_collision_resistance →
  ∀{v₁ v₂ : Vector F 1568} {prop₁ : allIxes is_bit v₁} {prop₂ : allIxes is_bit v₂},
   (FromBinaryBigEndian_256_constant ↑(KeccakGadget_1568_64_24_1568_256_24_1088_1_constant' v₁ prop₁ RCBits).val).val.val =
   (FromBinaryBigEndian_256_constant ↑(KeccakGadget_1568_64_24_1568_256_24_1088_1_constant' v₂ prop₂ RCBits).val).val.val →
   v₁ = v₂ := by
  intro kr _ _ _ _ h
  simp [ReducedKeccak_1568_collision_resistance, reducedKeccak1568] at kr
  simp [KeccakGadget_1568_64_24_1568_256_24_1088_1_constant'] at h
  apply kr
  exact h
  all_goals assumption

theorem Insertion_InputHash_injective :
  ReducedKeccak_1568_collision_resistance →
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash StartIndex₁ PreRoot₁ PostRoot₁ IdComms₁ MerkleProofs₁ ∧
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash StartIndex₂ PreRoot₂ PostRoot₂ IdComms₂ MerkleProofs₂ →
  StartIndex₁ = StartIndex₂ ∧ PreRoot₁ = PreRoot₂ ∧ PostRoot₁ = PostRoot₂ ∧ IdComms₁ = IdComms₂ := by
  repeat rw [InsertionMbuCircuit_4_30_4_4_30_folded]
  unfold InsertionMbuCircuit_4_30_4_4_30_Fold
  intro kr ⟨h₁, h₂⟩
  have h₁ := constant_domain_rw ToReducedBigEndian_32_constant ToReducedBigEndian_32_domain h₁
  have h₂ := constant_domain_rw ToReducedBigEndian_32_constant ToReducedBigEndian_32_domain h₂
  repeat rw [(ToReducedBigEndian_256_constant _).equiv] at h₁ h₂
  rw [ (KeccakGadget_1568_64_24_1568_256_24_1088_1_constant' _ (by simp [ofFnGet_id, allIxes_append, Subtype.property]) _).equiv
     , (FromBinaryBigEndian_256_constant _).equiv
     ] at h₁ h₂
  rcases h₁ with ⟨h₁, _⟩
  rcases h₂ with ⟨h₂, _⟩
  have := Eq.trans (Eq.symm h₁) h₂
  have := ReducedKeccak_1568_collision_rw kr this
  have := Vector.append_inj this
  rcases this with ⟨this, d₃⟩
  have := Vector.append_inj this
  rcases this with ⟨this, d₂⟩
  have := Vector.append_inj this
  rcases this with ⟨this, d₁⟩
  have := Vector.append_inj this
  rcases this with ⟨this, d₀⟩
  have := Vector.append_inj this
  rcases this with ⟨this, hPostRoot⟩
  have := Vector.append_inj this
  rcases this with ⟨hStartIndex, hPreRoot⟩
  repeat rw [ofFnGet_id] at hPostRoot hPreRoot hStartIndex d₀ d₁ d₂ d₃
  have hPostRoot := ToReducedBigEndian_256_injective (Subtype.eq hPostRoot)
  have hPreRoot := ToReducedBigEndian_256_injective (Subtype.eq hPreRoot)
  have hStartIndex := ToReducedBigEndian_32_inj (Subtype.eq hStartIndex)
  have hStartIndex := congrArg Subtype.val hStartIndex
  refine ⟨hStartIndex, hPreRoot, hPostRoot, ?_⟩
  have d₀ := ToReducedBigEndian_256_injective (Subtype.eq d₀)
  have d₁ := ToReducedBigEndian_256_injective (Subtype.eq d₁)
  have d₂ := ToReducedBigEndian_256_injective (Subtype.eq d₂)
  have d₃ := ToReducedBigEndian_256_injective (Subtype.eq d₃)
  simp [GetElem.getElem] at d₀ d₁ d₂ d₃
  ext i
  fin_cases i <;> simpa
