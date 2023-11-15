import FormalVerification
import FormalVerification.BinaryReps.Basic
import FormalVerification.BinaryReps.SemanticEquivalence
import FormalVerification.Keccak.SemanticEquivalence
import ProvenZk.Gates
import ProvenZk.Ext.Vector

open SemaphoreMTB (F Order)

axiom ord_prime : Nat.Prime Order
instance : Fact (Nat.Prime Order) := ⟨ord_prime⟩

def RC : Vector (Fin (2 ^ 64)) 24 := vec![0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A, 0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A, 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

def RCBits : SubVector (Vector F 64) 24 (Vector.allIxes is_bit):=
  SubVector.lift (Vector.map (fun x => SubVector.lift (Vector.map embedBit (fin_to_bits_le x))) RC)

def DeletionMbuCircuit_4_4_30_4_4_30_Fold (InputHash: F) (DeletionIndices: Vector F 4) (PreRoot: F) (PostRoot: F) (IdComms: Vector F 4) (MerkleProofs: Vector (Vector F 30) 4): Prop :=
    SemaphoreMTB.ToReducedBigEndian_32 DeletionIndices[0] fun gate_0 =>
    SemaphoreMTB.ToReducedBigEndian_32 DeletionIndices[1] fun gate_1 =>
    SemaphoreMTB.ToReducedBigEndian_32 DeletionIndices[2] fun gate_2 =>
    SemaphoreMTB.ToReducedBigEndian_32 DeletionIndices[3] fun gate_3 =>
    SemaphoreMTB.ToReducedBigEndian_256 PreRoot fun gate_4 =>
    SemaphoreMTB.ToReducedBigEndian_256 PostRoot fun gate_5 =>
    SemaphoreMTB.KeccakGadget_640_64_24_640_256_24_1088_1
      (Vector.ofFnGet gate_0 ++ Vector.ofFnGet gate_1 ++ Vector.ofFnGet gate_2 ++ Vector.ofFnGet gate_3 ++ Vector.ofFnGet gate_4 ++ Vector.ofFnGet gate_5) RCBits.val fun gate_6 =>
    SemaphoreMTB.FromBinaryBigEndian_256 gate_6 fun gate_7 =>
    Gates.eq InputHash gate_7 ∧
    SemaphoreMTB.DeletionProof_4_4_30_4_4_30 DeletionIndices PreRoot IdComms MerkleProofs fun gate_9 =>
    Gates.eq gate_9 PostRoot ∧
    True

theorem DeletionCircuit_folded {InputHash PreRoot PostRoot : F} {DeletionIndices IdComms : Vector F 4} {MerkleProofs: Vector (Vector F 30) 4}:
  SemaphoreMTB.DeletionMbuCircuit_4_4_30_4_4_30 InputHash DeletionIndices PreRoot PostRoot IdComms MerkleProofs =
  DeletionMbuCircuit_4_4_30_4_4_30_Fold InputHash DeletionIndices PreRoot PostRoot IdComms MerkleProofs := by rfl

def KeccakGadget_640_64_24_640_256_24_1088_1_constant'
  (input : Vector F 640)
  (prop_input : Vector.allIxes is_bit input)
  ( rc : { v : Vector (Vector F 64) 24 // Vector.allIxes (Vector.allIxes is_bit) v } ):
  ConstantOf (SemaphoreMTB.KeccakGadget_640_64_24_640_256_24_1088_1 input rc.val) (Vector.allIxes is_bit) :=
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
     , (KeccakGadget_640_64_24_640_256_24_1088_1_constant' _ (by simp [Vector.ofFnGet_id, Vector.allIxes_append, Subtype.property]) _).equiv
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
  ∀{v₁ v₂ : Vector F 640} {prop₁ : Vector.allIxes is_bit v₁} {prop₂ : Vector.allIxes is_bit v₂},
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
  simp only [Vector.ofFnGet_id] at h₁ h₂
  rw [ (ToReducedBigEndian_256_constant _).equiv
     , (ToReducedBigEndian_256_constant _).equiv
     , (KeccakGadget_640_64_24_640_256_24_1088_1_constant' _ (by simp [Vector.ofFnGet_id, Vector.allIxes_append, Subtype.property]) _).equiv
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
        (Vector.ofFnGet gate_0 ++ Vector.ofFnGet gate_1 ++ Vector.ofFnGet gate_2 ++ Vector.ofFnGet gate_3 ++ Vector.ofFnGet gate_4 ++ Vector.ofFnGet gate_5 ++ Vector.ofFnGet gate_6) RCBits.val fun gate_7 =>
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
  (prop_input : Vector.allIxes is_bit input)
  ( rc : { v : Vector (Vector F 64) 24 // Vector.allIxes (Vector.allIxes is_bit) v } ):
  ConstantOf (SemaphoreMTB.KeccakGadget_1568_64_24_1568_256_24_1088_1 input rc.val) (Vector.allIxes is_bit) :=
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
  rw [ (KeccakGadget_1568_64_24_1568_256_24_1088_1_constant' _ (by simp [Vector.ofFnGet_id, Vector.allIxes_append, Subtype.property]) _).equiv
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
  ∀{v₁ v₂ : Vector F 1568} {prop₁ : Vector.allIxes is_bit v₁} {prop₂ : Vector.allIxes is_bit v₂},
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
  rw [ (KeccakGadget_1568_64_24_1568_256_24_1088_1_constant' _ (by simp [Vector.ofFnGet_id, Vector.allIxes_append, Subtype.property]) _).equiv
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
