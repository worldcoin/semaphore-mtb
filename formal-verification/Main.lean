import ProvenZk
import FormalVerification
import FormalVerification.Insertion
import FormalVerification.Deletion
import FormalVerification.Common
import FormalVerification.Poseidon
import FormalVerification.InputHashing
import FormalVerification.ReducednessCheck
import FormalVerification.BinaryDecompositions

open SemaphoreMTB (F Order)

namespace Deletion

theorem root_transformation_correct
    [Fact (CollisionResistant poseidon₂)]
    {tree : MerkleTree F poseidon₂ D}:
    SemaphoreMTB.DeletionMbuCircuit_4_4_30_4_4_30 inputHash deletionIndices tree.root postRoot identities merkleProofs →
    ∃(postTree : MerkleTree F poseidon₂ D),
    postTree.root = postRoot ∧
    (∀ i ∈ deletionIndices, postTree[i.val]! = 0) ∧
    (∀ i, i ∉ deletionIndices → postTree[i.val]! = tree[i.val]!)
  := by
  intro hp
  replace hp := Deletion_skipHashing hp
  rw [deletionProofCircuit_eq_deletionRoundsSemantics] at hp
  replace hp := deletionRounds_rootTransformation hp
  rcases hp with ⟨postTree, treeTrans, rootTrans⟩
  exists postTree
  refine ⟨rootTrans, ?inrange, ?outrange⟩
  . intro i hi
    apply treeTranform_get_present treeTrans hi
  . intro i hi
    simp [getElem!_eq_getElem?_get!]
    apply congrArg
    apply treeTransform_get_absent treeTrans hi

theorem assignment_exists
  [Fact (CollisionResistant poseidon₂)]
  {tree : MerkleTree F poseidon₂ D}:
    (∀i ∈ indices, i.val < 2^(D+1)) →
    ∃inputHash identities proofs postRoot, SemaphoreMTB.DeletionMbuCircuit_4_4_30_4_4_30 inputHash indices tree.root postRoot identities proofs
  := by
  intro h;
  simp only [DeletionCircuit_folded, DeletionMbuCircuit_4_4_30_4_4_30_Fold]
  simp only [
    Vector.ofFnGet_id,
    ToReducedBigEndian_32_uncps,
    ToReducedBigEndian_256_uncps,
    RCBitsField_def,
    ←Vector.map_permute,
    Vector.map_hAppend,
    (KeccakGadget_640_64_24_640_256_24_1088_1_uniqueAssignment _ _).equiv,
    FromBinaryBigEndian_256_uncps,
    Gates.eq,
    deletionProofCircuit_eq_deletionRoundsSemantics
  ]
  have := exists_assignment (tree := tree) h
  rcases this with ⟨_, _, _, hp⟩
  repeat apply Exists.intro
  apply And.intro (Eq.refl _)
  simp
  apply hp
  simp only [D] at h
  all_goals {
    apply Nat.lt_trans _ ((by decide) : 2 ^ 31 < 2 ^ 32)
    apply h
    simp [getElem]
  }

/--
Establishes that the deletion circuit's InputHash parameter is uniquely
determined by DeletionIndices, PreRoot and PostRoot. That is done by showing
that any two valid assigments that agree on those parameters, must also agree
on InputHash.
-/
theorem inputHash_deterministic:
  (SemaphoreMTB.DeletionMbuCircuit_4_4_30_4_4_30 InputHash₁ DeletionIndices PreRoot PostRoot IdComms₁ MerkleProofs₁ ∧
   SemaphoreMTB.DeletionMbuCircuit_4_4_30_4_4_30 InputHash₂ DeletionIndices PreRoot PostRoot IdComms₂ MerkleProofs₂)
  → InputHash₁ = InputHash₂
  := Deletion_InputHash_deterministic

def testString80 : String :=
  "This string is exactly 80 bytes long, which is unbelievably lucky for this test."

def testVector640 : Vector Bool 640 :=
  Subtype.mk (testString80.toUTF8.toList.map (fun b => Vector.toList $ Fin.toBitsLE (d := 8) b.val)).join (by native_decide)

/--
The reference number is obtained by hashing the test string using the following Solidity code:
```solidity
string memory data = "This string is exactly 80 bytes long, which is unbelievably lucky for this test.";
uint256 result;
assembly {
  result := mod(keccak256(add(data, 0x20), mload(data)), 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001)
}
```
-/
theorem reducedKeccak640_test :
  reducedKeccak640 testVector640 = 0x799e635101207dc20689c342be25dc6f5a2f25b51d2a5ac3c9fee51694b3609 := by native_decide

axiom reducedKeccak640_collision_resistant :
  ∀x y, reducedKeccak640 x = reducedKeccak640 y → x = y

theorem inputHash_injective:
  SemaphoreMTB.DeletionMbuCircuit_4_4_30_4_4_30 InputHash DeletionIndices₁ PreRoot₁ PostRoot₁ IdComms₁ MerkleProofs₁ ∧
  SemaphoreMTB.DeletionMbuCircuit_4_4_30_4_4_30 InputHash DeletionIndices₂ PreRoot₂ PostRoot₂ IdComms₂ MerkleProofs₂ →
  DeletionIndices₁ = DeletionIndices₂ ∧ PreRoot₁ = PreRoot₂ ∧ PostRoot₁ = PostRoot₂  :=
  Deletion_InputHash_injective reducedKeccak640_collision_resistant

end Deletion

namespace Insertion

theorem before_insertion_all_items_zero
  [Fact (CollisionResistant poseidon₂)]
  {tree: MerkleTree F poseidon₂ D}
  {startIndex : F}:
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash startIndex tree.root PostRoot IdComms MerkleProofs →
  ∀ i ∈ [startIndex.val:startIndex.val + B], tree[i]! = 0 := by
  intro hp i hir
  have hp := Insertion_skipHashing hp
  rw [Insertion.insertionRoundsCircuit_eq_insertionRoundsSemantics] at hp
  have hp'' := ix_bound hp
  rw [getElem!_eq_getElem?_get!]
  rw [before_insertion_all_zero hp]; rfl
  apply And.intro
  . exact hir.1
  . apply Nat.lt_of_lt_of_eq hir.2
    rw [ZMod.val_add, Nat.mod_eq_of_lt]
    rfl
    calc
      startIndex.val + 4 = (startIndex.val + 3) + 1 := by ring
      _ < 2^D + 1 := Nat.add_lt_add_right hp'' (k := 1)
      _ < Order := by decide

theorem root_transformation_correct
    [Fact (CollisionResistant poseidon₂)]
    {Tree : MerkleTree F poseidon₂ D}:
    SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash StartIndex Tree.root PostRoot IdComms MerkleProofs →
    ∃(postTree : MerkleTree F poseidon₂ D),
    postTree.root = PostRoot ∧
    (∀ i, i ∈ [StartIndex.val:StartIndex.val + B] → postTree[i]! = IdComms[i-StartIndex.val]!) ∧
    (∀ i, i ∉ [StartIndex.val:StartIndex.val + B] → postTree[i]! = Tree[i]!)
  := by
  intro hp
  have hp := Insertion_skipHashing hp
  rw [insertionRoundsCircuit_eq_insertionRoundsSemantics] at hp
  have hp := insertionRoundsRootTransformation hp
  rcases hp with ⟨postTree, treeTrans, rootTrans⟩
  exists postTree
  simp_rw [getElem!_eq_getElem?_get!]
  refine ⟨rootTrans, ?inrange, ?outrange⟩
  case inrange =>
    intro i hi
    have : i = StartIndex.val + (i - StartIndex.val) := by
      rw [add_comm, Nat.sub_add_cancel hi.1]
    have i_off_inrange : i - StartIndex.val ∈ [0:B] := by
      refine ⟨Nat.zero_le _, ?_⟩
      cases hi
      linarith
    rw [this, treeTransform_get_inrange treeTrans i_off_inrange, ←this]
    apply congrArg
    apply eq_comm.mp
    apply getElem?_eq_some_getElem_of_valid_index
  case outrange =>
    intro i hi
    cases Nat.lt_or_ge i StartIndex.val with
    | inl h =>
      apply congrArg
      apply eq_comm.mp
      apply treeTransform_get_lt treeTrans h
    | inr h =>
      cases Nat.lt_or_ge i (StartIndex.val + B) with
      | inl h' =>
        exfalso
        exact hi ⟨h, h'⟩
      | inr h =>
        apply congrArg
        apply eq_comm.mp
        apply treeTransform_get_gt treeTrans h

theorem assignment_exists [Fact (CollisionResistant poseidon₂)] {tree : MerkleTree F poseidon₂ D}:
    startIndex + B < 2 ^ D ∧
    (∀i, (h: i ∈ [startIndex : startIndex + B]) → tree[i]! = 0) →
    ∃proofs postRoot inputHash, SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 inputHash startIndex tree.root postRoot idComms proofs
  := by
  rintro ⟨ix_ok, items_zero⟩
  simp only [InsertionMbuCircuit_4_30_4_4_30_folded]
  unfold InsertionMbuCircuit_4_30_4_4_30_Fold
  simp only [
    Vector.ofFnGet_id,
    ToReducedBigEndian_32_uncps,
    ToReducedBigEndian_256_uncps,
    RCBitsField_def,
    ←Vector.map_permute,
    Vector.map_hAppend,
    (KeccakGadget_1568_64_24_1568_256_24_1088_1_uniqueAssignment _ _).equiv,
    FromBinaryBigEndian_256_uncps,
    Gates.eq
  ]
  simp [insertionRoundsCircuit_eq_insertionRoundsSemantics]
  have := exists_assignment (identities := idComms) ix_ok (by
    intro i h
    apply getElem_of_getElem!
    apply items_zero
    assumption
  )
  rcases this with ⟨proofs, postRoot, h⟩
  exists proofs, postRoot
  apply And.intro
  . apply Exists.intro
    apply Exists.intro
    . rfl
    . simp only [D, B] at ix_ok
      rw [ZMod.val_cast_of_lt]
      . linarith
      . simp only [Order]; linarith
  . exact h

/--
Establishes that the insertion circuit's InputHash parameter is uniquely
determined by StartIndex, PreRoot, PostRoot and the identity commitments. That
is done by showing that any two valid assigments that agree on those
parameters, must also agree on InputHash.
-/
theorem inputHash_deterministic:
    SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash₁ StartIndex PreRoot PostRoot IdComms MerkleProofs₁ ∧
    SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash₂ StartIndex PreRoot PostRoot IdComms MerkleProofs₂ →
    InputHash₁ = InputHash₂
  := Insertion_InputHash_deterministic

def testString196 : String :=
  "This is string is exactly 196 bytes long, which happens to be exactly the length we need to test the 1568-bit keccak hash implementation, that can be found in the SemaphoreMTB Insertion Circuit..."
def testVector1568 : Vector Bool 1568 :=
  Subtype.mk (testString196.toUTF8.toList.map (fun b => Vector.toList $ Fin.toBitsLE (d := 8) b.val)).join (by native_decide)

/--
The reference number is obtained by hashing the test string using the following Solidity code:
```solidity
string memory data = "This is string is exactly 196 bytes long, which happens to be exactly the length we need to test the 1568-bit keccak hash implementation, that can be found in the SemaphoreMTB Insertion Circuit...";
uint256 result;
assembly {
  result := mod(keccak256(add(data, 0x20), mload(data)), 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001)
}
```
-/
theorem reducedKeccak1568_test :
  reducedKeccak1568 testVector1568 = 0x204e42742e70b563e147bca3aac705534bfae2e7d17691127dd6425b23f5ba43 := by native_decide

axiom reducedKeccak1568_collision_resistant :
  ∀x y, reducedKeccak1568 x = reducedKeccak1568 y → x = y

theorem inputHash_injective:
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash StartIndex₁ PreRoot₁ PostRoot₁ IdComms₁ MerkleProofs₁ ∧
  SemaphoreMTB.InsertionMbuCircuit_4_30_4_4_30 InputHash StartIndex₂ PreRoot₂ PostRoot₂ IdComms₂ MerkleProofs₂ →
  StartIndex₁ = StartIndex₂ ∧ PreRoot₁ = PreRoot₂ ∧ PostRoot₁ = PostRoot₂ ∧ IdComms₁ = IdComms₂ :=
  Insertion_InputHash_injective reducedKeccak1568_collision_resistant

end Insertion

def main (_ : List String): IO UInt32 := pure 0
