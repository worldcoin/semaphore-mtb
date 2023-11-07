import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Ext.Vector

def is_index_in_range {n : Nat} (D : Nat) (a : ZMod n) : Prop :=
  a.val < 2^D

def is_index_in_range_nat (D : Nat) (a : Nat) : Prop :=
  a < 2^D

lemma is_index_in_range_nat_sum {n : Nat} (D : Nat) (a b : Nat) (h : 2^D < n): is_index_in_range_nat D (a + b) → is_index_in_range D (a:ZMod n) := by
  intro xs_small
  rw [is_index_in_range_nat] at xs_small
  rw [is_index_in_range]
  rw [ZMod.val_cast_of_lt]
  . linarith
  . linarith

def are_indices_in_range {d n : Nat} (D : Nat) (a : Vector (ZMod n) d) : Prop :=
  List.foldr (fun x r => (is_index_in_range D x) ∧ r) True a.toList

theorem are_indices_in_range_cons {d n : Nat} (D : Nat) (a : ZMod n) (vec : Vector (ZMod n) d) :
  are_indices_in_range D (a ::ᵥ vec) ↔ is_index_in_range D a ∧ are_indices_in_range D vec := by
  unfold are_indices_in_range
  conv => lhs; unfold List.foldr; simp

theorem are_indices_in_range_split {d n : Nat} (D : Nat) (a : Vector (ZMod n) (d+1)) :
  are_indices_in_range D a ↔ is_index_in_range D a.head ∧ are_indices_in_range D a.tail := by
  rw [<-are_indices_in_range_cons]
  simp

lemma head_index_in_range {b : Nat} (D : Nat) (Index : Vector (ZMod n) (b+1)) (xs_small : are_indices_in_range D Index) :
  is_index_in_range D (Vector.head Index) := by
  rw [are_indices_in_range_split] at xs_small
  cases xs_small
  rename_i x xs
  simp [x]

lemma tail_index_in_range {b : Nat} (D : Nat) (Index : Vector (ZMod n) (b+1)) (xs_small : are_indices_in_range D Index) :
  are_indices_in_range D (Vector.tail Index) := by
  rw [are_indices_in_range_split] at xs_small
  cases xs_small
  rename_i x xs
  simp [xs]