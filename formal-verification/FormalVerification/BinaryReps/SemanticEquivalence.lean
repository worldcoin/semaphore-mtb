import FormalVerification
import FormalVerification.BinaryReps.Basic
import ProvenZk.Gates

open SemaphoreMTB (F Order)

variable [Fact (Nat.Prime Order)]

lemma and_iff (P Q R : Prop): (Q ↔ R) → (P ∧ Q ↔ P ∧ R) := by
  tauto

lemma ex_iff {P Q : α → Prop}: (∀x, P x ↔ Q x) → ((∃x, P x) ↔ ∃x, Q x) := by
  intro h;
  apply Iff.intro <;> {
    intro h1
    cases h1; rename_i witness prop
    exists witness
    try { rw [h witness]; assumption }
    try { rw [←h witness]; assumption }
  }

lemma and_t {P : Prop}: P ↔ (P ∧ True) := by
  tauto

set_option pp.rawOnError true

-- abbrev order_binary_le' : { v : Vector F 10 // allIxes is_bit v } := liftAllIxes vec![bOne,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero]
abbrev order_binary_le' : { v : Vector F 34 // allIxes is_bit v } := liftAllIxes vec![bOne,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bZero,bOne,bOne,bOne,bOne,bOne,bOne]


def ReducedModRCheck_256' (Input: Vector F 34) : Prop :=
    Gates.is_bool Input[33] ∧
    ∃gate_761, gate_761 = Gates.sub (1:F) Input[33] ∧
    ∃gate_762, Gates.or gate_761 0 gate_762 ∧
    ∃gate_763, Gates.select 0 (0:F) gate_762 gate_763 ∧
    Gates.is_bool Input[32] ∧
    ∃gate_765, gate_765 = Gates.sub (1:F) Input[32] ∧
    ∃gate_766, Gates.or gate_765 gate_763 gate_766 ∧
    ∃gate_767, Gates.select 0 (0:F) gate_766 gate_767 ∧
    Gates.is_bool Input[31] ∧
    ∃gate_769, gate_769 = Gates.sub (1:F) Input[31] ∧
    ∃gate_770, Gates.or gate_769 gate_767 gate_770 ∧
    ∃gate_771, Gates.select 0 (0:F) gate_770 gate_771 ∧
    Gates.is_bool Input[30] ∧
    ∃gate_773, gate_773 = Gates.sub (1:F) Input[30] ∧
    ∃gate_774, Gates.or gate_773 gate_771 gate_774 ∧
    ∃gate_775, Gates.select 0 (0:F) gate_774 gate_775 ∧
    Gates.is_bool Input[29] ∧
    ∃gate_777, gate_777 = Gates.sub (1:F) Input[29] ∧
    ∃gate_778, Gates.or gate_777 gate_775 gate_778 ∧
    ∃gate_779, Gates.select 0 (0:F) gate_778 gate_779 ∧
    Gates.is_bool Input[28] ∧
    ∃gate_781, gate_781 = Gates.sub (1:F) Input[28] ∧
    ∃gate_782, Gates.or gate_781 gate_779 gate_782 ∧
    ∃gate_783, Gates.select 0 (0:F) gate_782 gate_783 ∧
    Gates.is_bool Input[27] ∧
    ∃gate_785, Gates.or Input[27] 0 gate_785 ∧
    ∃gate_786, Gates.select gate_783 (0:F) gate_785 gate_786 ∧
    Gates.is_bool Input[26] ∧
    ∃gate_788, Gates.or Input[26] gate_786 gate_788 ∧
    ∃gate_789, Gates.select gate_783 (0:F) gate_788 gate_789 ∧
    Gates.is_bool Input[25] ∧
    ∃gate_791, Gates.or Input[25] gate_789 gate_791 ∧
    ∃gate_792, Gates.select gate_783 (0:F) gate_791 gate_792 ∧
    Gates.is_bool Input[24] ∧
    ∃gate_794, Gates.or Input[24] gate_792 gate_794 ∧
    ∃gate_795, Gates.select gate_783 (0:F) gate_794 gate_795 ∧
    Gates.is_bool Input[23] ∧
    ∃gate_797, Gates.or Input[23] gate_795 gate_797 ∧
    ∃gate_798, Gates.select gate_783 (0:F) gate_797 gate_798 ∧
    Gates.is_bool Input[22] ∧
    ∃gate_800, Gates.or Input[22] gate_798 gate_800 ∧
    ∃gate_801, Gates.select gate_783 (0:F) gate_800 gate_801 ∧
    Gates.is_bool Input[21] ∧
    ∃gate_803, Gates.or Input[21] gate_801 gate_803 ∧
    ∃gate_804, Gates.select gate_783 (0:F) gate_803 gate_804 ∧
    Gates.is_bool Input[20] ∧
    ∃gate_806, Gates.or Input[20] gate_804 gate_806 ∧
    ∃gate_807, Gates.select gate_783 (0:F) gate_806 gate_807 ∧
    Gates.is_bool Input[19] ∧
    ∃gate_809, Gates.or Input[19] gate_807 gate_809 ∧
    ∃gate_810, Gates.select gate_783 (0:F) gate_809 gate_810 ∧
    Gates.is_bool Input[18] ∧
    ∃gate_812, Gates.or Input[18] gate_810 gate_812 ∧
    ∃gate_813, Gates.select gate_783 (0:F) gate_812 gate_813 ∧
    Gates.is_bool Input[17] ∧
    ∃gate_815, Gates.or Input[17] gate_813 gate_815 ∧
    ∃gate_816, Gates.select gate_783 (0:F) gate_815 gate_816 ∧
    Gates.is_bool Input[16] ∧
    ∃gate_818, Gates.or Input[16] gate_816 gate_818 ∧
    ∃gate_819, Gates.select gate_783 (0:F) gate_818 gate_819 ∧
    Gates.is_bool Input[15] ∧
    ∃gate_821, Gates.or Input[15] gate_819 gate_821 ∧
    ∃gate_822, Gates.select gate_783 (0:F) gate_821 gate_822 ∧
    Gates.is_bool Input[14] ∧
    ∃gate_824, Gates.or Input[14] gate_822 gate_824 ∧
    ∃gate_825, Gates.select gate_783 (0:F) gate_824 gate_825 ∧
    Gates.is_bool Input[13] ∧
    ∃gate_827, Gates.or Input[13] gate_825 gate_827 ∧
    ∃gate_828, Gates.select gate_783 (0:F) gate_827 gate_828 ∧
    Gates.is_bool Input[12] ∧
    ∃gate_830, Gates.or Input[12] gate_828 gate_830 ∧
    ∃gate_831, Gates.select gate_783 (0:F) gate_830 gate_831 ∧
    Gates.is_bool Input[11] ∧
    ∃gate_833, Gates.or Input[11] gate_831 gate_833 ∧
    ∃gate_834, Gates.select gate_783 (0:F) gate_833 gate_834 ∧
    Gates.is_bool Input[10] ∧
    ∃gate_836, Gates.or Input[10] gate_834 gate_836 ∧
    ∃gate_837, Gates.select gate_783 (0:F) gate_836 gate_837 ∧
    Gates.is_bool Input[9] ∧
    ∃gate_839, Gates.or Input[9] gate_837 gate_839 ∧
    ∃gate_840, Gates.select gate_783 (0:F) gate_839 gate_840 ∧
    Gates.is_bool Input[8] ∧
    ∃gate_842, Gates.or Input[8] gate_840 gate_842 ∧
    ∃gate_843, Gates.select gate_783 (0:F) gate_842 gate_843 ∧
    Gates.is_bool Input[7] ∧
    ∃gate_845, Gates.or Input[7] gate_843 gate_845 ∧
    ∃gate_846, Gates.select gate_783 (0:F) gate_845 gate_846 ∧
    Gates.is_bool Input[6] ∧
    ∃gate_848, Gates.or Input[6] gate_846 gate_848 ∧
    ∃gate_849, Gates.select gate_783 (0:F) gate_848 gate_849 ∧
    Gates.is_bool Input[5] ∧
    ∃gate_851, Gates.or Input[5] gate_849 gate_851 ∧
    ∃gate_852, Gates.select gate_783 (0:F) gate_851 gate_852 ∧
    Gates.is_bool Input[4] ∧
    ∃gate_854, Gates.or Input[4] gate_852 gate_854 ∧
    ∃gate_855, Gates.select gate_783 (0:F) gate_854 gate_855 ∧
    Gates.is_bool Input[3] ∧
    ∃gate_857, Gates.or Input[3] gate_855 gate_857 ∧
    ∃gate_858, Gates.select gate_783 (0:F) gate_857 gate_858 ∧
    Gates.is_bool Input[2] ∧
    ∃gate_860, Gates.or Input[2] gate_858 gate_860 ∧
    ∃gate_861, Gates.select gate_783 (0:F) gate_860 gate_861 ∧
    Gates.is_bool Input[1] ∧
    ∃gate_863, Gates.or Input[1] gate_861 gate_863 ∧
    ∃gate_864, Gates.select gate_783 (0:F) gate_863 gate_864 ∧
    Gates.is_bool Input[0] ∧
    ∃gate_866, gate_866 = Gates.sub (1:F) Input[0] ∧
    ∃gate_867, Gates.or gate_866 gate_783 gate_867 ∧
    ∃gate_868, Gates.select gate_864 (0:F) gate_867 gate_868 ∧
    Gates.eq gate_868 (1:F) ∧
    True

theorem allIxes_indexed' {v : {v : Vector α n // allIxes prop v}} {i : Nat} {i_small : i < n}:
  prop (v.val[i]'i_small) ↔ True := by simp; exact v.prop ⟨i, i_small⟩

lemma lemma1 {v : {v : Vector F n // allIxes is_bit v}} {i : Nat} {i_small : i < n}:
  (P ↔ Q) → (P ↔ Gates.is_bool (v.val[i]'i_small) ∧ Q) := by
  rw [is_bool_is_bit, allIxes_indexed' (prop := is_bit), true_and]
  exact id

theorem ReducedModRCheck_256_Fold :
  ∀ (v : {v : Vector F 256 // allIxes is_bit v}), binary_comparison_with_constant order_binary_le v ⟨255, by decide⟩  0 0 ↔ SemaphoreMTB.ReducedModRCheck_256 v := by
  intro v
  unfold SemaphoreMTB.ReducedModRCheck_256

  -- rw [is_bool_is_bit, allIxes_indexed' (prop := is_bit), true_and]
  repeat (
    apply lemma1
    repeat (apply ex_iff; intro _; apply and_iff)
  )

  tauto
