import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle

import FormalVerification
import FormalVerification.Poseidon.Spec
import FormalVerification.Poseidon.Correctness
import FormalVerification.SemanticEquivalence

open SemaphoreMTB (F Order)

variable [Fact (Nat.Prime Order)]

open SemaphoreMTB renaming VerifyProof_4_3 → gVerifyProof
open SemaphoreMTB renaming DeletionRound_3_3 → gDeletionRound
open SemaphoreMTB renaming DeletionProof_2_2_3_2_2_3 → gDeletionProof
open SemaphoreMTB renaming InsertionRound_3_3 → gInsertionRound
open SemaphoreMTB renaming InsertionProof_2_3_2_2_3 → gInsertionProof

-- theorem before_deletion_tree_matches_root (DeletionIndices: Vector F B) (PreRoot: F) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (k: F -> Prop) :
--   gDeletionProof DeletionIndices PreRoot IdComms MerkleProofs k →
--   ∃out, recover_binary_zmod' out = DeletionIndices.head ∧ is_vector_binary out ∧
--   MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) MerkleProofs.head IdComms.head = PreRoot := by
--   simp [DeletionProof_looped, deletion_rounds_uncps, DeletionLoop]
--   intros
--   apply Exists.intro
--   tauto

-- theorem after_deletion_items_are_zero (DeletionIndices: Vector F B) (PreRoot: F) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) :
--   gDeletionProof DeletionIndices PreRoot IdComms MerkleProofs fun post_root => ∃x, recover_binary_zmod' x = DeletionIndices.last ∧ is_vector_binary x ∧
--   MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec x) MerkleProofs.last 0 = post_root := by
--   -- simp [DeletionProof_2_2_3_2_uncps]
--   -- simp [DeletionLoop]

--   -- simp [SemaphoreMTB.DeletionProof_2_2_3_2]
--   -- simp [DeletionRound_uncps]

--   sorry


def list_to_vec_n (L : List Dir) (n : Nat) : Vector Dir n := ⟨List.takeI n L, List.takeI_length n L⟩

@[simp]
theorem list_to_vec_cons_succ : list_to_vec_n (x :: xs) (Nat.succ n) = x ::ᵥ list_to_vec_n xs n := by
  rfl

@[simp]
theorem list_to_vec_nil: list_to_vec_n [] n = Vector.replicate n Dir.left := by
  apply Vector.eq
  simp [list_to_vec_n, Vector.replicate, default]

@[simp]
theorem vector_replicate_succ : Vector.replicate (Nat.succ n) a = a ::ᵥ Vector.replicate n a := by
  rfl

theorem vector_replicate_succ_snoc : Vector.replicate (Nat.succ n) a = (Vector.replicate n a).snoc a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    conv => rhs; simp [←ih]


@[simp]
theorem vector_replicate_reverse : Vector.reverse (Vector.replicate n a) = Vector.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [ih, ←vector_replicate_succ_snoc]

@[simp]
theorem vector_map_replicate : Vector.map f (Vector.replicate n a) = Vector.replicate n (f a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [ih]

def mod_two (inp : Nat) : Dir := match h:inp%2 with
 | 0 => Dir.left
 | 1 => Dir.right
 | x + 2 => False.elim (by
   have := Nat.mod_lt inp (y := 2)
   rw [h] at this
   simp at this
   contradiction
 )

def nat_to_list_le : Nat → List Dir
  | 0 => [Dir.left]
  | 1 => [Dir.right]
  | x+2 => mod_two x :: nat_to_list_le ((x + 2) / 2)
termination_by nat_to_list_le x => x
decreasing_by simp_wf; simp_arith; apply Nat.div_le_self

def nat_to_list_be (d: Nat) (ix: Nat): Vector Dir d := match d with
| 0 => Vector.nil
| Nat.succ d' => if ix ≥ 2^d'
  then Dir.right ::ᵥ nat_to_list_be d' (ix - 2^d')
  else Dir.left ::ᵥ nat_to_list_be d' ix

def dir_to_bit : Dir → Bit
  | Dir.left => Bit.zero
  | Dir.right => Bit.one

def bit_to_dir : Bit → Dir
  | Bit.zero => Dir.left
  | Bit.one => Dir.right

def nat_to_dir_vec (idx : Nat) (depth : Nat ): Vector Dir depth :=
  Vector.reverse $ list_to_vec_n (nat_to_list_le idx) depth

lemma reverse_map_reverse_is_map {n : Nat} {x : Vector α n} {f : α → β} : Vector.reverse (Vector.map f (Vector.reverse x)) = Vector.map f x := by
  apply Vector.eq
  simp [Vector.toList_reverse, List.map_reverse]

def bool_to_bit : Bool -> Bit := fun x => match x with
  | false => Bit.zero
  | true => Bit.one

def bit_to_bool : Bit -> Bool := fun x => match x with
  | Bit.zero => false
  | Bit.one => true

def bool_to_dir : Bool -> Dir := fun x => match x with
  | false => Dir.left
  | true => Dir.right

def dir_to_bool : Dir -> Bool := fun x => match x with
  | Dir.left => false
  | Dir.right => true

def dirvec_to_bitvec {n : Nat} (x : Vector Dir n) : Bitvec n :=
  Vector.map dir_to_bool x

def bitvec_to_dirvec {n : Nat} (x : Bitvec n) : Vector Dir n :=
  Vector.map bool_to_dir x

@[simp]
theorem recover_binary_nat_zero {n : Nat} : recover_binary_nat (Vector.replicate n Bit.zero) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [recover_binary_nat, ih]


-- #eval Bitvec.ofNat 3 11
-- #eval (list_to_vec_n (nat_to_list_le 11) 3).reverse

theorem nat_to_dir_vec_recover {ix d: ℕ} : ix < 2^d → recover_binary_nat (Vector.map dir_to_bit (nat_to_dir_vec ix d)).reverse = ix := by
  induction' d with d ih generalizing ix
  · intro h; simp_arith at h; cases h; rfl
  · intro range
    unfold nat_to_dir_vec at *
    cases ix with
    | zero =>
      simp [nat_to_list_le, dir_to_bit, recover_binary_nat, recover_binary_nat_zero (n:=d)]
    | succ ix =>
      cases ix with
      | zero =>
        simp [nat_to_list_le, dir_to_bit, recover_binary_nat, recover_binary_nat_zero (n:=d)]
      | succ ix =>
        simp [nat_to_list_le, recover_binary_nat, mod_two]
        rw [ih]
        . split
          . simp [Bit.toNat, dir_to_bit]
            rw [←Nat.mod_add_div ix.succ.succ 2]
            simp_arith
            assumption
          . simp [Bit.toNat, dir_to_bit]
            rw [←Nat.mod_add_div ix.succ.succ 2]
            simp_arith
            apply Eq.symm
            assumption
          . contradiction
        . rw [Nat.pow_succ, ← Nat.div_lt_iff_lt_mul] at range
          have : Nat.succ (ix/2) = ix.succ.succ / 2 := by simp_arith
          rw [this]
          assumption
          simp

def item_at_nat {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (idx : Nat) : F :=
  let p := nat_to_dir_vec idx depth
  t.item_at p

def set_at_nat(t : MerkleTree F H depth) (idx: Nat) (newVal: F): MerkleTree F H depth :=
  t.set (nat_to_dir_vec idx depth) newVal

-- IdComms not needed because proving that all items are 0 after deletion
-- def item_is_zero_or_skip {n} (Tree: MerkleTree F poseidon₂ D) (DeletionIndices: Vector F n) (PostRoot: F) (MerkleProofs: Vector (Vector F D) n) : Prop :=
--   match n with
--   | Nat.zero => True
--   | Nat.succ _ =>
--     ∃out: Vector F (D+1), recover_binary_zmod' out = DeletionIndices.head ∧ is_vector_binary out ∧
--     match zmod_to_bit out.last with
--       | Bit.zero => Tree.item_at (Dir.create_dir_vec out).front = 0 ∧ item_is_zero_or_skip Tree DeletionIndices.tail PostRoot MerkleProofs.tail -- Update the root
--       | Bit.one => item_is_zero_or_skip Tree DeletionIndices.tail PostRoot MerkleProofs.tail  -- Skip flag set, don't update the root

-- IdComms not needed because proving that all items are 0 before insertion
-- theorem after_deletion_all_items_zero (Tree: MerkleTree F poseidon₂ D) (DeletionIndices: Vector F B) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (k: F -> Prop) :
--   gDeletionProof DeletionIndices Tree.root IdComms MerkleProofs fun PostRoot => Tree.root = PostRoot ∧ item_is_zero_or_skip Tree DeletionIndices PostRoot MerkleProofs := by
--     simp [DeletionProof_uncps]
--     unfold DeletionLoop
--     unfold item_is_zero_or_skip
--     --apply Exists.intro

--     sorry

def InsertionLoopTree {n} (Tree: MerkleTree F poseidon₂ D) (StartIndex: F) (PreRoot: F) (IdComms: Vector F n) (MerkleProofs: Vector (Vector F D) n) : Prop :=
  match n with
  | Nat.zero => PreRoot = Tree.root
  | Nat.succ _ =>
    ∃out: Vector F D, recover_binary_zmod' out = StartIndex ∧ is_vector_binary out ∧
    MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) MerkleProofs.head 0 = Tree.root ∧
    InsertionLoopTree Tree (StartIndex + 1) (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) MerkleProofs.head IdComms.head) IdComms.tail MerkleProofs.tail

def item_is_zero {n} (Tree: MerkleTree F poseidon₂ D) (StartIndex: F) (PreRoot: F) (MerkleProofs: Vector (Vector F D) n) : Prop :=
  match n with
  | Nat.zero => True
  | Nat.succ _ =>
    ∃out: Vector F D, recover_binary_zmod' out = StartIndex ∧ is_vector_binary out ∧
    Tree.item_at (Dir.create_dir_vec out).reverse = 0 ∧ item_is_zero Tree (StartIndex + 1) PreRoot MerkleProofs.tail

theorem recover_tail_reverse_equals_recover'
  {F depth}
  (H : Hash F 2)
  (ix : Vector Dir depth)
  (proof : Vector F depth)
  (item : F) :
  MerkleTree.recover_tail H ix proof item = MerkleTree.recover H ix.reverse proof.reverse item := by
  rw [←Vector.ofFn_get (v := ix)]
  rw [←Vector.ofFn_get (v := proof)]
  rw [<-MerkleTree.recover_tail_reverse_equals_recover H _ _ item]
  simp

def TreeInsert [Fact (perfect_hash poseidon₂)] (Tree : MerkleTree F poseidon₂ D) (Index: F) (Item: F) (Proof: Vector F D) (k: F -> Prop) : Prop :=
  ∃out: Vector F D, recover_binary_zmod' out = Index ∧ is_vector_binary out ∧
  MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) Proof 0 = Tree.root ∧
  k (Tree.set (Dir.create_dir_vec out).reverse Item).root
-- inst✝¹: Fact (Nat.Prime Order)
-- inst✝: Fact (perfect_hash poseidon₂)
-- Tree: MerkleTree F poseidon₂ D
-- IndexItem: F
-- Proof: Vector F D
-- k: F → Prop
-- w✝: Vector F D
-- left✝²: recover_binary_zmod' w✝ = Index
-- left✝¹: is_vector_binary w✝
-- left✝: MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec w✝) Proof 0 = MerkleTree.root Tree
-- right✝: k (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec w✝) Proof Item)
-- ⊢ MerkleTree.recover poseidon₂ (nat_to_dir_vec (ZMod.val Index) D) ?mp.intro.intro.intro.intro.left.proof 0 =
--   MerkleTree.root Tree


-- theorem nat_to_dir_vec_recover {ix d: ℕ} : ix < 2^d →
-- recover_binary_nat (Vector.map dir_to_bit (nat_to_dir_vec ix d)).reverse = ix := by

@[simp]
theorem vector_zmod_to_bit_cons : vector_zmod_to_bit (x ::ᵥ xs) = (nat_to_bit x.val) ::ᵥ vector_zmod_to_bit xs := by
  rfl

-- theorem create_dir_vec_nat_to_dir : Vector.reverse (nat_to_dir_vec (recover_binary_nat (vector_zmod_to_bit w)) D) = Dir.create_dir_vec w := by

theorem recover_binary_zmod_bit {w : Vector F n}: is_vector_binary w → recover_binary_zmod' w = recover_binary_zmod (vector_zmod_to_bit w) := by
  intro h
  induction w using Vector.inductionOn with
  | h_nil => rfl
  | h_cons ih =>
    simp [recover_binary_zmod', recover_binary_zmod]
    rw [is_vector_binary_cons] at h
    cases h
    rw [ih]
    rotate_left
    . assumption
    rename (is_bit _) => isb
    cases isb <;> {
      subst_vars
      rfl
    }

theorem dir_bit_dir : Dir.nat_to_dir x = bit_to_dir (nat_to_bit x) := by
  cases x
  . rfl
  . rename_i x; cases x <;> rfl

theorem create_dir_vec_bit : Dir.create_dir_vec w = Vector.map bit_to_dir (vector_zmod_to_bit w) := by
  induction w using Vector.inductionOn with
  | h_nil => rfl
  | h_cons ih =>
    simp [ih]
    congr
    rw [dir_bit_dir]

theorem bit_to_dir_to_bit : bit_to_dir (dir_to_bit x) = x := by cases x <;> rfl

theorem vector_reverse_eq {x y : Vector α n} : (x.reverse = y) ↔ (x = y.reverse) := by
  apply Iff.intro
  case mp => {
    intro
    subst_vars
    simp
  }
  case mpr => {
    intro
    subst_vars
    simp
  }

theorem nat_to_dir_vec_correct {Index : F}:
  is_vector_binary w →
  recover_binary_zmod' w = Index →
  (nat_to_dir_vec (Index.val) D).reverse = Dir.create_dir_vec w := by
  intro bin recover_bin
  rw [recover_binary_zmod_bit bin] at recover_bin
  have : (2^D < Order) := by simp
  have recover_w : recover_binary_nat (vector_zmod_to_bit w) = Index.val := by
    rw [←binary_zmod_same_as_nat]
    congr
    assumption
  have index_small : Index.val < 2 ^ D := by
    rw [←recover_w]
    apply binary_nat_lt
  have := nat_to_dir_vec_recover index_small
  rw [←recover_w] at this
  have := binary_nat_unique _ _ this
  rw [recover_w] at this
  rw [create_dir_vec_bit, ←this]
  simp [Vector.map_reverse, bit_to_dir_to_bit]
  rfl

theorem nat_to_dir_vec_correct' {Index : F}:
  is_vector_binary w →
  recover_binary_zmod' w = Index →
  (nat_to_dir_vec (Index.val) D) = (Dir.create_dir_vec w).reverse := by
    intros
    rw [<-vector_reverse_eq]
    rw [nat_to_dir_vec_correct]
    assumption
    assumption

theorem insertion_round_uncps [Fact (perfect_hash poseidon₂)] (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (Proof : Vector F D) (k : F → Prop):
  insertion_round Index Item Tree.root Proof k ↔
  item_at_nat Tree Index.val = 0 ∧ k (set_at_nat Tree Index.val Item).root := by
  unfold insertion_round
  apply Iff.intro
  . intros
    casesm* (∃_,_), (_∧_)
    apply And.intro
    . unfold item_at_nat
      apply MerkleTree.proof_ceritfies_item (proof := Proof.reverse)
      rw [←MerkleTree.recover_tail_reverse_equals_recover]
      rw [nat_to_dir_vec_correct]
      . simp
        assumption
      . assumption
      . assumption
    . simp [set_at_nat]
      rw [←MerkleTree.proof_insert_invariant (proof := Proof.reverse) (old := 0)]
      rw [←MerkleTree.recover_tail_reverse_equals_recover]
      rw [nat_to_dir_vec_correct]
      . simp
        assumption
      . assumption
      . assumption
      . rw [←MerkleTree.recover_tail_reverse_equals_recover]
        rw [nat_to_dir_vec_correct]
        . simp
          assumption
        . assumption
        . assumption
  . intros
    casesm* (_∧_)
    rename_i h₁ h₂
    unfold item_at_nat at h₁
    simp at h₁
    simp [set_at_nat] at h₂
    rw [←MerkleTree.proof_insert_invariant (proof := Proof) (old := 0) (new := Item)] at h₂
    rw [←MerkleTree.recover_tail_reverse_equals_recover] at h₂
    --rw [nat_to_dir_vec_correct] at h₂
    simp at h₂
    rotate_left
    
    repeat (
      sorry
    )

theorem insertion_round_uncps' [Fact (perfect_hash poseidon₂)] (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (Proof : Vector F D) (k : F → Prop):
  insertion_round Index Item Tree.root Proof k ↔
  (MerkleTree.recover poseidon₂ (nat_to_dir_vec (Index.val) D) Proof.reverse 0 = Tree.root) ∧ k (set_at_nat Tree Index.val Item).root := by sorry

theorem InsertIsSet [Fact (perfect_hash poseidon₂)] {Tree : MerkleTree F poseidon₂ D} {Index: F} {Item: F} {Proof: Vector F D} {k: F -> Prop} :
  insertion_round Index Item Tree.root Proof k ↔
  TreeInsert Tree Index Item Proof k := by
    simp [insertion_round]
    simp [TreeInsert]
    apply exists_congr
    intro out
    simp
    intros
    have : MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec out) Proof Item = (Tree.set (Dir.create_dir_vec out).reverse Item).root := by
      simp [recover_tail_reverse_equals_recover'] at *
      rw [MerkleTree.proof_insert_invariant (Dir.create_dir_vec out).reverse Tree 0 Item Proof.reverse]
      assumption
    simp [<-MerkleTree.recover_tail_reverse_equals_recover] at this
    simp [this]

def item_at_invariant { depth : Nat } {F: Type} {H : Hash F 2} {tree : MerkleTree F H depth} {ix₁ ix₂ : Vector Dir depth} {item₁ item₂ : F} {h₁ : ix₁ ≠ ix₂} {h₁ : depth > 0} :
  (MerkleTree.item_at (tree.set ix₁ item₁) ix₂ = item₂) ↔ (tree.item_at ix₂ = item₂) := by
    apply Iff.intro
    case mp => {
      intro h
      induction depth
      case zero => {
        apply absurd h₁
        linarith
      }
      case succ ih _ => {
        simp [MerkleTree.set, MerkleTree.item_at] at h
        split at h
        case h_1 => {
          have : Vector.head ix₂ = Dir.right := by
            sorry
          simp [this] at h
          simp [MerkleTree.tree_for] at h
          
          sorry
        }
        case h_2 => {
          sorry
        }
      }
    }
    case mpr => {
      intro h
      induction depth
      case zero => {
        apply absurd h₁
        linarith
      }
      case succ _ ih => {
        sorry
      }
    }

-- def recover_invariant { depth : Nat } {F: Type} {H : Hash F 2} [Fact (perfect_hash H)] (tree : MerkleTree F H depth) (ix₁ ix₂ : Vector Dir depth) (proof : Vector F depth) (item₁ item₂ : F) :
--   (MerkleTree.recover H ix₁ proof item₁ = MerkleTree.root (tree.set ix₂ item₂)) ↔ (MerkleTree.recover H ix₁ proof item₁ = tree.root) := by
--     apply Iff.intro
--     case mp => {
--       intro h
--       induction depth with
--       | zero => 
--         unfold MerkleTree.set at h
--         unfold MerkleTree.root at h
--         unfold MerkleTree.root
        
--         simp
--         split
--         sorry
--         sorry
--       | succ _ ih => sorry
--     }
--     case mpr => {
--       sorry
--     }

-- def recover_invariant' { depth : Nat } {F: Type} {H : Hash F 2} [Fact (perfect_hash H)] {tree : MerkleTree F H depth} {ix₁ ix₂ : Vector Dir depth} {proof : Vector F depth} {item₁ item₂ : F} :
--   (MerkleTree.recover H ix₁ proof item₁ = MerkleTree.root (tree.set ix₂ item₂)) → ((tree.set ix₂ item₂).item_at ix₁ = item₁) := by
--     induction depth
--     case zero => {
--       intro h
--       unfold MerkleTree.root at h
--       unfold MerkleTree.set at h
--       unfold MerkleTree.recover at h
--       simp at h
--       unfold MerkleTree.set
--       unfold MerkleTree.item_at
--       simp
--       apply Eq.symm
--       assumption
--     }
--     case succ _ _ => {
--       intro h
--       rw [MerkleTree.proof_ceritfies_item]
--       assumption
--       assumption
--     }

theorem val_nat_cast_of_lt {n a : ℕ} : (a : ZMod n).val = a := by
  -- rwa [ZMod.val_nat_cast, Nat.mod_eq_of_lt]
  sorry

theorem val_nat_cast_with_sum {n a : ℕ} {b : ZMod n} : (ZMod.val ((a : ZMod n) + b)) = (a + b.val) := by sorry

theorem before_insertion_all_items_zero
  [Fact (perfect_hash poseidon₂)]
  {Tree: MerkleTree F poseidon₂ D}
  (StartIndex: Nat) (IdComms: Vector F B) (MerkleProofs: Vector (Vector F D) B) (k: F -> Prop) :
  gInsertionProof ↑StartIndex Tree.root IdComms MerkleProofs k →
  (∀ i ∈ [StartIndex:StartIndex + B], item_at_nat Tree i = 0) := by
    simp [gInsertionProof]
    simp [InsertionRound_uncps, insertion_round_uncps']
    intro h1 h2 _
    simp [Gates.add] at h1 h2
    -- With longer batches, it will require more have statements. Is there a way to avoid the have statements?
    have h₁ : (MerkleTree.set Tree (nat_to_dir_vec StartIndex D) IdComms[0]).item_at (nat_to_dir_vec (StartIndex + 1) D) = (0:F) := by
      rw [MerkleTree.proof_ceritfies_item (proof:= (Vector.reverse MerkleProofs[1])) (item := (0:F))]
      rw [val_nat_cast_with_sum] at h2
      rw [val_nat_cast_of_lt] at h2
      assumption
    rw [item_at_invariant] at h₁
    rotate_left
    simp [congr_arg]
    sorry
    linarith
    simp
    have h₂ : Tree.item_at (nat_to_dir_vec StartIndex D) = (0:F) := by
      rw [MerkleTree.proof_ceritfies_item (proof:= (Vector.reverse MerkleProofs[0])) (item := (0:F))]
      rw [val_nat_cast_of_lt] at h1
      assumption
    simp [item_at_nat]
    
    intro i range
    cases range; rename_i _ up
    cases up
    case intro.refl => {
      assumption
    }
    case intro.step => {
      rename_i h₃
      simp_arith at h₃
      cases h₃
      assumption
      rename_i h₃
      simp at h₃
      rename_i m s _
      simp_arith at s
      simp_arith at h₃
      apply absurd h₃
      simp [h₃]
      linarith
    }

def main : IO Unit := pure ()