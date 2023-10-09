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

def mod_two' (inp : Nat) : Bit := match h:inp%2 with
 | 0 => Bit.zero
 | 1 => Bit.one
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

def nat_to_bits_le (l : Nat): Nat → Option (Vector Bit l) := match l with
  | 0 => fun i => if i = 0 then some Vector.nil else none
  | Nat.succ l => fun i => do
    let x := i / 2
    let y := mod_two' i
    let xs ← nat_to_bits_le l x
    some (y ::ᵥ xs)

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

def nat_to_dir_vec (idx : Nat) (depth : Nat ): Option <| Vector Dir depth :=
  (Vector.reverse ∘ Vector.map bit_to_dir) <$> nat_to_bits_le depth idx

-- theorem nat_to_list_bits_le_recover {l i}: nat_to_bits_le l i

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

-- theorem nat_to_dir_vec_recover {ix d: ℕ} : ix < 2^d → recover_binary_nat (Vector.map dir_to_bit (nat_to_dir_vec ix d)).reverse = ix := by
--   induction' d with d ih generalizing ix
--   · intro h; simp_arith at h; cases h; rfl
--   · intro range
--     unfold nat_to_dir_vec at *
--     cases ix with
--     | zero =>
--       simp [nat_to_list_le, dir_to_bit, recover_binary_nat, recover_binary_nat_zero (n:=d)]
--     | succ ix =>
--       cases ix with
--       | zero =>
--         simp [nat_to_list_le, dir_to_bit, recover_binary_nat, recover_binary_nat_zero (n:=d)]
--       | succ ix =>
--         simp [nat_to_list_le, recover_binary_nat, mod_two]
--         rw [ih]
--         . split
--           . simp [Bit.toNat, dir_to_bit]
--             rw [←Nat.mod_add_div ix.succ.succ 2]
--             simp_arith
--             assumption
--           . simp [Bit.toNat, dir_to_bit]
--             rw [←Nat.mod_add_div ix.succ.succ 2]
--             simp_arith
--             apply Eq.symm
--             assumption
--           . contradiction
--         . rw [Nat.pow_succ, ← Nat.div_lt_iff_lt_mul] at range
--           have : Nat.succ (ix/2) = ix.succ.succ / 2 := by simp_arith
--           rw [this]
--           assumption
--           simp

def item_at_nat {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (idx : Nat) : Option F := do
  t.item_at <$> nat_to_dir_vec idx depth

def set_at_nat(t : MerkleTree F H depth) (idx: Nat) (newVal: F): Option (MerkleTree F H depth) :=
  (t.set · newVal) <$> nat_to_dir_vec idx depth

def proof_at_nat (t : MerkleTree F H depth) (idx: Nat): Option (Vector F depth) :=
  t.proof <$> nat_to_dir_vec idx depth

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

-- -- @[simp]
-- theorem odd_div_by_two : n = (1 + 2 * n ) / 2 := by
--   induction n with
--   | zero => rfl
--   | succ n ih =>
--     rw [Nat.add_div]
--     simp


theorem vector_eq_cons : (x ::ᵥ xs) = (y ::ᵥ ys) ↔ x = y ∧ xs = ys := by
  simp [Vector.eq_cons_iff]


theorem mod_two_bit_back : (Bit.toNat $ mod_two' n) = n % 2 := by
  simp [mod_two']
  split
  . simp [*]
  . simp [*]
  . contradiction

theorem recover_binary_nat_to_bits_le {w : Vector Bit d}:
  recover_binary_nat w = v ↔
  nat_to_bits_le d v = some w := by
  apply Iff.intro
  . induction d generalizing v with
    | zero =>
      cases w using Vector.casesOn
      intro h; cases h; rfl
    | succ d ih =>
      cases w using Vector.casesOn; rename_i hd tl;
      simp [recover_binary_nat, nat_to_bits_le]
      intro h
      rw [ih (v := v/2) (w := tl)]
      . conv => lhs; whnf
        congr
        rw [←Nat.mod_add_div (m := v) (k := 2), ←mod_two_bit_back] at h
        have := And.left (parity_bit_unique _ _ _ _ h)
        apply Eq.symm
        assumption
      . subst_vars
        unfold Bit.toNat
        rw [Nat.add_div]
        cases hd
        . simp
        . simp
        . simp_arith
  . induction d generalizing v with
    | zero =>
      cases w using Vector.casesOn
      simp [recover_binary_nat, nat_to_bits_le]
      tauto
    | succ d ih =>
      cases w using Vector.casesOn
      simp [recover_binary_nat, nat_to_bits_le, Bind.bind]
      intro tl htl veq
      rw [vector_eq_cons] at veq
      cases veq
      subst_vars
      rw [ih (v := v/2)]
      . rw [mod_two_bit_back]
        simp [Nat.mod_add_div]
      . assumption




-- theorem recover_binary_nat_to_bits_le {w : Vector Bit d}:
--   recover_binary_nat w = v ↔
--   nat_to_bits_le d v = some w := by
--   induction d generalizing v with
--   | zero =>
--     cases w using Vector.casesOn
--     intro h; cases h; rfl
--   | succ d ih =>
--     cases w using Vector.casesOn; rename_i hd tl;
--     simp [recover_binary_nat, nat_to_bits_le]
--     intro h
--     rw [ih (v := v/2) (w := tl)]
--     . conv => lhs; whnf
--       congr
--       rw [←Nat.mod_add_div (m := v) (k := 2), ←mod_two_bit_back] at h
--       have := And.left (parity_bit_unique _ _ _ _ h)
--       apply Eq.symm
--       assumption
--     . subst_vars
--       unfold Bit.toNat
--       rw [Nat.add_div]
--       cases hd
--       . simp
--       . simp
--       . simp_arith

theorem recover_binary_zmod'_to_bits_le {w : Vector F d}:
  2 ^ d < Order →
  is_vector_binary w →
  recover_binary_zmod' w = v →
  nat_to_bits_le d v.val = some (vector_zmod_to_bit w) := by
  intros
  rw [←recover_binary_nat_to_bits_le]
  subst_vars
  rw [recover_binary_zmod_bit]
  . apply Eq.symm
    apply binary_zmod_same_as_nat
    assumption
  . assumption

theorem zmod_to_bit_coe {w : Vector Bit d} : vector_zmod_to_bit (Vector.map (Bit.toZMod (n := Order)) w) = w := by
  induction w using Vector.inductionOn with
  | h_nil => rfl
  | h_cons ih =>
    simp [vector_zmod_to_bit] at ih
    simp [vector_zmod_to_bit, ih]
    congr
    unfold Bit.toZMod
    split <;> rfl

theorem coe_val {v : F} : ↑v.val = v := by
  cases v
  conv => lhs; whnf
  congr
  conv => lhs; arg 1; whnf
  apply Nat.mod_eq_of_lt
  assumption

theorem vector_binary_of_bit_to_zmod {w : Vector Bit d }: is_vector_binary (w.map (Bit.toZMod (n := Order))) := by
  induction w using Vector.inductionOn with
  | h_nil => trivial
  | h_cons ih =>
    simp [is_vector_binary_cons]
    apply And.intro
    . unfold Bit.toZMod
      split <;> trivial
    . apply ih

theorem recover_binary_of_to_bits {w : Vector Bit d} {v : F}:
  nat_to_bits_le d v.val = some w →
  recover_binary_zmod' (w.map Bit.toZMod) = v := by
  rw [←recover_binary_nat_to_bits_le, recover_binary_zmod_bit, zmod_to_bit_coe]
  intro h
  rw [←binary_nat_zmod_equiv]
  rw [h, coe_val]
  apply vector_binary_of_bit_to_zmod

-- theorem nat_to_dir_vec_correct {Index : F}:
--   is_vector_binary w →
--   recover_binary_zmod' w = Index →
--   (nat_to_dir_vec (Index.val) D).reverse = Dir.create_dir_vec w := by
--   intro bin recover_bin
--   rw [recover_binary_zmod_bit bin] at recover_bin
--   have : (2^D < Order) := by simp
--   have recover_w : recover_binary_nat (vector_zmod_to_bit w) = Index.val := by
--     rw [←binary_zmod_same_as_nat]
--     congr
--     assumption
--   have index_small : Index.val < 2 ^ D := by
--     rw [←recover_w]
--     apply binary_nat_lt
--   have := nat_to_dir_vec_recover index_small
--   rw [←recover_w] at this
--   have := binary_nat_unique _ _ this
--   rw [recover_w] at this
--   rw [create_dir_vec_bit, ←this]
--   simp [Vector.map_reverse, bit_to_dir_to_bit]
--   rfl

-- theorem nat_to_dir_vec_correct' {Index : F}:
--   is_vector_binary w →
--   recover_binary_zmod' w = Index →
--   (nat_to_dir_vec (Index.val) D) = (Dir.create_dir_vec w).reverse := by
--     intros
--     rw [<-vector_reverse_eq]
--     rw [nat_to_dir_vec_correct]
--     assumption
--     assumption

theorem recover_proof_reversible {H : Hash α 2} [Fact (perfect_hash H)] {Tree : MerkleTree α H d} {Proof : Vector α d}:
  MerkleTree.recover H Index Proof Item = Tree.root →
  Tree.proof Index = Proof := by
  induction d with
  | zero =>
    cases Proof using Vector.casesOn
    simp [MerkleTree.proof]
  | succ d ih =>
    cases Proof using Vector.casesOn
    cases Index using Vector.casesOn
    cases Tree
    simp [MerkleTree.root, MerkleTree.recover, MerkleTree.proof]
    intro h
    split at h <;> {
      have : perfect_hash H := (inferInstance : Fact (perfect_hash H)).out
      have := this h
      rw [vector_eq_cons, vector_eq_cons] at this
      casesm* (_ ∧ _)
      subst_vars
      simp [MerkleTree.tree_for, Dir.swap, MerkleTree.left, MerkleTree.right]
      congr
      apply ih
      assumption
    }

theorem recover_tail_equals_recover_reverse
  {F depth}
  (H : Hash F 2)
  (ix : Vector Dir depth)
  (proof : Vector F depth)
  (item : F) :
  MerkleTree.recover_tail H ix proof item = MerkleTree.recover H ix.reverse proof.reverse item := by
  have : ix = ix.reverse.reverse:= by simp
  rw [this]
  have : proof = proof.reverse.reverse := by simp
  rw [this]
  rw [MerkleTree.recover_tail_reverse_equals_recover]
  simp


theorem insertion_round_uncps [Fact (perfect_hash poseidon₂)] (Tree : MerkleTree F poseidon₂ D) (Index Item : F) (Proof : Vector F D) (k : F → Prop):
  insertion_round Index Item Tree.root Proof k ↔
  item_at_nat Tree Index.val = some 0 ∧
  proof_at_nat Tree Index.val = some Proof.reverse ∧
  ∃postTree, set_at_nat Tree Index.val Item = some postTree ∧
  k postTree.root := by
  unfold insertion_round
  apply Iff.intro
  . rintro ⟨ixbin, _⟩
    casesm* (_ ∧ _)
    have : nat_to_bits_le D Index.val = some (vector_zmod_to_bit ixbin) := by
      apply recover_binary_zmod'_to_bits_le
      . simp
      . assumption
      . assumption
    unfold item_at_nat
    unfold proof_at_nat
    unfold set_at_nat
    unfold nat_to_dir_vec
    rw [this]
    simp [←create_dir_vec_bit]
    refine ⟨?_, ⟨?_, ?_⟩⟩
    . apply MerkleTree.proof_ceritfies_item (proof := Proof.reverse)
      simpa [←MerkleTree.recover_tail_reverse_equals_recover]
    . apply recover_proof_reversible
      rw [←MerkleTree.recover_tail_reverse_equals_recover]
      simpa
    . rw [←MerkleTree.proof_insert_invariant (proof := Proof.reverse) (old := 0)]
      . rw [←MerkleTree.recover_tail_reverse_equals_recover]
        simpa
      . rw [←MerkleTree.recover_tail_reverse_equals_recover]
        simpa
  . rintro ⟨hitem, ⟨hproof, ⟨ftree, ⟨hftree, hresult⟩⟩⟩⟩
    simp [item_at_nat, nat_to_dir_vec] at hitem
    rcases hitem with ⟨bits, ⟨hbits, hitem_at⟩⟩
    simp [proof_at_nat, nat_to_dir_vec] at hproof
    rcases hproof with ⟨bits', ⟨hbits', hproof_at⟩⟩
    simp [hbits] at hbits'
    subst_vars
    simp [set_at_nat, nat_to_dir_vec] at hftree
    rcases hftree with ⟨bits'', ⟨hbits'', hftree_at⟩⟩
    simp [hbits''] at hbits
    rw [←vector_reverse_eq] at hproof_at
    subst_vars
    exists (bits''.map Bit.toZMod)
    refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
    . apply recover_binary_of_to_bits
      assumption
    . apply vector_binary_of_bit_to_zmod
    . rw [recover_tail_equals_recover_reverse, create_dir_vec_bit, zmod_to_bit_coe, ←hitem_at]
      simp [MerkleTree.recover_proof_is_root]
    . rw [recover_tail_equals_recover_reverse, create_dir_vec_bit, zmod_to_bit_coe]
      rw [MerkleTree.proof_insert_invariant _]
      . assumption
      . exact 0
      . rw [← hitem_at]
        simp [MerkleTree.recover_proof_is_root]


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


theorem item_at_invariant { depth : Nat } {F: Type} {H : Hash F 2} {tree : MerkleTree F H depth} {ix₁ ix₂ : Vector Dir depth} {item₁ : F} {neq : ix₁ ≠ ix₂}:
  (MerkleTree.item_at (tree.set ix₁ item₁) ix₂ = tree.item_at ix₂) := by
  induction depth with
  | zero =>
    cases ix₁ using Vector.casesOn
    cases ix₂ using Vector.casesOn
    cases (neq rfl)
  | succ depth ih =>
    cases ix₁ using Vector.casesOn; rename_i ix₁_hd ix₁_tl
    cases ix₂ using Vector.casesOn; rename_i ix₂_hd ix₂_tl
    cases tree; rename_i tree_l tree_r
    simp [MerkleTree.item_at, MerkleTree.set, MerkleTree.tree_for, MerkleTree.set, MerkleTree.left, MerkleTree.right]
    simp [vector_eq_cons] at neq
    split <;> { split <;> { simp [ih, neq] at * }}
    cases ix₁_hd <;> { cases ix₂_hd <;> { simp [ih, neq] } }

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