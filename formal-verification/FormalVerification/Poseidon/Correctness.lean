import FormalVerification
import FormalVerification.Poseidon.Constants
import FormalVerification.Poseidon.Spec
import Mathlib
import ProvenZk

open Matrix
open SemaphoreMTB (F Order)

variable [Fact (Nat.Prime Order)]

private lemma iff_to_eq {α} {a b: α} {k : α -> Prop }: a = b -> (k a ↔ k b) := by intro eq; rw [eq]

def mds_matmul (cfg : Constants) (S : Vector cfg.F cfg.t) : Vector cfg.F cfg.t := (cfg.MDS_matrix ⬝ S.to_column).to_vector

def full_round (cfg : Constants) (S C: Vector cfg.F cfg.t) : Vector cfg.F cfg.t :=
  mds_matmul cfg (S.mapIdx fun i s => (s + C.get i) ^ 5)

def partial_round (cfg : Constants) (S C: Vector cfg.F cfg.t) : Vector cfg.F cfg.t :=
  let with_const := S.mapIdx fun i s => s + C.get i
  mds_matmul cfg (with_const.set 0 (with_const.get 0 ^ 5))

def full_rounds (cfg : Constants) (state_words : Vector cfg.F cfg.t) (round_constants_counter rounds : ℕ) : Vector cfg.F cfg.t := Id.run do
  let mut round_constants_counter := round_constants_counter
  let mut state_words := state_words

  for _ in [0:rounds] do
    let consts := Vector.ofFn (fun i => cfg.round_constants[round_constants_counter + i]!)
    state_words := full_round cfg state_words consts
    round_constants_counter := round_constants_counter + cfg.t
  state_words

def partial_rounds (cfg : Constants) (state_words : Vector cfg.F cfg.t) (round_constants_counter rounds : ℕ) : Vector cfg.F cfg.t := Id.run do
  let mut round_constants_counter := round_constants_counter
  let mut state_words := state_words

  for _ in [0:rounds] do
    let consts := Vector.ofFn (fun i => cfg.round_constants[round_constants_counter + i]!)
    state_words := partial_round cfg state_words consts
    round_constants_counter := round_constants_counter + cfg.t
  state_words

def full_rounds_cps
    (cfg : Constants)
    (full_round : Vector cfg.F cfg.t -> Vector cfg.F cfg.t -> (Vector cfg.F cfg.t -> Prop) -> Prop)
    (state: Vector cfg.F cfg.t)
    (init_const: Nat)
    (round_count: Nat)
    (k : Vector cfg.F cfg.t -> Prop): Prop := match round_count with
| Nat.zero => k state
| Nat.succ round_count =>
    full_round state (Vector.ofFn fun i => cfg.round_constants[init_const + i]!) fun state' =>
        full_rounds_cps cfg full_round state' (init_const + cfg.t) round_count k

def half_rounds_cps
    (cfg : Constants)
    (half_round : Vector cfg.F cfg.t -> Vector cfg.F cfg.t -> (Vector cfg.F cfg.t -> Prop) -> Prop)
    (state: Vector cfg.F cfg.t)
    (init_const: Nat)
    (round_count: Nat)
    (k : Vector cfg.F cfg.t -> Prop): Prop := match round_count with
| Nat.zero => k state
| Nat.succ round_count =>
    half_round state (Vector.ofFn fun i => cfg.round_constants[init_const + i]!) fun state' =>
        half_rounds_cps cfg half_round state' (init_const + cfg.t) round_count k

lemma sbox_uncps (A : F) (k : F -> Prop): SemaphoreMTB.sbox A k = k (A ^ 5) := by
  unfold SemaphoreMTB.sbox
  simp [Gates.mul]
  apply iff_to_eq
  repeat (rw [pow_succ])
  rw [pow_zero, mul_one, mul_assoc]

lemma mds_3_uncps (S : Vector F 3) (k : Vector F 3 -> Prop):
  SemaphoreMTB.mds_3 S k = k (mds_matmul Constants.x5_254_3 S) := by
  simp [SemaphoreMTB.mds_3, Gates.add, Gates.mul]
  apply iff_to_eq
  simp [mds_matmul, Constants.x5_254_3, Constants.x5_254_3_MDS_matrix]
  simp [Vector.to_column, Matrix.to_vector, Vector.ofFn]
  repeat (
    apply congrArg₂
    {
      simp [getElem, Matrix.of, Matrix.mul, Matrix.dotProduct]
      simp [Finset.sum, Finset.univ, Fintype.elems]
      rw [←add_assoc]
      conv => lhs; simp [mul_comm]
    }
  )
  rfl

lemma full_round_3_uncps (S C: Vector F 3) (k : Vector F 3 -> Prop):
  SemaphoreMTB.fullRound_3_3 S C k = k (full_round Constants.x5_254_3 S C) := by
  sorry
  --unfold SemaphoreMTB.fullRound_3_3
  --unfold Gates.add
  --simp [Gates.add, sbox_uncps, mds_3_uncps, full_round]
  --apply iff_to_eq
  --have : ∀ {α} {v : Vector α 3}, vec![v[0], v[1], v[2]] = v := by
  --  intro α v
  --  conv => rhs; rw [←Vector.ofFn_get v]
  --rw [this]
  --congr
  --conv => rhs ; rw [←Vector.ofFn_get S]

lemma half_round_3_uncps (S C: Vector F 3) (k : Vector F 3 -> Prop):
  SemaphoreMTB.halfRound_3_3 S C k = k (partial_round Constants.x5_254_3 S C) := by
  sorry
  --unfold SemaphoreMTB.halfRound_3_3
  --unfold Gates.add
  --simp [Gates.add, sbox_uncps, mds_3_uncps, partial_round]
  --apply iff_to_eq
  --have : ∀ {α} {v : Vector α 3}, vec![v[0], v[1], v[2]] = v := by
  --  intro α v
  --  conv => rhs; rw [←Vector.ofFn_get v]
  --rw [this]
  --congr
  --conv => rhs ; rw [←Vector.ofFn_get S]

lemma partial_rounds_uncps
  {cfg : Constants}
  {S : Vector cfg.F cfg.t}
  {start count : Nat}
  {k : Vector cfg.F cfg.t -> Prop}
  {half_round_cps : Vector cfg.F cfg.t -> Vector cfg.F cfg.t -> (Vector cfg.F cfg.t -> Prop) -> Prop}
  {half_round_uncps : ∀ S C k, half_round_cps S C k = k (partial_round cfg S C)}
  :
  half_rounds_cps cfg half_round_cps S start count k = k (partial_rounds cfg S start count) := by
  induction count generalizing start S with
  | zero =>
    simp [half_rounds_cps, partial_rounds, forIn, Std.Range.forIn, Std.Range.forIn.loop, Id.run]
  | succ count ih =>
    unfold half_rounds_cps
    rw [half_round_uncps, ih]
    unfold partial_rounds
    simp [Id.run, forIn]
    apply iff_to_eq
    simp [Std.Range.counter_elide_fst]
    rw [←zero_add (Nat.succ count), Std.Range.forIn_startSucc]
    have : Nat.succ 0 = 0 + 1 := by rfl
    rw [this]
    have : 0 + Nat.succ count = count + 1 := by simp_arith
    rw [this]
    rw [←Std.Range.forIn_ixShift]
    apply congrArg₂
    { simp }
    funext i r
    congr
    funext i'
    have : start + cfg.t + i * cfg.t + ↑i' = start + (i + 1) * cfg.t + ↑i' := by linarith
    rw [this]

lemma partial_rounds_3_uncps
  {S : Vector F 3}
  {start count : Nat}
  {k : Vector F 3 -> Prop}:
  half_rounds_cps Constants.x5_254_3 SemaphoreMTB.halfRound_3_3 S start count k = k (partial_rounds Constants.x5_254_3 S start count) := by
  apply partial_rounds_uncps
  apply half_round_3_uncps

lemma full_rounds_uncps
  {cfg : Constants}
  {S : Vector cfg.F cfg.t}
  {start count : Nat}
  {k : Vector cfg.F cfg.t -> Prop}
  {full_round_cps : Vector cfg.F cfg.t -> Vector cfg.F cfg.t -> (Vector cfg.F cfg.t -> Prop) -> Prop}
  {full_round_uncps : ∀ S C k, full_round_cps S C k = k (full_round cfg S C)}
  :
  full_rounds_cps cfg full_round_cps S start count k = k (full_rounds cfg S start count) := by
  induction count generalizing start S with
  | zero =>
    simp [full_rounds_cps, full_rounds, forIn, Std.Range.forIn, Std.Range.forIn.loop, Id.run]
  | succ count ih =>
    unfold full_rounds_cps
    rw [full_round_uncps, ih]
    unfold full_rounds
    simp [Id.run, forIn]
    apply iff_to_eq
    simp [Std.Range.counter_elide_fst]
    rw [←zero_add (Nat.succ count), Std.Range.forIn_startSucc]
    have : Nat.succ 0 = 0 + 1 := by rfl
    rw [this]
    have : 0 + Nat.succ count = count + 1 := by simp_arith
    rw [this]
    rw [←Std.Range.forIn_ixShift]
    apply congrArg₂
    { simp }
    funext i r
    congr
    funext i'
    have : start + cfg.t + i * cfg.t + ↑i' = start + (i + 1) * cfg.t + ↑i' := by linarith
    rw [this]

lemma full_rounds_3_uncps
  {S : Vector F 3}
  {start count : Nat}
  {k : Vector F 3 -> Prop}:
  full_rounds_cps Constants.x5_254_3 SemaphoreMTB.fullRound_3_3 S start count k = k (full_rounds Constants.x5_254_3 S start count) := by
  apply full_rounds_uncps
  apply full_round_3_uncps

lemma fold_vec_2 {v : Vector F 2}: vec![v[0], v[1]] = v := by
    conv => rhs; rw [←Vector.ofFn_get v]

def looped_poseidon_3 (inp : Vector F 3) (k: Vector F 3 -> Prop): Prop :=
    full_rounds_cps Constants.x5_254_3 SemaphoreMTB.fullRound_3_3 inp 0 4 fun state =>
    half_rounds_cps Constants.x5_254_3 SemaphoreMTB.halfRound_3_3 state 12 57  fun state' =>
    full_rounds_cps Constants.x5_254_3 SemaphoreMTB.fullRound_3_3 state' 183 4 k

lemma fold_vec_3 {v : Vector F 3}: vec![v[0], v[1], v[2]] = v := by
    conv => rhs; rw [←Vector.ofFn_get v]

set_option maxRecDepth 2048

theorem looped_poseidon_3_go (inp : Vector F 3) (k : Vector F 3 -> Prop):
    SemaphoreMTB.poseidon_3 inp k = looped_poseidon_3 inp k := by
    unfold looped_poseidon_3
    unfold SemaphoreMTB.poseidon_3
    simp [full_rounds_cps, half_rounds_cps, getElem!, fold_vec_3, Vector.ofFn]
    rfl

set_option maxRecDepth 512

def perm_folded (cfg : Constants) (input_words : Vector cfg.F cfg.t): Vector cfg.F cfg.t := Id.run do
  let R_f := cfg.R_F / 2
  let mut round_constants_counter := 0
  let mut state_words := input_words

  state_words := full_rounds cfg state_words round_constants_counter R_f
  round_constants_counter := R_f * cfg.t

  state_words := partial_rounds cfg state_words round_constants_counter cfg.R_P
  round_constants_counter := R_f * cfg.t + cfg.R_P * cfg.t

  state_words := full_rounds cfg state_words round_constants_counter R_f

  state_words

theorem perm_folded_go (cfg : Constants) (input_words : Vector cfg.F cfg.t):
  Poseidon.perm cfg input_words = perm_folded cfg input_words := by
  unfold Poseidon.perm
  unfold perm_folded
  unfold full_rounds
  unfold partial_rounds
  simp [Id.run, forIn]
  simp [Std.Range.counter_elide_fst]
  cases cfg; rename_i prime t t_ne_zero R_F R_P round_constants MDS_matrix
  cases t
  { contradiction }
  rename_i t'
  simp at *
  apply congrArg₂
  {
    apply congrArg₂
    {
      apply congrArg
      funext i r
      unfold full_round
      unfold mds_matmul
      simp
      apply congrArg
      apply congrArg
      apply congrArg
      apply congrArg
      rw [Vector.setLoop_def (f := fun _ r => r ^ 5)]
      rw [Vector.setLoop_def (f := fun i' r => r + round_constants[i * Nat.succ t' + i']!)]
      simp [Vector.setLoop_mapIdx, Vector.mapIdx_compose]
      rw [Vector.mapIdx_mod]
    }
    {
      funext i r
      rw [Vector.setLoop_def (f := fun i' r => r + round_constants[R_F / 2 * Nat.succ t' + i * Nat.succ t' + i']!)]
      rw [Vector.setLoop_mapIdx]
      apply congrArg
      unfold partial_round
      simp
      unfold mds_matmul
      simp
      apply congrArg
      apply congrArg
      apply congrArg
      rw [Vector.mapIdx_mod]
    }
  }
  {
    funext i r
    apply congrArg
    unfold full_round
    unfold mds_matmul
    simp
    apply congrArg
    apply congrArg
    apply congrArg
    rw [Vector.setLoop_def (f := fun _ r => r ^ 5)]
    rw [Vector.setLoop_def (f := fun i' r => r + round_constants[R_F / 2 * Nat.succ t' + R_P * Nat.succ t' + i * Nat.succ t' + i']!)]
    simp [Vector.setLoop_mapIdx, Vector.mapIdx_compose]
    rw [Vector.mapIdx_mod]
  }

theorem poseidon_3_correct (inp : Vector F 3) (k : Vector F 3 -> Prop):
  SemaphoreMTB.poseidon_3 inp k = k (Poseidon.perm Constants.x5_254_3 inp) := by
  simp [
    looped_poseidon_3_go,
    looped_poseidon_3,
    full_rounds_uncps,
    partial_rounds_3_uncps,
    full_rounds_3_uncps,
    perm_folded_go,
    perm_folded
  ]
  rfl