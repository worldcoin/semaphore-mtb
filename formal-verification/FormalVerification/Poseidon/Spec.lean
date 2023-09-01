import Mathlib
import ProvenZk
import FormalVerification.Poseidon.Constants

open Matrix

namespace Poseidon

def perm (cfg : Constants) (input_words : Vector cfg.F cfg.t): Vector cfg.F cfg.t := Id.run do
  let R_f := cfg.R_F / 2
  let mut round_constants_counter := 0
  let mut state_words := input_words
  for _ in [0:R_f] do
    for i in [0:cfg.t] do
      state_words := state_words.set i (state_words.get i + cfg.round_constants[round_constants_counter]!)
      round_constants_counter := round_constants_counter + 1
    for i in [0:cfg.t] do
      state_words := state_words.set i (state_words.get i ^ 5)
    state_words := (cfg.MDS_matrix ⬝ state_words.to_column).to_vector

  for _ in [0:cfg.R_P] do
    for i in [0:cfg.t] do
      state_words := state_words.set i (state_words.get i + cfg.round_constants[round_constants_counter]!)
      round_constants_counter := round_constants_counter + 1
    state_words := state_words.set 0 (state_words.get 0 ^ 5)
    state_words := (cfg.MDS_matrix ⬝ state_words.to_column).to_vector

  for _ in [0:R_f] do
    for i in [0:cfg.t] do
      state_words := state_words.set i (state_words.get i + cfg.round_constants[round_constants_counter]!)
      round_constants_counter := round_constants_counter + 1
    for i in [0:cfg.t] do
      state_words := state_words.set i (state_words.get i ^ 5)
    state_words := (cfg.MDS_matrix ⬝ state_words.to_column).to_vector

  state_words

theorem test_vector_correct_x5_254_3:
  perm Constants.x5_254_3 vec![0,1,2] = vec![0x115cc0f5e7d690413df64c6b9662e9cf2a3617f2743245519e19607a4417189a, 0x0fca49b798923ab0239de1c9e7a4a9a2210312b6a2f616d18b5a87f9b628ae29, 0x0e7ae82e40091e63cbd4f16a6d16310b3729d4b6e138fcf54110e2867045a30c] :=
    by eq_refl

end Poseidon