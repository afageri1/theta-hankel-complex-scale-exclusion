/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch056

/-! Exact signed weight and batch integral certificates, batch 56 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch056Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-90651050269 / 500000000000 : ℝ)
  | 1 => (-9191783797 / 50000000000 : ℝ)
  | 2 => (-7455907051 / 40000000000 : ℝ)
  | 3 => (-94494181891 / 500000000000 : ℝ)
  | 4 => (-23951000337 / 125000000000 : ℝ)
  | 5 => (-97128429631 / 500000000000 : ℝ)
  | 6 => (-98467600873 / 500000000000 : ℝ)
  | 7 => (-6238853139 / 31250000000 : ℝ)
  | 8 => (-202381427717 / 1000000000000 : ℝ)
  | 9 => (-5128746449 / 25000000000 : ℝ)
  | 10 => (-207948867657 / 1000000000000 : ℝ)
  | 11 => (-210778735371 / 1000000000000 : ℝ)
  | 12 => (-26704967721 / 125000000000 : ℝ)
  | 13 => (-216532169619 / 1000000000000 : ℝ)
  | 14 => (-13716018989 / 62500000000 : ℝ)
  | 15 => (-111206215709 / 500000000000 : ℝ)
  | 16 => (-45080168317 / 200000000000 : ℝ)
  | 17 => (-9136873027 / 40000000000 : ℝ)
  | 18 => (-115737838607 / 500000000000 : ℝ)
  | 19 => (-58640672979 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch056Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-89398344907 / 500000000000 : ℝ)
  | 1 => (-181302100537 / 1000000000000 : ℝ)
  | 2 => (-183835675939 / 1000000000000 : ℝ)
  | 3 => (-93198838137 / 500000000000 : ℝ)
  | 4 => (-188988363781 / 1000000000000 : ℝ)
  | 5 => (-38321600539 / 200000000000 : ℝ)
  | 6 => (-194256859261 / 1000000000000 : ℝ)
  | 7 => (-39387040349 / 200000000000 : ℝ)
  | 8 => (-199643300447 / 1000000000000 : ℝ)
  | 9 => (-50595356929 / 250000000000 : ℝ)
  | 10 => (-205149857959 / 1000000000000 : ℝ)
  | 11 => (-25993608457 / 125000000000 : ℝ)
  | 12 => (-21077873537 / 100000000000 : ℝ)
  | 13 => (-213639741767 / 1000000000000 : ℝ)
  | 14 => (-108266084809 / 500000000000 : ℝ)
  | 15 => (-219456303823 / 1000000000000 : ℝ)
  | 16 => (-222412431417 / 1000000000000 : ℝ)
  | 17 => (-14087552599 / 62500000000 : ℝ)
  | 18 => (-114210912837 / 500000000000 : ℝ)
  | 19 => (-231475677213 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch056Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1120 : ℝ) + (j.val : ℝ)) / 1600)
      (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch056Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch056Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1120 : ℝ) + (j.val : ℝ)) / 1600)
    (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch056Neg100WeightLower j.val) (hpThetaShiftTwoBatch056Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch056Neg100WeightLower, hpThetaShiftTwoBatch056Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch056Neg100_integral_bounds :
    (-5461627653 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-10544277049 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch056Lower hpThetaJensenCellsBatch056Upper
    hpThetaShiftTwoBatch056Neg100WeightLower hpThetaShiftTwoBatch056Neg100WeightUpper hpThetaJensenCellsBatch056_bounds hpThetaShiftTwoBatch056Neg100_weight_bounds
  have hl : (-5461627653 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch056Lower j * hpThetaShiftTwoBatch056Neg100WeightLower j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftTwoBatch056Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftTwoBatch056Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch056Lower j * hpThetaShiftTwoBatch056Neg100WeightUpper j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftTwoBatch056Neg100WeightUpper j) / 1600) ≤ (-10544277049 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftTwoBatch056Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1120 : ℝ) / 1600 = 56 / 80 by norm_num,
    show ((1120 : ℝ) + 20) / 1600 = (56 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch056Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (886732037 / 125000000000 : ℝ)
  | 1 => (217257893 / 31250000000 : ℝ)
  | 2 => (3403595809 / 500000000000 : ℝ)
  | 3 => (266345159 / 40000000000 : ℝ)
  | 4 => (650651979 / 100000000000 : ℝ)
  | 5 => (793852349 / 125000000000 : ℝ)
  | 6 => (6191480299 / 1000000000000 : ℝ)
  | 7 => (188389319 / 31250000000 : ℝ)
  | 8 => (1172341199 / 200000000000 : ℝ)
  | 9 => (2845588357 / 500000000000 : ℝ)
  | 10 => (344801437 / 62500000000 : ℝ)
  | 11 => (166831157 / 31250000000 : ℝ)
  | 12 => (322278161 / 62500000000 : ℝ)
  | 13 => (2485167487 / 500000000000 : ℝ)
  | 14 => (4780201109 / 1000000000000 : ℝ)
  | 15 => (4585999429 / 1000000000000 : ℝ)
  | 16 => (877535987 / 200000000000 : ℝ)
  | 17 => (4185192183 / 1000000000000 : ℝ)
  | 18 => (1989242639 / 500000000000 : ℝ)
  | 19 => (3767507869 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch056Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (7232046821 / 1000000000000 : ℝ)
  | 1 => (7093856297 / 1000000000000 : ℝ)
  | 2 => (6952252577 / 1000000000000 : ℝ)
  | 3 => (6807191619 / 1000000000000 : ℝ)
  | 4 => (416164311 / 62500000000 : ℝ)
  | 5 => (6506519791 / 1000000000000 : ℝ)
  | 6 => (6350818793 / 1000000000000 : ℝ)
  | 7 => (61914803 / 10000000000 : ℝ)
  | 8 => (6028458209 / 1000000000000 : ℝ)
  | 9 => (1465426499 / 250000000000 : ℝ)
  | 10 => (1138235343 / 200000000000 : ℝ)
  | 11 => (5516822993 / 1000000000000 : ℝ)
  | 12 => (213543881 / 40000000000 : ℝ)
  | 13 => (5156450577 / 1000000000000 : ℝ)
  | 14 => (198813399 / 40000000000 : ℝ)
  | 15 => (478020111 / 100000000000 : ℝ)
  | 16 => (458599943 / 100000000000 : ℝ)
  | 17 => (68557499 / 15625000000 : ℝ)
  | 18 => (523149023 / 125000000000 : ℝ)
  | 19 => (3978485279 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch056Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1120 : ℝ) + (j.val : ℝ)) / 1600)
      (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch056Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch056Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1120 : ℝ) + (j.val : ℝ)) / 1600)
    (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch056Neg65WeightLower j.val) (hpThetaShiftTwoBatch056Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch056Neg65WeightLower, hpThetaShiftTwoBatch056Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch056Neg65_integral_bounds :
    (291661133 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (307166031 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch056Lower hpThetaJensenCellsBatch056Upper
    hpThetaShiftTwoBatch056Neg65WeightLower hpThetaShiftTwoBatch056Neg65WeightUpper hpThetaJensenCellsBatch056_bounds hpThetaShiftTwoBatch056Neg65_weight_bounds
  have hl : (291661133 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch056Lower j * hpThetaShiftTwoBatch056Neg65WeightLower j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftTwoBatch056Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftTwoBatch056Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch056Lower j * hpThetaShiftTwoBatch056Neg65WeightUpper j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftTwoBatch056Neg65WeightUpper j) / 1600) ≤ (307166031 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftTwoBatch056Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1120 : ℝ) / 1600 = 56 / 80 by norm_num,
    show ((1120 : ℝ) + 20) / 1600 = (56 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch056Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (5495820221 / 500000000000 : ℝ)
  | 1 => (5541576201 / 500000000000 : ℝ)
  | 2 => (11174884623 / 1000000000000 : ℝ)
  | 3 => (11266832251 / 1000000000000 : ℝ)
  | 4 => (11358990353 / 1000000000000 : ℝ)
  | 5 => (5725676957 / 500000000000 : ℝ)
  | 6 => (5771958917 / 500000000000 : ℝ)
  | 7 => (1163667693 / 100000000000 : ℝ)
  | 8 => (733101621 / 62500000000 : ℝ)
  | 9 => (11822759499 / 1000000000000 : ℝ)
  | 10 => (11916072181 / 1000000000000 : ℝ)
  | 11 => (1501194807 / 125000000000 : ℝ)
  | 12 => (12103212713 / 1000000000000 : ℝ)
  | 13 => (48788117 / 4000000000 : ℝ)
  | 14 => (6145501139 / 500000000000 : ℝ)
  | 15 => (12385125917 / 1000000000000 : ℝ)
  | 16 => (12479394197 / 1000000000000 : ℝ)
  | 17 => (392931283 / 31250000000 : ℝ)
  | 18 => (6334170171 / 500000000000 : ℝ)
  | 19 => (12763005807 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch056Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (11083152403 / 1000000000000 : ℝ)
  | 1 => (698430289 / 62500000000 : ℝ)
  | 2 => (2816708063 / 250000000000 : ℝ)
  | 3 => (5679495177 / 500000000000 : ℝ)
  | 4 => (2290270783 / 200000000000 : ℝ)
  | 5 => (2308783567 / 200000000000 : ℝ)
  | 6 => (11636676931 / 1000000000000 : ℝ)
  | 7 => (11729625937 / 1000000000000 : ℝ)
  | 8 => (23645519 / 2000000000 : ℝ)
  | 9 => (5958036091 / 500000000000 : ℝ)
  | 10 => (12009558457 / 1000000000000 : ℝ)
  | 11 => (6051606357 / 500000000000 : ℝ)
  | 12 => (12197029251 / 1000000000000 : ℝ)
  | 13 => (12291002279 / 1000000000000 : ℝ)
  | 14 => (6192562959 / 500000000000 : ℝ)
  | 15 => (6239697099 / 500000000000 : ℝ)
  | 16 => (12573801057 / 1000000000000 : ℝ)
  | 17 => (12668340343 / 1000000000000 : ℝ)
  | 18 => (797687863 / 62500000000 : ℝ)
  | 19 => (1607223889 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch056Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1120 : ℝ) + (j.val : ℝ)) / 1600)
      (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch056Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch056Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1120 : ℝ) + (j.val : ℝ)) / 1600)
    (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch056Neg45WeightLower j.val) (hpThetaShiftTwoBatch056Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch056Neg45WeightLower, hpThetaShiftTwoBatch056Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch056Neg45_integral_bounds :
    (614382187 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (316414427 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch056Lower hpThetaJensenCellsBatch056Upper
    hpThetaShiftTwoBatch056Neg45WeightLower hpThetaShiftTwoBatch056Neg45WeightUpper hpThetaJensenCellsBatch056_bounds hpThetaShiftTwoBatch056Neg45_weight_bounds
  have hl : (614382187 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch056Lower j * hpThetaShiftTwoBatch056Neg45WeightLower j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftTwoBatch056Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftTwoBatch056Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch056Lower j * hpThetaShiftTwoBatch056Neg45WeightUpper j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftTwoBatch056Neg45WeightUpper j) / 1600) ≤ (316414427 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftTwoBatch056Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1120 : ℝ) / 1600 = 56 / 80 by norm_num,
    show ((1120 : ℝ) + 20) / 1600 = (56 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch056Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-755696687 / 200000000000 : ℝ)
  | 1 => (-3771560311 / 1000000000000 : ℝ)
  | 2 => (-1882188627 / 500000000000 : ℝ)
  | 3 => (-751386457 / 200000000000 : ℝ)
  | 4 => (-3661351 / 976562500 : ℝ)
  | 5 => (-1870624341 / 500000000000 : ℝ)
  | 6 => (-3733006067 / 1000000000000 : ℝ)
  | 7 => (-1862246791 / 500000000000 : ℝ)
  | 8 => (-3715709223 / 1000000000000 : ℝ)
  | 9 => (-3706650981 / 1000000000000 : ℝ)
  | 10 => (-3697316843 / 1000000000000 : ℝ)
  | 11 => (-460963099 / 125000000000 : ℝ)
  | 12 => (-3677812803 / 1000000000000 : ℝ)
  | 13 => (-3667638847 / 1000000000000 : ℝ)
  | 14 => (-3657180891 / 1000000000000 : ℝ)
  | 15 => (-3646436897 / 1000000000000 : ℝ)
  | 16 => (-1817702411 / 500000000000 : ℝ)
  | 17 => (-453010327 / 125000000000 : ℝ)
  | 18 => (-903117057 / 250000000000 : ℝ)
  | 19 => (-3600559599 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch056Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-377156031 / 100000000000 : ℝ)
  | 1 => (-3764377253 / 1000000000000 : ℝ)
  | 2 => (-939233071 / 250000000000 : ℝ)
  | 3 => (-3749223423 / 1000000000000 : ℝ)
  | 4 => (-3741248681 / 1000000000000 : ℝ)
  | 5 => (-1866503033 / 500000000000 : ℝ)
  | 6 => (-3724493581 / 1000000000000 : ℝ)
  | 7 => (-1857854611 / 500000000000 : ℝ)
  | 8 => (-185332549 / 50000000000 : ℝ)
  | 9 => (-1848658421 / 500000000000 : ℝ)
  | 10 => (-3687704791 / 1000000000000 : ℝ)
  | 11 => (-1838906401 / 500000000000 : ℝ)
  | 12 => (-1833819423 / 500000000000 : ℝ)
  | 13 => (-365718089 / 100000000000 : ℝ)
  | 14 => (-113951153 / 31250000000 : ℝ)
  | 15 => (-3635404821 / 1000000000000 : ℝ)
  | 16 => (-724816523 / 200000000000 : ℝ)
  | 17 => (-3612468227 / 1000000000000 : ℝ)
  | 18 => (-1800279799 / 500000000000 : ℝ)
  | 19 => (-1794177333 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch056Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1120 : ℝ) + (j.val : ℝ)) / 1600)
      (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch056Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch056Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1120 : ℝ) + (j.val : ℝ)) / 1600)
    (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch056Neg25WeightLower j.val) (hpThetaShiftTwoBatch056Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch056Neg25WeightLower, hpThetaShiftTwoBatch056Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch056Neg25_integral_bounds :
    (-19643033 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-191721183 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch056Lower hpThetaJensenCellsBatch056Upper
    hpThetaShiftTwoBatch056Neg25WeightLower hpThetaShiftTwoBatch056Neg25WeightUpper hpThetaJensenCellsBatch056_bounds hpThetaShiftTwoBatch056Neg25_weight_bounds
  have hl : (-19643033 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch056Lower j * hpThetaShiftTwoBatch056Neg25WeightLower j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftTwoBatch056Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftTwoBatch056Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch056Lower j * hpThetaShiftTwoBatch056Neg25WeightUpper j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftTwoBatch056Neg25WeightUpper j) / 1600) ≤ (-191721183 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftTwoBatch056Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1120 : ℝ) / 1600 = 56 / 80 by norm_num,
    show ((1120 : ℝ) + 20) / 1600 = (56 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch056Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch056Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch056Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch056Neg25_integral_bounds
end HodgeProofHP
