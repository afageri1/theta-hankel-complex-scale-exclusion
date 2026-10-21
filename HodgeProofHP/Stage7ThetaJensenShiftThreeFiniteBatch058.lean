/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch058

/-! Exact signed weight and batch integral certificates, batch 58 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch058Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2194797719 / 500000000000 : ℝ)
  | 1 => (-4463628073 / 1000000000000 : ℝ)
  | 2 => (-907734241 / 200000000000 : ℝ)
  | 3 => (-4614736397 / 1000000000000 : ℝ)
  | 4 => (-73309927 / 15625000000 : ℝ)
  | 5 => (-1192494947 / 250000000000 : ℝ)
  | 6 => (-2424590841 / 500000000000 : ℝ)
  | 7 => (-492945303 / 100000000000 : ℝ)
  | 8 => (-313175373 / 62500000000 : ℝ)
  | 9 => (-5093252749 / 1000000000000 : ℝ)
  | 10 => (-1035361149 / 200000000000 : ℝ)
  | 11 => (-1052295489 / 200000000000 : ℝ)
  | 12 => (-5347280459 / 1000000000000 : ℝ)
  | 13 => (-2717113759 / 500000000000 : ℝ)
  | 14 => (-1380582869 / 250000000000 : ℝ)
  | 15 => (-1402901327 / 250000000000 : ℝ)
  | 16 => (-5702062113 / 1000000000000 : ℝ)
  | 17 => (-5793715117 / 1000000000000 : ℝ)
  | 18 => (-5886577669 / 1000000000000 : ℝ)
  | 19 => (-5980663247 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch058Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4316561843 / 1000000000000 : ℝ)
  | 1 => (-4389595437 / 1000000000000 : ℝ)
  | 2 => (-557953509 / 125000000000 : ℝ)
  | 3 => (-1134667801 / 250000000000 : ℝ)
  | 4 => (-1153684099 / 250000000000 : ℝ)
  | 5 => (-4691835327 / 1000000000000 : ℝ)
  | 6 => (-4769979787 / 1000000000000 : ℝ)
  | 7 => (-4849181681 / 1000000000000 : ℝ)
  | 8 => (-4929453029 / 1000000000000 : ℝ)
  | 9 => (-5010805967 / 1000000000000 : ℝ)
  | 10 => (-1273313187 / 250000000000 : ℝ)
  | 11 => (-323550359 / 62500000000 : ℝ)
  | 12 => (-1315369361 / 250000000000 : ℝ)
  | 13 => (-2673640229 / 500000000000 : ℝ)
  | 14 => (-5434227517 / 1000000000000 : ℝ)
  | 15 => (-220893259 / 40000000000 : ℝ)
  | 16 => (-5611605307 / 1000000000000 : ℝ)
  | 17 => (-178189441 / 31250000000 : ℝ)
  | 18 => (-1448428779 / 250000000000 : ℝ)
  | 19 => (-1471644417 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch058Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1160 : ℝ) + (j.val : ℝ)) / 1600)
      (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch058Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch058Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1160 : ℝ) + (j.val : ℝ)) / 1600)
    (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch058Neg100WeightLower j.val) (hpThetaShiftThreeBatch058Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch058Neg100WeightLower, hpThetaShiftThreeBatch058Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch058Neg100_integral_bounds :
    (-31579379 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-189849 / 1250000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch058Lower hpThetaJensenCellsBatch058Upper
    hpThetaShiftThreeBatch058Neg100WeightLower hpThetaShiftThreeBatch058Neg100WeightUpper hpThetaJensenCellsBatch058_bounds hpThetaShiftThreeBatch058Neg100_weight_bounds
  have hl : (-31579379 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch058Lower j * hpThetaShiftThreeBatch058Neg100WeightLower j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftThreeBatch058Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftThreeBatch058Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch058Lower j * hpThetaShiftThreeBatch058Neg100WeightUpper j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftThreeBatch058Neg100WeightUpper j) / 1600) ≤ (-189849 / 1250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftThreeBatch058Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1160 : ℝ) / 1600 = 58 / 80 by norm_num,
    show ((1160 : ℝ) + 20) / 1600 = (58 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch058Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (295503373 / 1000000000000 : ℝ)
  | 1 => (145707701 / 500000000000 : ℝ)
  | 2 => (143595421 / 500000000000 : ℝ)
  | 3 => (70706867 / 250000000000 : ℝ)
  | 4 => (69580757 / 250000000000 : ℝ)
  | 5 => (273675247 / 1000000000000 : ℝ)
  | 6 => (13444091 / 50000000000 : ℝ)
  | 7 => (52788083 / 200000000000 : ℝ)
  | 8 => (129424337 / 500000000000 : ℝ)
  | 9 => (253604211 / 1000000000000 : ℝ)
  | 10 => (62051153 / 250000000000 : ℝ)
  | 11 => (121323717 / 500000000000 : ℝ)
  | 12 => (118465103 / 500000000000 : ℝ)
  | 13 => (231050429 / 1000000000000 : ℝ)
  | 14 => (112502787 / 500000000000 : ℝ)
  | 15 => (54698271 / 250000000000 : ℝ)
  | 16 => (212410371 / 1000000000000 : ℝ)
  | 17 => (205854819 / 1000000000000 : ℝ)
  | 18 => (9956189 / 50000000000 : ℝ)
  | 19 => (96107289 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch058Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (37432119 / 125000000000 : ℝ)
  | 1 => (147751687 / 500000000000 : ℝ)
  | 2 => (291415403 / 1000000000000 : ℝ)
  | 3 => (287190843 / 1000000000000 : ℝ)
  | 4 => (282827469 / 1000000000000 : ℝ)
  | 5 => (278323029 / 1000000000000 : ℝ)
  | 6 => (17104703 / 62500000000 : ℝ)
  | 7 => (268881821 / 1000000000000 : ℝ)
  | 8 => (4124069 / 15625000000 : ℝ)
  | 9 => (10353947 / 40000000000 : ℝ)
  | 10 => (63401053 / 250000000000 : ℝ)
  | 11 => (248204613 / 1000000000000 : ℝ)
  | 12 => (48529487 / 200000000000 : ℝ)
  | 13 => (236930207 / 1000000000000 : ℝ)
  | 14 => (23105043 / 100000000000 : ℝ)
  | 15 => (9000223 / 40000000000 : ℝ)
  | 16 => (43758617 / 200000000000 : ℝ)
  | 17 => (53102593 / 250000000000 : ℝ)
  | 18 => (10292741 / 50000000000 : ℝ)
  | 19 => (199123781 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch058Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1160 : ℝ) + (j.val : ℝ)) / 1600)
      (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch058Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch058Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1160 : ℝ) + (j.val : ℝ)) / 1600)
    (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch058Neg70WeightLower j.val) (hpThetaShiftThreeBatch058Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch058Neg70WeightLower, hpThetaShiftThreeBatch058Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch058Neg70_integral_bounds :
    (946387 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (790693 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch058Lower hpThetaJensenCellsBatch058Upper
    hpThetaShiftThreeBatch058Neg70WeightLower hpThetaShiftThreeBatch058Neg70WeightUpper hpThetaJensenCellsBatch058_bounds hpThetaShiftThreeBatch058Neg70_weight_bounds
  have hl : (946387 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch058Lower j * hpThetaShiftThreeBatch058Neg70WeightLower j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftThreeBatch058Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftThreeBatch058Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch058Lower j * hpThetaShiftThreeBatch058Neg70WeightUpper j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftThreeBatch058Neg70WeightUpper j) / 1600) ≤ (790693 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftThreeBatch058Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1160 : ℝ) / 1600 = 58 / 80 by norm_num,
    show ((1160 : ℝ) + 20) / 1600 = (58 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch058Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (123975671 / 500000000000 : ℝ)
  | 1 => (251524707 / 1000000000000 : ℝ)
  | 2 => (51025113 / 200000000000 : ℝ)
  | 3 => (129376981 / 500000000000 : ℝ)
  | 4 => (13120497 / 50000000000 : ℝ)
  | 5 => (13304677 / 50000000000 : ℝ)
  | 6 => (42157 / 156250000 : ℝ)
  | 7 => (68385939 / 250000000000 : ℝ)
  | 8 => (69327611 / 250000000000 : ℝ)
  | 9 => (56220979 / 200000000000 : ℝ)
  | 10 => (284927139 / 1000000000000 : ℝ)
  | 11 => (288777203 / 1000000000000 : ℝ)
  | 12 => (292655113 / 1000000000000 : ℝ)
  | 13 => (74140223 / 250000000000 : ℝ)
  | 14 => (300494559 / 1000000000000 : ℝ)
  | 15 => (152228067 / 500000000000 : ℝ)
  | 16 => (308445631 / 1000000000000 : ℝ)
  | 17 => (39057883 / 125000000000 : ℝ)
  | 18 => (316508443 / 1000000000000 : ℝ)
  | 19 => (20036361 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch058Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (62881177 / 250000000000 : ℝ)
  | 1 => (127562783 / 500000000000 : ℝ)
  | 2 => (258753963 / 1000000000000 : ℝ)
  | 3 => (262409941 / 1000000000000 : ℝ)
  | 4 => (266093541 / 1000000000000 : ℝ)
  | 5 => (269804801 / 1000000000000 : ℝ)
  | 6 => (273543757 / 1000000000000 : ℝ)
  | 7 => (55462089 / 200000000000 : ℝ)
  | 8 => (549033 / 1953125000 : ℝ)
  | 9 => (14246357 / 50000000000 : ℝ)
  | 10 => (72194301 / 250000000000 : ℝ)
  | 11 => (146327557 / 500000000000 : ℝ)
  | 12 => (296560893 / 1000000000000 : ℝ)
  | 13 => (1878091 / 6250000000 : ℝ)
  | 14 => (60891227 / 200000000000 : ℝ)
  | 15 => (4819463 / 15625000000 : ℝ)
  | 16 => (62492613 / 200000000000 : ℝ)
  | 17 => (79127111 / 250000000000 : ℝ)
  | 18 => (320581777 / 1000000000000 : ℝ)
  | 19 => (324683069 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch058Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1160 : ℝ) + (j.val : ℝ)) / 1600)
      (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch058Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch058Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1160 : ℝ) + (j.val : ℝ)) / 1600)
    (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch058Neg45WeightLower j.val) (hpThetaShiftThreeBatch058Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch058Neg45WeightLower, hpThetaShiftThreeBatch058Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch058Neg45_integral_bounds :
    (8502671 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (550917 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch058Lower hpThetaJensenCellsBatch058Upper
    hpThetaShiftThreeBatch058Neg45WeightLower hpThetaShiftThreeBatch058Neg45WeightUpper hpThetaJensenCellsBatch058_bounds hpThetaShiftThreeBatch058Neg45_weight_bounds
  have hl : (8502671 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch058Lower j * hpThetaShiftThreeBatch058Neg45WeightLower j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftThreeBatch058Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftThreeBatch058Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch058Lower j * hpThetaShiftThreeBatch058Neg45WeightUpper j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftThreeBatch058Neg45WeightUpper j) / 1600) ≤ (550917 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftThreeBatch058Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1160 : ℝ) / 1600 = 58 / 80 by norm_num,
    show ((1160 : ℝ) + 20) / 1600 = (58 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch058Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3218753 / 15625000000 : ℝ)
  | 1 => (-206915293 / 1000000000000 : ℝ)
  | 2 => (-831309 / 4000000000 : ℝ)
  | 3 => (-8349439 / 40000000000 : ℝ)
  | 4 => (-1677131 / 8000000000 : ℝ)
  | 5 => (-164487 / 781250000 : ℝ)
  | 6 => (-211441837 / 1000000000000 : ℝ)
  | 7 => (-212336713 / 1000000000000 : ℝ)
  | 8 => (-42645579 / 200000000000 : ℝ)
  | 9 => (-107057643 / 500000000000 : ℝ)
  | 10 => (-214998793 / 1000000000000 : ℝ)
  | 11 => (-215878319 / 1000000000000 : ℝ)
  | 12 => (-108376883 / 500000000000 : ℝ)
  | 13 => (-108812519 / 500000000000 : ℝ)
  | 14 => (-43698407 / 200000000000 : ℝ)
  | 15 => (-109677329 / 500000000000 : ℝ)
  | 16 => (-220212807 / 1000000000000 : ℝ)
  | 17 => (-11053319 / 50000000000 : ℝ)
  | 18 => (-221915277 / 1000000000000 : ℝ)
  | 19 => (-111379697 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch058Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-205082037 / 1000000000000 : ℝ)
  | 1 => (-206000191 / 1000000000000 : ℝ)
  | 2 => (-51728823 / 250000000000 : ℝ)
  | 3 => (-207827249 / 1000000000000 : ℝ)
  | 4 => (-104367987 / 500000000000 : ℝ)
  | 5 => (-104820687 / 500000000000 : ℝ)
  | 6 => (-210543359 / 1000000000000 : ℝ)
  | 7 => (-52860459 / 250000000000 : ℝ)
  | 8 => (-26542089 / 125000000000 : ℝ)
  | 9 => (-106613947 / 500000000000 : ℝ)
  | 10 => (-42823057 / 200000000000 : ℝ)
  | 11 => (-26874849 / 125000000000 : ℝ)
  | 12 => (-107939159 / 500000000000 : ℝ)
  | 13 => (-43350753 / 200000000000 : ℝ)
  | 14 => (-217625037 / 1000000000000 : ℝ)
  | 15 => (-109246017 / 500000000000 : ℝ)
  | 16 => (-219354657 / 1000000000000 : ℝ)
  | 17 => (-110106403 / 500000000000 : ℝ)
  | 18 => (-221066379 / 1000000000000 : ℝ)
  | 19 => (-55478819 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch058Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1160 : ℝ) + (j.val : ℝ)) / 1600)
      (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch058Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch058Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1160 : ℝ) + (j.val : ℝ)) / 1600)
    (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch058Neg25WeightLower j.val) (hpThetaShiftThreeBatch058Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch058Neg25WeightLower, hpThetaShiftThreeBatch058Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch058Neg25_integral_bounds :
    (-6609087 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-1608749 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch058Lower hpThetaJensenCellsBatch058Upper
    hpThetaShiftThreeBatch058Neg25WeightLower hpThetaShiftThreeBatch058Neg25WeightUpper hpThetaJensenCellsBatch058_bounds hpThetaShiftThreeBatch058Neg25_weight_bounds
  have hl : (-6609087 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch058Lower j * hpThetaShiftThreeBatch058Neg25WeightLower j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftThreeBatch058Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftThreeBatch058Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch058Lower j * hpThetaShiftThreeBatch058Neg25WeightUpper j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftThreeBatch058Neg25WeightUpper j) / 1600) ≤ (-1608749 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftThreeBatch058Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1160 : ℝ) / 1600 = 58 / 80 by norm_num,
    show ((1160 : ℝ) + 20) / 1600 = (58 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch058Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch058Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch058Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch058Neg25_integral_bounds
end HodgeProofHP
