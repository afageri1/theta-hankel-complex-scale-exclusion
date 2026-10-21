/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch046

/-! Exact signed weight and batch integral certificates, batch 46 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch046Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (61677843 / 500000000000 : ℝ)
  | 1 => (123747399 / 1000000000000 : ℝ)
  | 2 => (124118581 / 1000000000000 : ℝ)
  | 3 => (124468639 / 1000000000000 : ℝ)
  | 4 => (124796969 / 1000000000000 : ℝ)
  | 5 => (62551479 / 500000000000 : ℝ)
  | 6 => (62692991 / 500000000000 : ℝ)
  | 7 => (25129081 / 200000000000 : ℝ)
  | 8 => (62940291 / 500000000000 : ℝ)
  | 9 => (63045429 / 500000000000 : ℝ)
  | 10 => (63137783 / 500000000000 : ℝ)
  | 11 => (31608507 / 250000000000 : ℝ)
  | 12 => (63282777 / 500000000000 : ℝ)
  | 13 => (31667361 / 250000000000 : ℝ)
  | 14 => (126744987 / 1000000000000 : ℝ)
  | 15 => (126791459 / 1000000000000 : ℝ)
  | 16 => (49529 / 390625000 : ℝ)
  | 17 => (63374521 / 500000000000 : ℝ)
  | 18 => (126671761 / 1000000000000 : ℝ)
  | 19 => (25312323 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch046Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (618737 / 5000000000 : ℝ)
  | 1 => (62059291 / 500000000000 : ℝ)
  | 2 => (777929 / 6250000000 : ℝ)
  | 3 => (12479697 / 100000000000 : ℝ)
  | 4 => (125102959 / 1000000000000 : ℝ)
  | 5 => (125385983 / 1000000000000 : ℝ)
  | 6 => (62822703 / 500000000000 : ℝ)
  | 7 => (125880583 / 1000000000000 : ℝ)
  | 8 => (126090859 / 1000000000000 : ℝ)
  | 9 => (126275567 / 1000000000000 : ℝ)
  | 10 => (126434029 / 1000000000000 : ℝ)
  | 11 => (25313111 / 200000000000 : ℝ)
  | 12 => (25333889 / 200000000000 : ℝ)
  | 13 => (31686247 / 250000000000 : ℝ)
  | 14 => (6339573 / 50000000000 : ℝ)
  | 15 => (126808127 / 1000000000000 : ℝ)
  | 16 => (126808253 / 1000000000000 : ℝ)
  | 17 => (126794241 / 1000000000000 : ℝ)
  | 18 => (126749043 / 1000000000000 : ℝ)
  | 19 => (63335881 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch046Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((920 : ℝ) + (j.val : ℝ)) / 1600)
      (((920 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch046Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch046Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((920 : ℝ) + (j.val : ℝ)) / 1600)
    (((920 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch046Neg100WeightLower j.val) (hpThetaShiftThreeBatch046Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch046Neg100WeightLower, hpThetaShiftThreeBatch046Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch046Neg100_integral_bounds :
    (62130399 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (3960569 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (920 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch046Lower hpThetaJensenCellsBatch046Upper
    hpThetaShiftThreeBatch046Neg100WeightLower hpThetaShiftThreeBatch046Neg100WeightUpper hpThetaJensenCellsBatch046_bounds hpThetaShiftThreeBatch046Neg100_weight_bounds
  have hl : (62130399 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch046Lower j * hpThetaShiftThreeBatch046Neg100WeightLower j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftThreeBatch046Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftThreeBatch046Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch046Lower j * hpThetaShiftThreeBatch046Neg100WeightUpper j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftThreeBatch046Neg100WeightUpper j) / 1600) ≤ (3960569 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftThreeBatch046Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (920 : ℝ) / 1600 = 46 / 80 by norm_num,
    show ((920 : ℝ) + 20) / 1600 = (46 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch046Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3410457 / 62500000000 : ℝ)
  | 1 => (55639559 / 1000000000000 : ℝ)
  | 2 => (14180719 / 250000000000 : ℝ)
  | 3 => (57817299 / 1000000000000 : ℝ)
  | 4 => (2946143 / 50000000000 : ℝ)
  | 5 => (7504949 / 125000000000 : ℝ)
  | 6 => (30583763 / 500000000000 : ℝ)
  | 7 => (62306693 / 1000000000000 : ℝ)
  | 8 => (396607 / 6250000000 : ℝ)
  | 9 => (64618837 / 1000000000000 : ℝ)
  | 10 => (65791869 / 1000000000000 : ℝ)
  | 11 => (33488121 / 500000000000 : ℝ)
  | 12 => (3408599 / 50000000000 : ℝ)
  | 13 => (69379107 / 1000000000000 : ℝ)
  | 14 => (35298821 / 500000000000 : ℝ)
  | 15 => (71827607 / 1000000000000 : ℝ)
  | 16 => (3653451 / 50000000000 : ℝ)
  | 17 => (74321899 / 1000000000000 : ℝ)
  | 18 => (3779313 / 50000000000 : ℝ)
  | 19 => (19215529 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch046Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1390989 / 25000000000 : ℝ)
  | 1 => (56722877 / 1000000000000 : ℝ)
  | 2 => (578173 / 10000000000 : ℝ)
  | 3 => (58922861 / 1000000000000 : ℝ)
  | 4 => (60039593 / 1000000000000 : ℝ)
  | 5 => (61167527 / 1000000000000 : ℝ)
  | 6 => (31153347 / 500000000000 : ℝ)
  | 7 => (63457121 / 1000000000000 : ℝ)
  | 8 => (32309419 / 500000000000 : ℝ)
  | 9 => (6579187 / 100000000000 : ℝ)
  | 10 => (66976243 / 1000000000000 : ℝ)
  | 11 => (68171981 / 1000000000000 : ℝ)
  | 12 => (17344777 / 250000000000 : ℝ)
  | 13 => (70597643 / 1000000000000 : ℝ)
  | 14 => (8978451 / 125000000000 : ℝ)
  | 15 => (73069021 / 1000000000000 : ℝ)
  | 16 => (743219 / 10000000000 : ℝ)
  | 17 => (75586261 / 1000000000000 : ℝ)
  | 18 => (76862117 / 1000000000000 : ℝ)
  | 19 => (39074741 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch046Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((920 : ℝ) + (j.val : ℝ)) / 1600)
      (((920 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch046Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch046Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((920 : ℝ) + (j.val : ℝ)) / 1600)
    (((920 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch046Neg70WeightLower j.val) (hpThetaShiftThreeBatch046Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch046Neg70WeightLower, hpThetaShiftThreeBatch046Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch046Neg70_integral_bounds :
    (8035381 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (1041393 / 31250000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (920 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch046Lower hpThetaJensenCellsBatch046Upper
    hpThetaShiftThreeBatch046Neg70WeightLower hpThetaShiftThreeBatch046Neg70WeightUpper hpThetaJensenCellsBatch046_bounds hpThetaShiftThreeBatch046Neg70_weight_bounds
  have hl : (8035381 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch046Lower j * hpThetaShiftThreeBatch046Neg70WeightLower j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftThreeBatch046Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftThreeBatch046Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch046Lower j * hpThetaShiftThreeBatch046Neg70WeightUpper j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftThreeBatch046Neg70WeightUpper j) / 1600) ≤ (1041393 / 31250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftThreeBatch046Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (920 : ℝ) / 1600 = 46 / 80 by norm_num,
    show ((920 : ℝ) + 20) / 1600 = (46 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch046Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-44362611 / 1000000000000 : ℝ)
  | 1 => (-44449309 / 1000000000000 : ℝ)
  | 2 => (-11133061 / 250000000000 : ℝ)
  | 3 => (-22305677 / 500000000000 : ℝ)
  | 4 => (-11171643 / 250000000000 : ℝ)
  | 5 => (-22378917 / 500000000000 : ℝ)
  | 6 => (-11206269 / 250000000000 : ℝ)
  | 7 => (-4488823 / 100000000000 : ℝ)
  | 8 => (-4494723 / 100000000000 : ℝ)
  | 9 => (-45002009 / 1000000000000 : ℝ)
  | 10 => (-45052499 / 1000000000000 : ℝ)
  | 11 => (-45098633 / 1000000000000 : ℝ)
  | 12 => (-22570171 / 500000000000 : ℝ)
  | 13 => (-11294389 / 250000000000 : ℝ)
  | 14 => (-9042041 / 200000000000 : ℝ)
  | 15 => (-2261911 / 50000000000 : ℝ)
  | 16 => (-4526153 / 100000000000 : ℝ)
  | 17 => (-707501 / 15625000000 : ℝ)
  | 18 => (-11323437 / 250000000000 : ℝ)
  | 19 => (-2831407 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch046Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-22136107 / 500000000000 : ℝ)
  | 1 => (-4436261 / 100000000000 : ℝ)
  | 2 => (-11112327 / 250000000000 : ℝ)
  | 3 => (-44532243 / 1000000000000 : ℝ)
  | 4 => (-44611353 / 1000000000000 : ℝ)
  | 5 => (-44686571 / 1000000000000 : ℝ)
  | 6 => (-44757833 / 1000000000000 : ℝ)
  | 7 => (-1793003 / 40000000000 : ℝ)
  | 8 => (-44888229 / 1000000000000 : ℝ)
  | 9 => (-44947229 / 1000000000000 : ℝ)
  | 10 => (-5625251 / 125000000000 : ℝ)
  | 11 => (-22526249 / 500000000000 : ℝ)
  | 12 => (-5637329 / 125000000000 : ℝ)
  | 13 => (-45140341 / 1000000000000 : ℝ)
  | 14 => (-9035511 / 200000000000 : ℝ)
  | 15 => (-11302551 / 250000000000 : ℝ)
  | 16 => (-45238219 / 1000000000000 : ℝ)
  | 17 => (-45261529 / 1000000000000 : ℝ)
  | 18 => (-45280063 / 1000000000000 : ℝ)
  | 19 => (-45293747 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch046Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((920 : ℝ) + (j.val : ℝ)) / 1600)
      (((920 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch046Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch046Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((920 : ℝ) + (j.val : ℝ)) / 1600)
    (((920 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch046Neg45WeightLower j.val) (hpThetaShiftThreeBatch046Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch046Neg45WeightLower, hpThetaShiftThreeBatch046Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch046Neg45_integral_bounds :
    (-11311783 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-5547239 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (920 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch046Lower hpThetaJensenCellsBatch046Upper
    hpThetaShiftThreeBatch046Neg45WeightLower hpThetaShiftThreeBatch046Neg45WeightUpper hpThetaJensenCellsBatch046_bounds hpThetaShiftThreeBatch046Neg45_weight_bounds
  have hl : (-11311783 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch046Lower j * hpThetaShiftThreeBatch046Neg45WeightLower j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftThreeBatch046Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftThreeBatch046Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch046Lower j * hpThetaShiftThreeBatch046Neg45WeightUpper j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftThreeBatch046Neg45WeightUpper j) / 1600) ≤ (-5547239 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftThreeBatch046Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (920 : ℝ) / 1600 = 46 / 80 by norm_num,
    show ((920 : ℝ) + 20) / 1600 = (46 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch046Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-35941 / 1953125000 : ℝ)
  | 1 => (-18818853 / 1000000000000 : ℝ)
  | 2 => (-2404911 / 125000000000 : ℝ)
  | 3 => (-19663107 / 1000000000000 : ℝ)
  | 4 => (-10045159 / 500000000000 : ℝ)
  | 5 => (-20520931 / 1000000000000 : ℝ)
  | 6 => (-10477477 / 500000000000 : ℝ)
  | 7 => (-4278479 / 200000000000 : ℝ)
  | 8 => (-21833263 / 1000000000000 : ℝ)
  | 9 => (-4455513 / 200000000000 : ℝ)
  | 10 => (-22725311 / 1000000000000 : ℝ)
  | 11 => (-5794127 / 250000000000 : ℝ)
  | 12 => (-5907791 / 250000000000 : ℝ)
  | 13 => (-12044643 / 500000000000 : ℝ)
  | 14 => (-24550883 / 1000000000000 : ℝ)
  | 15 => (-25015961 / 1000000000000 : ℝ)
  | 16 => (-1592783 / 62500000000 : ℝ)
  | 17 => (-25956591 / 1000000000000 : ℝ)
  | 18 => (-26432157 / 1000000000000 : ℝ)
  | 19 => (-52561 / 1953125000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch046Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-35133 / 1953125000 : ℝ)
  | 1 => (-18401791 / 1000000000000 : ℝ)
  | 2 => (-4704713 / 250000000000 : ℝ)
  | 3 => (-19239287 / 1000000000000 : ℝ)
  | 4 => (-9831553 / 500000000000 : ℝ)
  | 5 => (-20090317 / 1000000000000 : ℝ)
  | 6 => (-2052093 / 100000000000 : ℝ)
  | 7 => (-20954953 / 1000000000000 : ℝ)
  | 8 => (-10696197 / 500000000000 : ℝ)
  | 9 => (-10916631 / 500000000000 : ℝ)
  | 10 => (-5569391 / 250000000000 : ℝ)
  | 11 => (-2272531 / 100000000000 : ℝ)
  | 12 => (-23176507 / 1000000000000 : ℝ)
  | 13 => (-23631163 / 1000000000000 : ℝ)
  | 14 => (-4817857 / 200000000000 : ℝ)
  | 15 => (-12275441 / 500000000000 : ℝ)
  | 16 => (-625399 / 25000000000 : ℝ)
  | 17 => (-25484527 / 1000000000000 : ℝ)
  | 18 => (-2595659 / 100000000000 : ℝ)
  | 19 => (-6608039 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch046Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((920 : ℝ) + (j.val : ℝ)) / 1600)
      (((920 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch046Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch046Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((920 : ℝ) + (j.val : ℝ)) / 1600)
    (((920 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch046Neg25WeightLower j.val) (hpThetaShiftThreeBatch046Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch046Neg25WeightLower, hpThetaShiftThreeBatch046Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch046Neg25_integral_bounds :
    (-2256991 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-10861087 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (920 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch046Lower hpThetaJensenCellsBatch046Upper
    hpThetaShiftThreeBatch046Neg25WeightLower hpThetaShiftThreeBatch046Neg25WeightUpper hpThetaJensenCellsBatch046_bounds hpThetaShiftThreeBatch046Neg25_weight_bounds
  have hl : (-2256991 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch046Lower j * hpThetaShiftThreeBatch046Neg25WeightLower j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftThreeBatch046Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftThreeBatch046Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch046Lower j * hpThetaShiftThreeBatch046Neg25WeightUpper j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftThreeBatch046Neg25WeightUpper j) / 1600) ≤ (-10861087 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftThreeBatch046Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (920 : ℝ) / 1600 = 46 / 80 by norm_num,
    show ((920 : ℝ) + 20) / 1600 = (46 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch046Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch046Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch046Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch046Neg25_integral_bounds
end HodgeProofHP
