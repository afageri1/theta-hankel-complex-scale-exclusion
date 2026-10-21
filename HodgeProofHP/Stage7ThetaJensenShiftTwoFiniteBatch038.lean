/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch038

/-! Exact signed weight and batch integral certificates, batch 38 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch038Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2468778723 / 1000000000000 : ℝ)
  | 1 => (1248577403 / 500000000000 : ℝ)
  | 2 => (505119501 / 200000000000 : ℝ)
  | 3 => (2554102773 / 1000000000000 : ℝ)
  | 4 => (322833309 / 125000000000 : ℝ)
  | 5 => (261128437 / 100000000000 : ℝ)
  | 6 => (2639952141 / 1000000000000 : ℝ)
  | 7 => (2668665363 / 1000000000000 : ℝ)
  | 8 => (2697419517 / 1000000000000 : ℝ)
  | 9 => (1363104993 / 500000000000 : ℝ)
  | 10 => (1377516027 / 500000000000 : ℝ)
  | 11 => (2783880903 / 1000000000000 : ℝ)
  | 12 => (10987311 / 3906250000 : ℝ)
  | 13 => (2841639169 / 1000000000000 : ℝ)
  | 14 => (2870538437 / 1000000000000 : ℝ)
  | 15 => (2899444187 / 1000000000000 : ℝ)
  | 16 => (2928351079 / 1000000000000 : ℝ)
  | 17 => (2957253667 / 1000000000000 : ℝ)
  | 18 => (373268299 / 125000000000 : ℝ)
  | 19 => (1507511793 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch038Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2497154807 / 1000000000000 : ℝ)
  | 1 => (1262798753 / 500000000000 : ℝ)
  | 2 => (1277051387 / 500000000000 : ℝ)
  | 3 => (2582666473 / 1000000000000 : ℝ)
  | 4 => (2611284371 / 1000000000000 : ℝ)
  | 5 => (1319976071 / 500000000000 : ℝ)
  | 6 => (667166341 / 250000000000 : ℝ)
  | 7 => (1348709759 / 500000000000 : ℝ)
  | 8 => (2726209987 / 1000000000000 : ℝ)
  | 9 => (551006411 / 200000000000 : ℝ)
  | 10 => (347985113 / 125000000000 : ℝ)
  | 11 => (2812751617 / 1000000000000 : ℝ)
  | 12 => (284163917 / 100000000000 : ℝ)
  | 13 => (1435269219 / 500000000000 : ℝ)
  | 14 => (724861047 / 250000000000 : ℝ)
  | 15 => (73208777 / 25000000000 : ℝ)
  | 16 => (739313417 / 250000000000 : ℝ)
  | 17 => (2986146393 / 1000000000000 : ℝ)
  | 18 => (3015023587 / 1000000000000 : ℝ)
  | 19 => (304387947 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch038Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((760 : ℝ) + (j.val : ℝ)) / 1600)
      (((760 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch038Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch038Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((760 : ℝ) + (j.val : ℝ)) / 1600)
    (((760 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch038Neg100WeightLower j.val) (hpThetaShiftTwoBatch038Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch038Neg100WeightLower, hpThetaShiftTwoBatch038Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch038Neg100_integral_bounds :
    (1280173159 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (262901749 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (760 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch038Lower hpThetaJensenCellsBatch038Upper
    hpThetaShiftTwoBatch038Neg100WeightLower hpThetaShiftTwoBatch038Neg100WeightUpper hpThetaJensenCellsBatch038_bounds hpThetaShiftTwoBatch038Neg100_weight_bounds
  have hl : (1280173159 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch038Lower j * hpThetaShiftTwoBatch038Neg100WeightLower j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftTwoBatch038Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftTwoBatch038Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch038Lower j * hpThetaShiftTwoBatch038Neg100WeightUpper j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftTwoBatch038Neg100WeightUpper j) / 1600) ≤ (262901749 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftTwoBatch038Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (760 : ℝ) / 1600 = 38 / 80 by norm_num,
    show ((760 : ℝ) + 20) / 1600 = (38 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch038Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-180383961 / 1000000000000 : ℝ)
  | 1 => (-84686619 / 500000000000 : ℝ)
  | 2 => (-158174191 / 1000000000000 : ℝ)
  | 3 => (-146785437 / 1000000000000 : ℝ)
  | 4 => (-135205593 / 1000000000000 : ℝ)
  | 5 => (-61716641 / 500000000000 : ℝ)
  | 6 => (-55733563 / 500000000000 : ℝ)
  | 7 => (-99305751 / 1000000000000 : ℝ)
  | 8 => (-43473893 / 500000000000 : ℝ)
  | 9 => (-74391861 / 1000000000000 : ℝ)
  | 10 => (-61636611 / 1000000000000 : ℝ)
  | 11 => (-48680673 / 1000000000000 : ℝ)
  | 12 => (-277521 / 7812500000 : ℝ)
  | 13 => (-221613 / 10000000000 : ℝ)
  | 14 => (-4297579 / 500000000000 : ℝ)
  | 15 => (5177087 / 1000000000000 : ℝ)
  | 16 => (9578389 / 500000000000 : ℝ)
  | 17 => (6669051 / 200000000000 : ℝ)
  | 18 => (11935963 / 250000000000 : ℝ)
  | 19 => (623539 / 10000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch038Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-169373237 / 1000000000000 : ℝ)
  | 1 => (-15817419 / 100000000000 : ℝ)
  | 2 => (-36696359 / 250000000000 : ℝ)
  | 3 => (-16900699 / 125000000000 : ℝ)
  | 4 => (-123433281 / 1000000000000 : ℝ)
  | 5 => (-891737 / 8000000000 : ℝ)
  | 6 => (-397223 / 4000000000 : ℝ)
  | 7 => (-17389557 / 200000000000 : ℝ)
  | 8 => (-3719593 / 50000000000 : ℝ)
  | 9 => (-6163661 / 100000000000 : ℝ)
  | 10 => (-1521271 / 31250000000 : ℝ)
  | 11 => (-35522687 / 1000000000000 : ℝ)
  | 12 => (-22161299 / 1000000000000 : ℝ)
  | 13 => (-8595157 / 1000000000000 : ℝ)
  | 14 => (20223 / 3906250000 : ℝ)
  | 15 => (19156779 / 1000000000000 : ℝ)
  | 16 => (4168157 / 125000000000 : ℝ)
  | 17 => (47743853 / 1000000000000 : ℝ)
  | 18 => (62353901 / 1000000000000 : ℝ)
  | 19 => (19294181 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch038Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((760 : ℝ) + (j.val : ℝ)) / 1600)
      (((760 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch038Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch038Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((760 : ℝ) + (j.val : ℝ)) / 1600)
    (((760 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch038Neg65WeightLower j.val) (hpThetaShiftTwoBatch038Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch038Neg65WeightLower, hpThetaShiftTwoBatch038Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch038Neg65_integral_bounds :
    (-64596109 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-20507037 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (760 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch038Lower hpThetaJensenCellsBatch038Upper
    hpThetaShiftTwoBatch038Neg65WeightLower hpThetaShiftTwoBatch038Neg65WeightUpper hpThetaJensenCellsBatch038_bounds hpThetaShiftTwoBatch038Neg65_weight_bounds
  have hl : (-64596109 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch038Lower j * hpThetaShiftTwoBatch038Neg65WeightLower j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftTwoBatch038Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftTwoBatch038Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch038Lower j * hpThetaShiftTwoBatch038Neg65WeightUpper j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftTwoBatch038Neg65WeightUpper j) / 1600) ≤ (-20507037 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftTwoBatch038Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (760 : ℝ) / 1600 = 38 / 80 by norm_num,
    show ((760 : ℝ) + 20) / 1600 = (38 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch038Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1074461737 / 1000000000000 : ℝ)
  | 1 => (-539305053 / 500000000000 : ℝ)
  | 2 => (-1082705489 / 1000000000000 : ℝ)
  | 3 => (-543373443 / 500000000000 : ℝ)
  | 4 => (-109073329 / 100000000000 : ℝ)
  | 5 => (-1094663687 / 1000000000000 : ℝ)
  | 6 => (-1098537057 / 1000000000000 : ℝ)
  | 7 => (-1102352373 / 1000000000000 : ℝ)
  | 8 => (-1106108599 / 1000000000000 : ℝ)
  | 9 => (-554902347 / 500000000000 : ℝ)
  | 10 => (-1113439611 / 1000000000000 : ℝ)
  | 11 => (-1117012293 / 1000000000000 : ℝ)
  | 12 => (-1120521679 / 1000000000000 : ℝ)
  | 13 => (-1123966699 / 1000000000000 : ℝ)
  | 14 => (-1127346277 / 1000000000000 : ℝ)
  | 15 => (-1130659331 / 1000000000000 : ℝ)
  | 16 => (-113390477 / 100000000000 : ℝ)
  | 17 => (-1137081499 / 1000000000000 : ℝ)
  | 18 => (-285047103 / 250000000000 : ℝ)
  | 19 => (-2858061 / 2500000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch038Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-535130687 / 500000000000 : ℝ)
  | 1 => (-134307717 / 125000000000 : ℝ)
  | 2 => (-215722021 / 200000000000 : ℝ)
  | 3 => (-67669093 / 62500000000 : ℝ)
  | 4 => (-217349377 / 200000000000 : ℝ)
  | 5 => (-1090733289 / 1000000000000 : ℝ)
  | 6 => (-547331843 / 500000000000 : ℝ)
  | 7 => (-34329283 / 31250000000 : ℝ)
  | 8 => (-275588093 / 250000000000 : ℝ)
  | 9 => (-553054299 / 500000000000 : ℝ)
  | 10 => (-1109804693 / 1000000000000 : ℝ)
  | 11 => (-111343961 / 100000000000 : ℝ)
  | 12 => (-279253073 / 250000000000 : ℝ)
  | 13 => (-560260839 / 500000000000 : ℝ)
  | 14 => (-561983349 / 500000000000 : ℝ)
  | 15 => (-281836569 / 250000000000 : ℝ)
  | 16 => (-113065933 / 100000000000 : ℝ)
  | 17 => (-1133904769 / 1000000000000 : ℝ)
  | 18 => (-568540749 / 500000000000 : ℝ)
  | 19 => (-1140188411 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch038Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((760 : ℝ) + (j.val : ℝ)) / 1600)
      (((760 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch038Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch038Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((760 : ℝ) + (j.val : ℝ)) / 1600)
    (((760 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch038Neg45WeightLower j.val) (hpThetaShiftTwoBatch038Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch038Neg45WeightLower, hpThetaShiftTwoBatch038Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch038Neg45_integral_bounds :
    (-1055934599 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-1035738881 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (760 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch038Lower hpThetaJensenCellsBatch038Upper
    hpThetaShiftTwoBatch038Neg45WeightLower hpThetaShiftTwoBatch038Neg45WeightUpper hpThetaJensenCellsBatch038_bounds hpThetaShiftTwoBatch038Neg45_weight_bounds
  have hl : (-1055934599 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch038Lower j * hpThetaShiftTwoBatch038Neg45WeightLower j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftTwoBatch038Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftTwoBatch038Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch038Lower j * hpThetaShiftTwoBatch038Neg45WeightUpper j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftTwoBatch038Neg45WeightUpper j) / 1600) ≤ (-1035738881 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftTwoBatch038Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (760 : ℝ) / 1600 = 38 / 80 by norm_num,
    show ((760 : ℝ) + 20) / 1600 = (38 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch038Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-354146319 / 1000000000000 : ℝ)
  | 1 => (-1414451 / 3906250000 : ℝ)
  | 2 => (-370103989 / 1000000000000 : ℝ)
  | 3 => (-378159923 / 1000000000000 : ℝ)
  | 4 => (-19313363 / 50000000000 : ℝ)
  | 5 => (-197213001 / 500000000000 : ℝ)
  | 6 => (-402636147 / 1000000000000 : ℝ)
  | 7 => (-51362211 / 125000000000 : ℝ)
  | 8 => (-419210619 / 1000000000000 : ℝ)
  | 9 => (-42757493 / 100000000000 : ℝ)
  | 10 => (-435990607 / 1000000000000 : ℝ)
  | 11 => (-222228817 / 500000000000 : ℝ)
  | 12 => (-452975993 / 1000000000000 : ℝ)
  | 13 => (-230772831 / 500000000000 : ℝ)
  | 14 => (-235083309 / 500000000000 : ℝ)
  | 15 => (-478838833 / 1000000000000 : ℝ)
  | 16 => (-121890569 / 250000000000 : ℝ)
  | 17 => (-124084229 / 250000000000 : ℝ)
  | 18 => (-126290679 / 250000000000 : ℝ)
  | 19 => (-514039639 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch038Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-346244567 / 1000000000000 : ℝ)
  | 1 => (-177073159 / 500000000000 : ℝ)
  | 2 => (-72419891 / 200000000000 : ℝ)
  | 3 => (-92525997 / 250000000000 : ℝ)
  | 4 => (-189079961 / 500000000000 : ℝ)
  | 5 => (-386267259 / 1000000000000 : ℝ)
  | 6 => (-394426001 / 1000000000000 : ℝ)
  | 7 => (-201318073 / 500000000000 : ℝ)
  | 8 => (-410897687 / 1000000000000 : ℝ)
  | 9 => (-209605309 / 500000000000 : ℝ)
  | 10 => (-427574929 / 1000000000000 : ℝ)
  | 11 => (-217995303 / 500000000000 : ℝ)
  | 12 => (-444457633 / 1000000000000 : ℝ)
  | 13 => (-56621999 / 125000000000 : ℝ)
  | 14 => (-461545661 / 1000000000000 : ℝ)
  | 15 => (-470166617 / 1000000000000 : ℝ)
  | 16 => (-29927427 / 62500000000 : ℝ)
  | 17 => (-19502491 / 40000000000 : ℝ)
  | 18 => (-99267383 / 200000000000 : ℝ)
  | 19 => (-101032543 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch038Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((760 : ℝ) + (j.val : ℝ)) / 1600)
      (((760 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch038Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch038Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((760 : ℝ) + (j.val : ℝ)) / 1600)
    (((760 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch038Neg25WeightLower j.val) (hpThetaShiftTwoBatch038Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch038Neg25WeightLower, hpThetaShiftTwoBatch038Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch038Neg25_integral_bounds :
    (-819486983 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-49423779 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (760 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch038Lower hpThetaJensenCellsBatch038Upper
    hpThetaShiftTwoBatch038Neg25WeightLower hpThetaShiftTwoBatch038Neg25WeightUpper hpThetaJensenCellsBatch038_bounds hpThetaShiftTwoBatch038Neg25_weight_bounds
  have hl : (-819486983 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch038Lower j * hpThetaShiftTwoBatch038Neg25WeightLower j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftTwoBatch038Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftTwoBatch038Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch038Lower j * hpThetaShiftTwoBatch038Neg25WeightUpper j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftTwoBatch038Neg25WeightUpper j) / 1600) ≤ (-49423779 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftTwoBatch038Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (760 : ℝ) / 1600 = 38 / 80 by norm_num,
    show ((760 : ℝ) + 20) / 1600 = (38 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch038Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch038Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch038Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch038Neg25_integral_bounds
end HodgeProofHP
