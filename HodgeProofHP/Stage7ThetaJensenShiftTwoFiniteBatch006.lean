/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch006

/-! Exact signed weight and batch integral certificates, batch 6 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch006Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2209463 / 1000000000000 : ℝ)
  | 1 => (2276953 / 1000000000000 : ℝ)
  | 2 => (36653 / 15625000000 : ℝ)
  | 3 => (1207993 / 500000000000 : ℝ)
  | 4 => (310943 / 125000000000 : ℝ)
  | 5 => (640119 / 250000000000 : ℝ)
  | 6 => (2634787 / 1000000000000 : ℝ)
  | 7 => (542097 / 200000000000 : ℝ)
  | 8 => (2787577 / 1000000000000 : ℝ)
  | 9 => (286607 / 100000000000 : ℝ)
  | 10 => (2945969 / 1000000000000 : ℝ)
  | 11 => (37841 / 12500000000 : ℝ)
  | 12 => (3110009 / 1000000000000 : ℝ)
  | 13 => (3194159 / 1000000000000 : ℝ)
  | 14 => (409967 / 125000000000 : ℝ)
  | 15 => (420843 / 125000000000 : ℝ)
  | 16 => (1727593 / 500000000000 : ℝ)
  | 17 => (709013 / 200000000000 : ℝ)
  | 18 => (3636383 / 1000000000000 : ℝ)
  | 19 => (3729143 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch006Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1138477 / 500000000000 : ℝ)
  | 1 => (2345793 / 1000000000000 : ℝ)
  | 2 => (2415987 / 1000000000000 : ℝ)
  | 3 => (497509 / 200000000000 : ℝ)
  | 4 => (2560477 / 1000000000000 : ℝ)
  | 5 => (658697 / 250000000000 : ℝ)
  | 6 => (1355243 / 500000000000 : ℝ)
  | 7 => (1393789 / 500000000000 : ℝ)
  | 8 => (2866071 / 1000000000000 : ℝ)
  | 9 => (294597 / 100000000000 : ℝ)
  | 10 => (3027281 / 1000000000000 : ℝ)
  | 11 => (311001 / 100000000000 : ℝ)
  | 12 => (39927 / 12500000000 : ℝ)
  | 13 => (3279737 / 1000000000000 : ℝ)
  | 14 => (673349 / 200000000000 : ℝ)
  | 15 => (3455187 / 1000000000000 : ℝ)
  | 16 => (1772533 / 500000000000 : ℝ)
  | 17 => (113637 / 31250000000 : ℝ)
  | 18 => (466143 / 125000000000 : ℝ)
  | 19 => (955837 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch006Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((120 : ℝ) + (j.val : ℝ)) / 1600)
      (((120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch006Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch006Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((120 : ℝ) + (j.val : ℝ)) / 1600)
    (((120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch006Neg100WeightLower j.val) (hpThetaShiftTwoBatch006Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch006Neg100WeightLower, hpThetaShiftTwoBatch006Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch006Neg100_integral_bounds :
    (6114967 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (15881201 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch006Lower hpThetaJensenCellsBatch006Upper
    hpThetaShiftTwoBatch006Neg100WeightLower hpThetaShiftTwoBatch006Neg100WeightUpper hpThetaJensenCellsBatch006_bounds hpThetaShiftTwoBatch006Neg100_weight_bounds
  have hl : (6114967 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch006Lower j * hpThetaShiftTwoBatch006Neg100WeightLower j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftTwoBatch006Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftTwoBatch006Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch006Lower j * hpThetaShiftTwoBatch006Neg100WeightUpper j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftTwoBatch006Neg100WeightUpper j) / 1600) ≤ (15881201 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftTwoBatch006Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (120 : ℝ) / 1600 = 6 / 80 by norm_num,
    show ((120 : ℝ) + 20) / 1600 = (6 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch006Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (471001 / 200000000000 : ℝ)
  | 1 => (2429749 / 1000000000000 : ℝ)
  | 2 => (501227 / 200000000000 : ℝ)
  | 3 => (129209 / 50000000000 : ℝ)
  | 4 => (1331951 / 500000000000 : ℝ)
  | 5 => (2745319 / 1000000000000 : ℝ)
  | 6 => (88389 / 31250000000 : ℝ)
  | 7 => (1456653 / 500000000000 : ℝ)
  | 8 => (2999909 / 1000000000000 : ℝ)
  | 9 => (123531 / 40000000000 : ℝ)
  | 10 => (3178421 / 1000000000000 : ℝ)
  | 11 => (1635181 / 500000000000 : ℝ)
  | 12 => (672823 / 200000000000 : ℝ)
  | 13 => (3459697 / 1000000000000 : ℝ)
  | 14 => (3557121 / 1000000000000 : ℝ)
  | 15 => (731281 / 200000000000 : ℝ)
  | 16 => (3757563 / 1000000000000 : ℝ)
  | 17 => (3860611 / 1000000000000 : ℝ)
  | 18 => (3965563 / 1000000000000 : ℝ)
  | 19 => (814487 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch006Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (9719 / 4000000000 : ℝ)
  | 1 => (313267 / 125000000000 : ℝ)
  | 2 => (2584181 / 1000000000000 : ℝ)
  | 3 => (2663903 / 1000000000000 : ℝ)
  | 4 => (68633 / 25000000000 : ℝ)
  | 5 => (2828449 / 1000000000000 : ℝ)
  | 6 => (2913307 / 1000000000000 : ℝ)
  | 7 => (299991 / 100000000000 : ℝ)
  | 8 => (772069 / 250000000000 : ℝ)
  | 9 => (1589211 / 500000000000 : ℝ)
  | 10 => (3270363 / 1000000000000 : ℝ)
  | 11 => (841029 / 250000000000 : ℝ)
  | 12 => (1729849 / 500000000000 : ℝ)
  | 13 => (1778561 / 500000000000 : ℝ)
  | 14 => (1828203 / 500000000000 : ℝ)
  | 15 => (939391 / 250000000000 : ℝ)
  | 16 => (965153 / 250000000000 : ℝ)
  | 17 => (991391 / 250000000000 : ℝ)
  | 18 => (1018109 / 250000000000 : ℝ)
  | 19 => (104531 / 25000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch006Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((120 : ℝ) + (j.val : ℝ)) / 1600)
      (((120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch006Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch006Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((120 : ℝ) + (j.val : ℝ)) / 1600)
    (((120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch006Neg65WeightLower j.val) (hpThetaShiftTwoBatch006Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch006Neg65WeightLower, hpThetaShiftTwoBatch006Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch006Neg65_integral_bounds :
    (13204653 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (68675949 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch006Lower hpThetaJensenCellsBatch006Upper
    hpThetaShiftTwoBatch006Neg65WeightLower hpThetaShiftTwoBatch006Neg65WeightUpper hpThetaJensenCellsBatch006_bounds hpThetaShiftTwoBatch006Neg65_weight_bounds
  have hl : (13204653 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch006Lower j * hpThetaShiftTwoBatch006Neg65WeightLower j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftTwoBatch006Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftTwoBatch006Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch006Lower j * hpThetaShiftTwoBatch006Neg65WeightUpper j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftTwoBatch006Neg65WeightUpper j) / 1600) ≤ (68675949 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftTwoBatch006Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (120 : ℝ) / 1600 = 6 / 80 by norm_num,
    show ((120 : ℝ) + 20) / 1600 = (6 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch006Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (76253 / 31250000000 : ℝ)
  | 1 => (629779 / 250000000000 : ℝ)
  | 2 => (1299977 / 500000000000 : ℝ)
  | 3 => (335329 / 125000000000 : ℝ)
  | 4 => (110687 / 40000000000 : ℝ)
  | 5 => (570721 / 200000000000 : ℝ)
  | 6 => (2941947 / 1000000000000 : ℝ)
  | 7 => (1516111 / 500000000000 : ℝ)
  | 8 => (624891 / 200000000000 : ℝ)
  | 9 => (3218669 / 1000000000000 : ℝ)
  | 10 => (1657443 / 500000000000 : ℝ)
  | 11 => (341313 / 100000000000 : ℝ)
  | 12 => (3513423 / 1000000000000 : ℝ)
  | 13 => (361579 / 100000000000 : ℝ)
  | 14 => (3720251 / 1000000000000 : ℝ)
  | 15 => (3826831 / 1000000000000 : ℝ)
  | 16 => (3935553 / 1000000000000 : ℝ)
  | 17 => (4046437 / 1000000000000 : ℝ)
  | 18 => (1039877 / 250000000000 : ℝ)
  | 19 => (4274787 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch006Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2519117 / 1000000000000 : ℝ)
  | 1 => (519991 / 200000000000 : ℝ)
  | 2 => (2682633 / 1000000000000 : ℝ)
  | 3 => (345897 / 125000000000 : ℝ)
  | 4 => (1426803 / 500000000000 : ℝ)
  | 5 => (735487 / 250000000000 : ℝ)
  | 6 => (3032223 / 1000000000000 : ℝ)
  | 7 => (390557 / 125000000000 : ℝ)
  | 8 => (321867 / 100000000000 : ℝ)
  | 9 => (3314887 / 1000000000000 : ℝ)
  | 10 => (3413131 / 1000000000000 : ℝ)
  | 11 => (219589 / 62500000000 : ℝ)
  | 12 => (3615791 / 1000000000000 : ℝ)
  | 13 => (930063 / 250000000000 : ℝ)
  | 14 => (239177 / 62500000000 : ℝ)
  | 15 => (1967777 / 500000000000 : ℝ)
  | 16 => (2023219 / 500000000000 : ℝ)
  | 17 => (4159509 / 1000000000000 : ℝ)
  | 18 => (1068697 / 250000000000 : ℝ)
  | 19 => (4392299 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch006Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((120 : ℝ) + (j.val : ℝ)) / 1600)
      (((120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch006Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch006Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((120 : ℝ) + (j.val : ℝ)) / 1600)
    (((120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch006Neg45WeightLower j.val) (hpThetaShiftTwoBatch006Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch006Neg45WeightLower, hpThetaShiftTwoBatch006Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch006Neg45_integral_bounds :
    (68885749 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (71702761 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch006Lower hpThetaJensenCellsBatch006Upper
    hpThetaShiftTwoBatch006Neg45WeightLower hpThetaShiftTwoBatch006Neg45WeightUpper hpThetaJensenCellsBatch006_bounds hpThetaShiftTwoBatch006Neg45_weight_bounds
  have hl : (68885749 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch006Lower j * hpThetaShiftTwoBatch006Neg45WeightLower j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftTwoBatch006Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftTwoBatch006Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch006Lower j * hpThetaShiftTwoBatch006Neg45WeightUpper j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftTwoBatch006Neg45WeightUpper j) / 1600) ≤ (71702761 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftTwoBatch006Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (120 : ℝ) / 1600 = 6 / 80 by norm_num,
    show ((120 : ℝ) + 20) / 1600 = (6 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch006Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (631649 / 250000000000 : ℝ)
  | 1 => (2609989 / 1000000000000 : ℝ)
  | 2 => (2695381 / 1000000000000 : ℝ)
  | 3 => (2782801 / 1000000000000 : ℝ)
  | 4 => (2872279 / 1000000000000 : ℝ)
  | 5 => (740961 / 250000000000 : ℝ)
  | 6 => (1528763 / 500000000000 : ℝ)
  | 7 => (630671 / 200000000000 : ℝ)
  | 8 => (20321 / 6250000000 : ℝ)
  | 9 => (3351571 / 1000000000000 : ℝ)
  | 10 => (3454019 / 1000000000000 : ℝ)
  | 11 => (3558733 / 1000000000000 : ℝ)
  | 12 => (733149 / 200000000000 : ℝ)
  | 13 => (3775083 / 1000000000000 : ℝ)
  | 14 => (1943389 / 500000000000 : ℝ)
  | 15 => (2000431 / 500000000000 : ℝ)
  | 16 => (1029341 / 250000000000 : ℝ)
  | 17 => (847263 / 200000000000 : ℝ)
  | 18 => (2178873 / 500000000000 : ℝ)
  | 19 => (560211 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch006Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (260999 / 100000000000 : ℝ)
  | 1 => (1347691 / 500000000000 : ℝ)
  | 2 => (1391401 / 500000000000 : ℝ)
  | 3 => (71807 / 25000000000 : ℝ)
  | 4 => (592769 / 200000000000 : ℝ)
  | 5 => (3057527 / 1000000000000 : ℝ)
  | 6 => (788339 / 250000000000 : ℝ)
  | 7 => (3251361 / 1000000000000 : ℝ)
  | 8 => (837893 / 250000000000 : ℝ)
  | 9 => (172701 / 50000000000 : ℝ)
  | 10 => (1779367 / 500000000000 : ℝ)
  | 11 => (1832873 / 500000000000 : ℝ)
  | 12 => (943771 / 250000000000 : ℝ)
  | 13 => (3886779 / 1000000000000 : ℝ)
  | 14 => (4000863 / 1000000000000 : ℝ)
  | 15 => (823473 / 200000000000 : ℝ)
  | 16 => (1059079 / 250000000000 : ℝ)
  | 17 => (4357747 / 1000000000000 : ℝ)
  | 18 => (4481689 / 1000000000000 : ℝ)
  | 19 => (1152043 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch006Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((120 : ℝ) + (j.val : ℝ)) / 1600)
      (((120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch006Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch006Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((120 : ℝ) + (j.val : ℝ)) / 1600)
    (((120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch006Neg25WeightLower j.val) (hpThetaShiftTwoBatch006Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch006Neg25WeightLower, hpThetaShiftTwoBatch006Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch006Neg25_integral_bounds :
    (71805187 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (9348843 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch006Lower hpThetaJensenCellsBatch006Upper
    hpThetaShiftTwoBatch006Neg25WeightLower hpThetaShiftTwoBatch006Neg25WeightUpper hpThetaJensenCellsBatch006_bounds hpThetaShiftTwoBatch006Neg25_weight_bounds
  have hl : (71805187 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch006Lower j * hpThetaShiftTwoBatch006Neg25WeightLower j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftTwoBatch006Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftTwoBatch006Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch006Lower j * hpThetaShiftTwoBatch006Neg25WeightUpper j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftTwoBatch006Neg25WeightUpper j) / 1600) ≤ (9348843 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftTwoBatch006Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (120 : ℝ) / 1600 = 6 / 80 by norm_num,
    show ((120 : ℝ) + 20) / 1600 = (6 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch006Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch006Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch006Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch006Neg25_integral_bounds
end HodgeProofHP
