/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch026

/-! Exact signed weight and batch integral certificates, batch 26 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch026Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-57348609 / 250000000000 : ℝ)
  | 1 => (-230355333 / 1000000000000 : ℝ)
  | 2 => (-115642369 / 500000000000 : ℝ)
  | 3 => (-232181903 / 1000000000000 : ℝ)
  | 4 => (-9321843 / 40000000000 : ℝ)
  | 5 => (-116938247 / 500000000000 : ℝ)
  | 6 => (-234672391 / 1000000000000 : ℝ)
  | 7 => (-117716497 / 500000000000 : ℝ)
  | 8 => (-236157521 / 1000000000000 : ℝ)
  | 9 => (-236845183 / 1000000000000 : ℝ)
  | 10 => (-59373797 / 250000000000 : ℝ)
  | 11 => (-238106733 / 1000000000000 : ℝ)
  | 12 => (-23867901 / 100000000000 : ℝ)
  | 13 => (-59802801 / 250000000000 : ℝ)
  | 14 => (-119851247 / 500000000000 : ℝ)
  | 15 => (-240152053 / 1000000000000 : ℝ)
  | 16 => (-60139761 / 250000000000 : ℝ)
  | 17 => (-60230657 / 250000000000 : ℝ)
  | 18 => (-60310489 / 250000000000 : ℝ)
  | 19 => (-241516173 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch026Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-114201393 / 500000000000 : ℝ)
  | 1 => (-45878887 / 200000000000 : ℝ)
  | 2 => (-57588833 / 250000000000 : ℝ)
  | 3 => (-231284737 / 1000000000000 : ℝ)
  | 4 => (-116090951 / 500000000000 : ℝ)
  | 5 => (-116523037 / 500000000000 : ℝ)
  | 6 => (-233876493 / 1000000000000 : ℝ)
  | 7 => (-23467239 / 100000000000 : ℝ)
  | 8 => (-235432993 / 1000000000000 : ℝ)
  | 9 => (-2951969 / 12500000000 : ℝ)
  | 10 => (-118422591 / 500000000000 : ℝ)
  | 11 => (-237495187 / 1000000000000 : ℝ)
  | 12 => (-59526683 / 250000000000 : ℝ)
  | 13 => (-238679009 / 1000000000000 : ℝ)
  | 14 => (-239211203 / 1000000000000 : ℝ)
  | 15 => (-239702493 / 1000000000000 : ℝ)
  | 16 => (-60038013 / 250000000000 : ℝ)
  | 17 => (-240559043 / 1000000000000 : ℝ)
  | 18 => (-240922627 / 1000000000000 : ℝ)
  | 19 => (-48248391 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch026Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((520 : ℝ) + (j.val : ℝ)) / 1600)
      (((520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch026Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch026Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((520 : ℝ) + (j.val : ℝ)) / 1600)
    (((520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch026Neg100WeightLower j.val) (hpThetaShiftTwoBatch026Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch026Neg100WeightLower, hpThetaShiftTwoBatch026Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch026Neg100_integral_bounds :
    (-222209193 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-1748984211 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch026Lower hpThetaJensenCellsBatch026Upper
    hpThetaShiftTwoBatch026Neg100WeightLower hpThetaShiftTwoBatch026Neg100WeightUpper hpThetaJensenCellsBatch026_bounds hpThetaShiftTwoBatch026Neg100_weight_bounds
  have hl : (-222209193 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch026Lower j * hpThetaShiftTwoBatch026Neg100WeightLower j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftTwoBatch026Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftTwoBatch026Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch026Lower j * hpThetaShiftTwoBatch026Neg100WeightUpper j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftTwoBatch026Neg100WeightUpper j) / 1600) ≤ (-1748984211 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftTwoBatch026Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (520 : ℝ) / 1600 = 26 / 80 by norm_num,
    show ((520 : ℝ) + 20) / 1600 = (26 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch026Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-168323339 / 1000000000000 : ℝ)
  | 1 => (-85570059 / 500000000000 : ℝ)
  | 2 => (-6958921 / 40000000000 : ℝ)
  | 3 => (-176821891 / 1000000000000 : ℝ)
  | 4 => (-35937309 / 200000000000 : ℝ)
  | 5 => (-18256681 / 100000000000 : ℝ)
  | 6 => (-37092501 / 200000000000 : ℝ)
  | 7 => (-37674689 / 200000000000 : ℝ)
  | 8 => (-2391243 / 12500000000 : ℝ)
  | 9 => (-24280037 / 125000000000 : ℝ)
  | 10 => (-98597907 / 500000000000 : ℝ)
  | 11 => (-200165791 / 1000000000000 : ℝ)
  | 12 => (-203150019 / 1000000000000 : ℝ)
  | 13 => (-41229657 / 200000000000 : ℝ)
  | 14 => (-52290093 / 250000000000 : ℝ)
  | 15 => (-212186057 / 1000000000000 : ℝ)
  | 16 => (-43045023 / 200000000000 : ℝ)
  | 17 => (-109138657 / 500000000000 : ℝ)
  | 18 => (-221342417 / 1000000000000 : ℝ)
  | 19 => (-224420183 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch026Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-165522849 / 1000000000000 : ℝ)
  | 1 => (-84161669 / 500000000000 : ℝ)
  | 2 => (-171140117 / 1000000000000 : ℝ)
  | 3 => (-5436657 / 31250000000 : ℝ)
  | 4 => (-17682189 / 100000000000 : ℝ)
  | 5 => (-11230409 / 62500000000 : ℝ)
  | 6 => (-182566809 / 1000000000000 : ℝ)
  | 7 => (-23182813 / 125000000000 : ℝ)
  | 8 => (-47093361 / 250000000000 : ℝ)
  | 9 => (-191299439 / 1000000000000 : ℝ)
  | 10 => (-38848059 / 200000000000 : ℝ)
  | 11 => (-197195813 / 1000000000000 : ℝ)
  | 12 => (-20016579 / 100000000000 : ℝ)
  | 13 => (-101575009 / 500000000000 : ℝ)
  | 14 => (-51537071 / 250000000000 : ℝ)
  | 15 => (-209160371 / 1000000000000 : ℝ)
  | 16 => (-26523257 / 125000000000 : ℝ)
  | 17 => (-107612557 / 500000000000 : ℝ)
  | 18 => (-218277313 / 1000000000000 : ℝ)
  | 19 => (-13833901 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch026Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((520 : ℝ) + (j.val : ℝ)) / 1600)
      (((520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch026Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch026Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((520 : ℝ) + (j.val : ℝ)) / 1600)
    (((520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch026Neg65WeightLower j.val) (hpThetaShiftTwoBatch026Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch026Neg65WeightLower, hpThetaShiftTwoBatch026Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch026Neg65_integral_bounds :
    (-1470018687 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-1428516727 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch026Lower hpThetaJensenCellsBatch026Upper
    hpThetaShiftTwoBatch026Neg65WeightLower hpThetaShiftTwoBatch026Neg65WeightUpper hpThetaJensenCellsBatch026_bounds hpThetaShiftTwoBatch026Neg65_weight_bounds
  have hl : (-1470018687 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch026Lower j * hpThetaShiftTwoBatch026Neg65WeightLower j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftTwoBatch026Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftTwoBatch026Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch026Lower j * hpThetaShiftTwoBatch026Neg65WeightUpper j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftTwoBatch026Neg65WeightUpper j) / 1600) ≤ (-1428516727 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftTwoBatch026Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (520 : ℝ) / 1600 = 26 / 80 by norm_num,
    show ((520 : ℝ) + 20) / 1600 = (26 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch026Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (12478977 / 1000000000000 : ℝ)
  | 1 => (10457713 / 1000000000000 : ℝ)
  | 2 => (8410457 / 1000000000000 : ℝ)
  | 3 => (633711 / 100000000000 : ℝ)
  | 4 => (2118789 / 500000000000 : ℝ)
  | 5 => (263971 / 125000000000 : ℝ)
  | 6 => (-40413 / 1000000000000 : ℝ)
  | 7 => (-443811 / 200000000000 : ℝ)
  | 8 => (-4424247 / 1000000000000 : ℝ)
  | 9 => (-6656077 / 1000000000000 : ℝ)
  | 10 => (-891463 / 100000000000 : ℝ)
  | 11 => (-11199991 / 1000000000000 : ℝ)
  | 12 => (-13512241 / 1000000000000 : ℝ)
  | 13 => (-7925731 / 500000000000 : ℝ)
  | 14 => (-9108867 / 500000000000 : ℝ)
  | 15 => (-5152783 / 250000000000 : ℝ)
  | 16 => (-11515867 / 500000000000 : ℝ)
  | 17 => (-25479613 / 1000000000000 : ℝ)
  | 18 => (-27954841 / 1000000000000 : ℝ)
  | 19 => (-30457489 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch026Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2894869 / 200000000000 : ℝ)
  | 1 => (6239489 / 500000000000 : ℝ)
  | 2 => (5228857 / 500000000000 : ℝ)
  | 3 => (4205229 / 500000000000 : ℝ)
  | 4 => (6337111 / 1000000000000 : ℝ)
  | 5 => (4237579 / 1000000000000 : ℝ)
  | 6 => (2111769 / 1000000000000 : ℝ)
  | 7 => (-10103 / 250000000000 : ℝ)
  | 8 => (-1109527 / 500000000000 : ℝ)
  | 9 => (-2212123 / 500000000000 : ℝ)
  | 10 => (-1664019 / 250000000000 : ℝ)
  | 11 => (-8914629 / 1000000000000 : ℝ)
  | 12 => (-1119999 / 100000000000 : ℝ)
  | 13 => (-168903 / 12500000000 : ℝ)
  | 14 => (-15851461 / 1000000000000 : ℝ)
  | 15 => (-18217733 / 1000000000000 : ℝ)
  | 16 => (-20611131 / 1000000000000 : ℝ)
  | 17 => (-23031733 / 1000000000000 : ℝ)
  | 18 => (-6369903 / 250000000000 : ℝ)
  | 19 => (-698871 / 25000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch026Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((520 : ℝ) + (j.val : ℝ)) / 1600)
      (((520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch026Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch026Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((520 : ℝ) + (j.val : ℝ)) / 1600)
    (((520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch026Neg45WeightLower j.val) (hpThetaShiftTwoBatch026Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch026Neg45WeightLower, hpThetaShiftTwoBatch026Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch026Neg45_integral_bounds :
    (-59599937 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-10408683 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch026Lower hpThetaJensenCellsBatch026Upper
    hpThetaShiftTwoBatch026Neg45WeightLower hpThetaShiftTwoBatch026Neg45WeightUpper hpThetaJensenCellsBatch026_bounds hpThetaShiftTwoBatch026Neg45_weight_bounds
  have hl : (-59599937 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch026Lower j * hpThetaShiftTwoBatch026Neg45WeightLower j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftTwoBatch026Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftTwoBatch026Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch026Lower j * hpThetaShiftTwoBatch026Neg45WeightUpper j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftTwoBatch026Neg45WeightUpper j) / 1600) ≤ (-10408683 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftTwoBatch026Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (520 : ℝ) / 1600 = 26 / 80 by norm_num,
    show ((520 : ℝ) + 20) / 1600 = (26 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch026Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (162666201 / 500000000000 : ℝ)
  | 1 => (65197087 / 200000000000 : ℝ)
  | 2 => (6532487 / 20000000000 : ℝ)
  | 3 => (163624487 / 500000000000 : ℝ)
  | 4 => (327859131 / 1000000000000 : ℝ)
  | 5 => (328454649 / 1000000000000 : ℝ)
  | 6 => (6580707 / 20000000000 : ℝ)
  | 7 => (16480053 / 50000000000 : ℝ)
  | 8 => (165075801 / 500000000000 : ℝ)
  | 9 => (165343399 / 500000000000 : ℝ)
  | 10 => (41400809 / 125000000000 : ℝ)
  | 11 => (66342089 / 200000000000 : ℝ)
  | 12 => (166099269 / 500000000000 : ℝ)
  | 13 => (83167643 / 250000000000 : ℝ)
  | 14 => (10410199 / 31250000000 : ℝ)
  | 15 => (20847859 / 62500000000 : ℝ)
  | 16 => (166994261 / 500000000000 : ℝ)
  | 17 => (167197259 / 500000000000 : ℝ)
  | 18 => (5230993 / 15625000000 : ℝ)
  | 19 => (4189443 / 12500000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch026Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (81496359 / 250000000000 : ℝ)
  | 1 => (326624351 / 1000000000000 : ℝ)
  | 2 => (13089959 / 40000000000 : ℝ)
  | 3 => (81964783 / 250000000000 : ℝ)
  | 4 => (6569093 / 20000000000 : ℝ)
  | 5 => (329035351 / 1000000000000 : ℝ)
  | 6 => (329601061 / 1000000000000 : ℝ)
  | 7 => (330151603 / 1000000000000 : ℝ)
  | 8 => (330686799 / 1000000000000 : ℝ)
  | 9 => (331206473 / 1000000000000 : ℝ)
  | 10 => (165855223 / 500000000000 : ℝ)
  | 11 => (332198539 / 1000000000000 : ℝ)
  | 12 => (332670573 / 1000000000000 : ℝ)
  | 13 => (333126369 / 1000000000000 : ℝ)
  | 14 => (66713149 / 200000000000 : ℝ)
  | 15 => (333988523 / 1000000000000 : ℝ)
  | 16 => (334394519 / 1000000000000 : ℝ)
  | 17 => (334783553 / 1000000000000 : ℝ)
  | 18 => (335155441 / 1000000000000 : ℝ)
  | 19 => (167755001 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch026Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((520 : ℝ) + (j.val : ℝ)) / 1600)
      (((520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch026Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch026Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((520 : ℝ) + (j.val : ℝ)) / 1600)
    (((520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch026Neg25WeightLower j.val) (hpThetaShiftTwoBatch026Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch026Neg25WeightLower, hpThetaShiftTwoBatch026Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch026Neg25_integral_bounds :
    (1226188313 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (2489476129 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch026Lower hpThetaJensenCellsBatch026Upper
    hpThetaShiftTwoBatch026Neg25WeightLower hpThetaShiftTwoBatch026Neg25WeightUpper hpThetaJensenCellsBatch026_bounds hpThetaShiftTwoBatch026Neg25_weight_bounds
  have hl : (1226188313 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch026Lower j * hpThetaShiftTwoBatch026Neg25WeightLower j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftTwoBatch026Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftTwoBatch026Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch026Lower j * hpThetaShiftTwoBatch026Neg25WeightUpper j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftTwoBatch026Neg25WeightUpper j) / 1600) ≤ (2489476129 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftTwoBatch026Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (520 : ℝ) / 1600 = 26 / 80 by norm_num,
    show ((520 : ℝ) + 20) / 1600 = (26 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch026Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch026Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch026Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch026Neg25_integral_bounds
end HodgeProofHP
