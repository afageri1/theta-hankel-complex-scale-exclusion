/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch044

/-! Exact signed weight and batch integral certificates, batch 44 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch044Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4156746753 / 1000000000000 : ℝ)
  | 1 => (4124801321 / 1000000000000 : ℝ)
  | 2 => (4091317197 / 1000000000000 : ℝ)
  | 3 => (253516679 / 62500000000 : ℝ)
  | 4 => (401962247 / 100000000000 : ℝ)
  | 5 => (159254233 / 40000000000 : ℝ)
  | 6 => (985359599 / 250000000000 : ℝ)
  | 7 => (3899841307 / 1000000000000 : ℝ)
  | 8 => (3856535333 / 1000000000000 : ℝ)
  | 9 => (38114909 / 10000000000 : ℝ)
  | 10 => (3764678079 / 1000000000000 : ℝ)
  | 11 => (1858033291 / 500000000000 : ℝ)
  | 12 => (1832812881 / 500000000000 : ℝ)
  | 13 => (3613324609 / 1000000000000 : ℝ)
  | 14 => (711826349 / 200000000000 : ℝ)
  | 15 => (1751507711 / 500000000000 : ℝ)
  | 16 => (3444943517 / 1000000000000 : ℝ)
  | 17 => (3384883533 / 1000000000000 : ℝ)
  | 18 => (3322802591 / 1000000000000 : ℝ)
  | 19 => (3258667429 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch044Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (4187180677 / 1000000000000 : ℝ)
  | 1 => (2078373377 / 500000000000 : ℝ)
  | 2 => (2062400661 / 500000000000 : ℝ)
  | 3 => (2045658599 / 500000000000 : ℝ)
  | 4 => (811253373 / 200000000000 : ℝ)
  | 5 => (4019622471 / 1000000000000 : ℝ)
  | 6 => (1990677913 / 500000000000 : ℝ)
  | 7 => (3941438397 / 1000000000000 : ℝ)
  | 8 => (974960327 / 250000000000 : ℝ)
  | 9 => (1928267667 / 500000000000 : ℝ)
  | 10 => (3811490901 / 1000000000000 : ℝ)
  | 11 => (11764619 / 3125000000 : ℝ)
  | 12 => (3716066583 / 1000000000000 : ℝ)
  | 13 => (3665625763 / 1000000000000 : ℝ)
  | 14 => (361332461 / 100000000000 : ℝ)
  | 15 => (1779565873 / 500000000000 : ℝ)
  | 16 => (3503015423 / 1000000000000 : ℝ)
  | 17 => (1722471759 / 500000000000 : ℝ)
  | 18 => (1692441767 / 500000000000 : ℝ)
  | 19 => (103837581 / 31250000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch044Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((880 : ℝ) + (j.val : ℝ)) / 1600)
      (((880 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch044Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch044Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((880 : ℝ) + (j.val : ℝ)) / 1600)
    (((880 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch044Neg100WeightLower j.val) (hpThetaShiftTwoBatch044Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch044Neg100WeightLower, hpThetaShiftTwoBatch044Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch044Neg100_integral_bounds :
    (1347974729 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (1388622381 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (880 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch044Lower hpThetaJensenCellsBatch044Upper
    hpThetaShiftTwoBatch044Neg100WeightLower hpThetaShiftTwoBatch044Neg100WeightUpper hpThetaJensenCellsBatch044_bounds hpThetaShiftTwoBatch044Neg100_weight_bounds
  have hl : (1347974729 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch044Lower j * hpThetaShiftTwoBatch044Neg100WeightLower j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftTwoBatch044Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftTwoBatch044Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch044Lower j * hpThetaShiftTwoBatch044Neg100WeightUpper j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftTwoBatch044Neg100WeightUpper j) / 1600) ≤ (1388622381 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftTwoBatch044Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (880 : ℝ) / 1600 = 44 / 80 by norm_num,
    show ((880 : ℝ) + 20) / 1600 = (44 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch044Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (563141691 / 200000000000 : ℝ)
  | 1 => (714182381 / 250000000000 : ℝ)
  | 2 => (2898020371 / 1000000000000 : ℝ)
  | 3 => (1469790061 / 500000000000 : ℝ)
  | 4 => (149070393 / 50000000000 : ℝ)
  | 5 => (94484457 / 31250000000 : ℝ)
  | 6 => (3065863407 / 1000000000000 : ℝ)
  | 7 => (1554244577 / 500000000000 : ℝ)
  | 8 => (3151378767 / 1000000000000 : ℝ)
  | 9 => (1597265549 / 500000000000 : ℝ)
  | 10 => (3237944953 / 1000000000000 : ℝ)
  | 11 => (205101193 / 62500000000 : ℝ)
  | 12 => (332555221 / 100000000000 : ℝ)
  | 13 => (3369742979 / 1000000000000 : ℝ)
  | 14 => (1707095001 / 500000000000 : ℝ)
  | 15 => (864722959 / 250000000000 : ℝ)
  | 16 => (1751923493 / 500000000000 : ℝ)
  | 17 => (221815869 / 62500000000 : ℝ)
  | 18 => (224656937 / 62500000000 : ℝ)
  | 19 => (910054149 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch044Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (114269181 / 40000000000 : ℝ)
  | 1 => (724505093 / 250000000000 : ℝ)
  | 2 => (2939580123 / 1000000000000 : ℝ)
  | 3 => (2981407861 / 1000000000000 : ℝ)
  | 4 => (24188021 / 8000000000 : ℝ)
  | 5 => (191616463 / 62500000000 : ℝ)
  | 6 => (621697831 / 200000000000 : ℝ)
  | 7 => (196961173 / 62500000000 : ℝ)
  | 8 => (3194531099 / 1000000000000 : ℝ)
  | 9 => (1618972477 / 500000000000 : ℝ)
  | 10 => (3281619089 / 1000000000000 : ℝ)
  | 11 => (3325552211 / 1000000000000 : ℝ)
  | 12 => (168487149 / 50000000000 : ℝ)
  | 13 => (3414190003 / 1000000000000 : ℝ)
  | 14 => (3458891837 / 1000000000000 : ℝ)
  | 15 => (3503846987 / 1000000000000 : ℝ)
  | 16 => (709810781 / 200000000000 : ℝ)
  | 17 => (3594510993 / 1000000000000 : ℝ)
  | 18 => (3640216597 / 1000000000000 : ℝ)
  | 19 => (3686169009 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch044Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((880 : ℝ) + (j.val : ℝ)) / 1600)
      (((880 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch044Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch044Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((880 : ℝ) + (j.val : ℝ)) / 1600)
    (((880 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch044Neg65WeightLower j.val) (hpThetaShiftTwoBatch044Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch044Neg65WeightLower, hpThetaShiftTwoBatch044Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch044Neg65_integral_bounds :
    (143268417 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (591164883 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (880 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch044Lower hpThetaJensenCellsBatch044Upper
    hpThetaShiftTwoBatch044Neg65WeightLower hpThetaShiftTwoBatch044Neg65WeightUpper hpThetaJensenCellsBatch044_bounds hpThetaShiftTwoBatch044Neg65_weight_bounds
  have hl : (143268417 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch044Lower j * hpThetaShiftTwoBatch044Neg65WeightLower j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftTwoBatch044Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftTwoBatch044Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch044Lower j * hpThetaShiftTwoBatch044Neg65WeightUpper j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftTwoBatch044Neg65WeightUpper j) / 1600) ≤ (591164883 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftTwoBatch044Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (880 : ℝ) / 1600 = 44 / 80 by norm_num,
    show ((880 : ℝ) + 20) / 1600 = (44 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch044Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-108648519 / 125000000000 : ℝ)
  | 1 => (-858216759 / 1000000000000 : ℝ)
  | 2 => (-52939339 / 62500000000 : ℝ)
  | 3 => (-417812247 / 500000000000 : ℝ)
  | 4 => (-412000157 / 500000000000 : ℝ)
  | 5 => (-812155227 / 1000000000000 : ℝ)
  | 6 => (-400043787 / 500000000000 : ℝ)
  | 7 => (-157559139 / 200000000000 : ℝ)
  | 8 => (-387638963 / 500000000000 : ℝ)
  | 9 => (-152506521 / 200000000000 : ℝ)
  | 10 => (-46847379 / 62500000000 : ℝ)
  | 11 => (-368176319 / 500000000000 : ℝ)
  | 12 => (-361457329 / 500000000000 : ℝ)
  | 13 => (-141848491 / 200000000000 : ℝ)
  | 14 => (-347667179 / 500000000000 : ℝ)
  | 15 => (-85148587 / 125000000000 : ℝ)
  | 16 => (-166700949 / 250000000000 : ℝ)
  | 17 => (-326088993 / 500000000000 : ℝ)
  | 18 => (-637309591 / 1000000000000 : ℝ)
  | 19 => (-622196939 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch044Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-429108379 / 500000000000 : ℝ)
  | 1 => (-847029423 / 1000000000000 : ℝ)
  | 2 => (-835624493 / 1000000000000 : ℝ)
  | 3 => (-824000313 / 1000000000000 : ℝ)
  | 4 => (-406077613 / 500000000000 : ℝ)
  | 5 => (-800087573 / 1000000000000 : ℝ)
  | 6 => (-393897847 / 500000000000 : ℝ)
  | 7 => (-31011117 / 40000000000 : ℝ)
  | 8 => (-190633151 / 250000000000 : ℝ)
  | 9 => (-749558063 / 1000000000000 : ℝ)
  | 10 => (-736352637 / 1000000000000 : ℝ)
  | 11 => (-722914657 / 1000000000000 : ℝ)
  | 12 => (-354621227 / 500000000000 : ℝ)
  | 13 => (-695334357 / 1000000000000 : ℝ)
  | 14 => (-136237739 / 200000000000 : ℝ)
  | 15 => (-133360759 / 200000000000 : ℝ)
  | 16 => (-130435597 / 200000000000 : ℝ)
  | 17 => (-63730959 / 100000000000 : ℝ)
  | 18 => (-311098469 / 500000000000 : ℝ)
  | 19 => (-606838353 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch044Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((880 : ℝ) + (j.val : ℝ)) / 1600)
      (((880 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch044Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch044Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((880 : ℝ) + (j.val : ℝ)) / 1600)
    (((880 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch044Neg45WeightLower j.val) (hpThetaShiftTwoBatch044Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch044Neg45WeightLower, hpThetaShiftTwoBatch044Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch044Neg45_integral_bounds :
    (-137480233 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-26549751 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (880 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch044Lower hpThetaJensenCellsBatch044Upper
    hpThetaShiftTwoBatch044Neg45WeightLower hpThetaShiftTwoBatch044Neg45WeightUpper hpThetaJensenCellsBatch044_bounds hpThetaShiftTwoBatch044Neg45_weight_bounds
  have hl : (-137480233 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch044Lower j * hpThetaShiftTwoBatch044Neg45WeightLower j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftTwoBatch044Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftTwoBatch044Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch044Lower j * hpThetaShiftTwoBatch044Neg45WeightUpper j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftTwoBatch044Neg45WeightUpper j) / 1600) ≤ (-26549751 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftTwoBatch044Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (880 : ℝ) / 1600 = 44 / 80 by norm_num,
    show ((880 : ℝ) + 20) / 1600 = (44 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch044Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1651574467 / 1000000000000 : ℝ)
  | 1 => (-1664827417 / 1000000000000 : ℝ)
  | 2 => (-839053909 / 500000000000 : ℝ)
  | 3 => (-1691415209 / 1000000000000 : ℝ)
  | 4 => (-1704749127 / 1000000000000 : ℝ)
  | 5 => (-1718109099 / 1000000000000 : ℝ)
  | 6 => (-432873663 / 250000000000 : ℝ)
  | 7 => (-218113163 / 125000000000 : ℝ)
  | 8 => (-1758340569 / 1000000000000 : ℝ)
  | 9 => (-1771799957 / 1000000000000 : ℝ)
  | 10 => (-178528297 / 100000000000 : ℝ)
  | 11 => (-449697277 / 250000000000 : ℝ)
  | 12 => (-906158931 / 500000000000 : ℝ)
  | 13 => (-912934361 / 500000000000 : ℝ)
  | 14 => (-114965073 / 62500000000 : ℝ)
  | 15 => (-1853034677 / 1000000000000 : ℝ)
  | 16 => (-933324361 / 500000000000 : ℝ)
  | 17 => (-117517673 / 62500000000 : ℝ)
  | 18 => (-473484069 / 250000000000 : ℝ)
  | 19 => (-19076087 / 10000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch044Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1638349421 / 1000000000000 : ℝ)
  | 1 => (-825787233 / 500000000000 : ℝ)
  | 2 => (-208103427 / 125000000000 : ℝ)
  | 3 => (-1678107817 / 1000000000000 : ℝ)
  | 4 => (-211426901 / 125000000000 : ℝ)
  | 5 => (-852374563 / 500000000000 : ℝ)
  | 6 => (-859054549 / 500000000000 : ℝ)
  | 7 => (-1731494651 / 1000000000000 : ℝ)
  | 8 => (-1744905303 / 1000000000000 : ℝ)
  | 9 => (-219792571 / 125000000000 : ℝ)
  | 10 => (-442949989 / 250000000000 : ℝ)
  | 11 => (-1785282969 / 1000000000000 : ℝ)
  | 12 => (-1798789107 / 1000000000000 : ℝ)
  | 13 => (-1812317861 / 1000000000000 : ℝ)
  | 14 => (-1825868721 / 1000000000000 : ℝ)
  | 15 => (-1839441167 / 1000000000000 : ℝ)
  | 16 => (-463258669 / 250000000000 : ℝ)
  | 17 => (-1866648721 / 1000000000000 : ℝ)
  | 18 => (-1880282767 / 1000000000000 : ℝ)
  | 19 => (-75757451 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch044Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((880 : ℝ) + (j.val : ℝ)) / 1600)
      (((880 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch044Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch044Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((880 : ℝ) + (j.val : ℝ)) / 1600)
    (((880 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch044Neg25WeightLower j.val) (hpThetaShiftTwoBatch044Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch044Neg25WeightLower, hpThetaShiftTwoBatch044Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch044Neg25_integral_bounds :
    (-80685313 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-3933737 / 3125000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (880 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch044Lower hpThetaJensenCellsBatch044Upper
    hpThetaShiftTwoBatch044Neg25WeightLower hpThetaShiftTwoBatch044Neg25WeightUpper hpThetaJensenCellsBatch044_bounds hpThetaShiftTwoBatch044Neg25_weight_bounds
  have hl : (-80685313 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch044Lower j * hpThetaShiftTwoBatch044Neg25WeightLower j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftTwoBatch044Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftTwoBatch044Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch044Lower j * hpThetaShiftTwoBatch044Neg25WeightUpper j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftTwoBatch044Neg25WeightUpper j) / 1600) ≤ (-3933737 / 3125000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftTwoBatch044Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (880 : ℝ) / 1600 = 44 / 80 by norm_num,
    show ((880 : ℝ) + 20) / 1600 = (44 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch044Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch044Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch044Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch044Neg25_integral_bounds
end HodgeProofHP
