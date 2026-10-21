/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch009

/-! Exact signed weight and batch integral certificates, batch 9 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch009Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (562474009 / 200000000000 : ℝ)
  | 1 => (1404463021 / 500000000000 : ℝ)
  | 2 => (1402409327 / 500000000000 : ℝ)
  | 3 => (350005137 / 125000000000 : ℝ)
  | 4 => (2794586651 / 1000000000000 : ℝ)
  | 5 => (2788448661 / 1000000000000 : ℝ)
  | 6 => (1390810267 / 500000000000 : ℝ)
  | 7 => (1387047873 / 500000000000 : ℝ)
  | 8 => (2765867837 / 1000000000000 : ℝ)
  | 9 => (1378465209 / 500000000000 : ℝ)
  | 10 => (686819293 / 250000000000 : ℝ)
  | 11 => (2736901851 / 1000000000000 : ℝ)
  | 12 => (2725798281 / 1000000000000 : ℝ)
  | 13 => (2713960363 / 1000000000000 : ℝ)
  | 14 => (2701382073 / 1000000000000 : ℝ)
  | 15 => (2688057467 / 1000000000000 : ℝ)
  | 16 => (668495169 / 250000000000 : ℝ)
  | 17 => (2659145913 / 1000000000000 : ℝ)
  | 18 => (1321773737 / 500000000000 : ℝ)
  | 19 => (328397467 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch009Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (10996709 / 3906250000 : ℝ)
  | 1 => (1406185023 / 500000000000 : ℝ)
  | 2 => (2808926043 / 1000000000000 : ℝ)
  | 3 => (560963731 / 200000000000 : ℝ)
  | 4 => (2800041097 / 1000000000000 : ℝ)
  | 5 => (698646663 / 250000000000 : ℝ)
  | 6 => (1394224331 / 500000000000 : ℝ)
  | 7 => (556324107 / 200000000000 : ℝ)
  | 8 => (2774095747 / 1000000000000 : ℝ)
  | 9 => (1382933919 / 500000000000 : ℝ)
  | 10 => (2756930419 / 1000000000000 : ℝ)
  | 11 => (2747277173 / 1000000000000 : ℝ)
  | 12 => (684225463 / 250000000000 : ℝ)
  | 13 => (1362899141 / 500000000000 : ℝ)
  | 14 => (678490091 / 250000000000 : ℝ)
  | 15 => (1350691037 / 500000000000 : ℝ)
  | 16 => (672014367 / 250000000000 : ℝ)
  | 17 => (2673980677 / 1000000000000 : ℝ)
  | 18 => (1329572957 / 500000000000 : ℝ)
  | 19 => (105741899 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch009Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((180 : ℝ) + (j.val : ℝ)) / 1600)
      (((180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch009Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch009Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((180 : ℝ) + (j.val : ℝ)) / 1600)
    (((180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch009Neg100WeightLower j.val) (hpThetaShiftOneBatch009Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch009Neg100WeightLower, hpThetaShiftOneBatch009Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch009Neg100_integral_bounds :
    (13334162117 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (27060267819 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch009Lower hpThetaJensenCellsBatch009Upper
    hpThetaShiftOneBatch009Neg100WeightLower hpThetaShiftOneBatch009Neg100WeightUpper hpThetaJensenCellsBatch009_bounds hpThetaShiftOneBatch009Neg100_weight_bounds
  have hl : (13334162117 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch009Lower j * hpThetaShiftOneBatch009Neg100WeightLower j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftOneBatch009Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftOneBatch009Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch009Lower j * hpThetaShiftOneBatch009Neg100WeightUpper j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftOneBatch009Neg100WeightUpper j) / 1600) ≤ (27060267819 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftOneBatch009Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (180 : ℝ) / 1600 = 9 / 80 by norm_num,
    show ((180 : ℝ) + 20) / 1600 = (9 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch009Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (393512713 / 100000000000 : ℝ)
  | 1 => (61786807 / 15625000000 : ℝ)
  | 2 => (3973195219 / 1000000000000 : ℝ)
  | 3 => (3991639307 / 1000000000000 : ℝ)
  | 4 => (2004840693 / 500000000000 : ℝ)
  | 5 => (4027314937 / 1000000000000 : ℝ)
  | 6 => (1011133363 / 250000000000 : ℝ)
  | 7 => (2030665217 / 500000000000 : ℝ)
  | 8 => (4077699397 / 1000000000000 : ℝ)
  | 9 => (4093633867 / 1000000000000 : ℝ)
  | 10 => (4109127381 / 1000000000000 : ℝ)
  | 11 => (4124173493 / 1000000000000 : ℝ)
  | 12 => (2069382883 / 500000000000 : ℝ)
  | 13 => (4152897783 / 1000000000000 : ℝ)
  | 14 => (4166563137 / 1000000000000 : ℝ)
  | 15 => (2089877721 / 500000000000 : ℝ)
  | 16 => (167698733 / 40000000000 : ℝ)
  | 17 => (525586929 / 125000000000 : ℝ)
  | 18 => (4216430427 / 1000000000000 : ℝ)
  | 19 => (2113833497 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch009Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3954355649 / 1000000000000 : ℝ)
  | 1 => (198659761 / 50000000000 : ℝ)
  | 2 => (997909827 / 250000000000 : ℝ)
  | 3 => (4009681387 / 1000000000000 : ℝ)
  | 4 => (2013657469 / 500000000000 : ℝ)
  | 5 => (4044533453 / 1000000000000 : ℝ)
  | 6 => (812266087 / 200000000000 : ℝ)
  | 7 => (2038849699 / 500000000000 : ℝ)
  | 8 => (1023408467 / 250000000000 : ℝ)
  | 9 => (2054563691 / 500000000000 : ℝ)
  | 10 => (2062086747 / 500000000000 : ℝ)
  | 11 => (4138765767 / 1000000000000 : ℝ)
  | 12 => (519112223 / 125000000000 : ℝ)
  | 13 => (2083281569 / 500000000000 : ℝ)
  | 14 => (4179755443 / 1000000000000 : ℝ)
  | 15 => (2096234163 / 500000000000 : ℝ)
  | 16 => (4204695433 / 1000000000000 : ℝ)
  | 17 => (1054107607 / 250000000000 : ℝ)
  | 18 => (845533399 / 200000000000 : ℝ)
  | 19 => (847679767 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch009Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((180 : ℝ) + (j.val : ℝ)) / 1600)
      (((180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch009Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch009Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((180 : ℝ) + (j.val : ℝ)) / 1600)
    (((180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch009Neg65WeightLower j.val) (hpThetaShiftOneBatch009Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch009Neg65WeightLower, hpThetaShiftOneBatch009Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch009Neg65_integral_bounds :
    (79659941773 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (10106794077 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch009Lower hpThetaJensenCellsBatch009Upper
    hpThetaShiftOneBatch009Neg65WeightLower hpThetaShiftOneBatch009Neg65WeightUpper hpThetaJensenCellsBatch009_bounds hpThetaShiftOneBatch009Neg65_weight_bounds
  have hl : (79659941773 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch009Lower j * hpThetaShiftOneBatch009Neg65WeightLower j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftOneBatch009Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftOneBatch009Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch009Lower j * hpThetaShiftOneBatch009Neg65WeightUpper j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftOneBatch009Neg65WeightUpper j) / 1600) ≤ (10106794077 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftOneBatch009Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (180 : ℝ) / 1600 = 9 / 80 by norm_num,
    show ((180 : ℝ) + 20) / 1600 = (9 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch009Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2403216189 / 500000000000 : ℝ)
  | 1 => (4843743331 / 1000000000000 : ℝ)
  | 2 => (4880920057 / 1000000000000 : ℝ)
  | 3 => (4917957561 / 1000000000000 : ℝ)
  | 4 => (2477425419 / 500000000000 : ℝ)
  | 5 => (39932759 / 8000000000 : ℝ)
  | 6 => (628523081 / 125000000000 : ℝ)
  | 7 => (40516921 / 8000000000 : ℝ)
  | 8 => (318805079 / 62500000000 : ℝ)
  | 9 => (160530563 / 31250000000 : ℝ)
  | 10 => (5172900323 / 1000000000000 : ℝ)
  | 11 => (65108039 / 12500000000 : ℝ)
  | 12 => (2622100667 / 500000000000 : ℝ)
  | 13 => (1319892471 / 250000000000 : ℝ)
  | 14 => (2657371841 / 500000000000 : ℝ)
  | 15 => (1069943527 / 200000000000 : ℝ)
  | 16 => (5384486641 / 1000000000000 : ℝ)
  | 17 => (1083809119 / 200000000000 : ℝ)
  | 18 => (681673673 / 125000000000 : ℝ)
  | 19 => (5487512889 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch009Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1210935833 / 250000000000 : ℝ)
  | 1 => (2440460029 / 500000000000 : ℝ)
  | 2 => (2458978781 / 500000000000 : ℝ)
  | 3 => (4954850839 / 1000000000000 : ℝ)
  | 4 => (1247898719 / 250000000000 : ℝ)
  | 5 => (5028184649 / 1000000000000 : ℝ)
  | 6 => (2532307563 / 500000000000 : ℝ)
  | 7 => (1020176253 / 200000000000 : ℝ)
  | 8 => (5136978017 / 1000000000000 : ℝ)
  | 9 => (1293225081 / 250000000000 : ℝ)
  | 10 => (5208643121 / 1000000000000 : ℝ)
  | 11 => (1048840267 / 200000000000 : ℝ)
  | 12 => (1055913977 / 200000000000 : ℝ)
  | 13 => (5314743683 / 1000000000000 : ℝ)
  | 14 => (1337429409 / 250000000000 : ℝ)
  | 15 => (2692243321 / 500000000000 : ℝ)
  | 16 => (1354761399 / 250000000000 : ℝ)
  | 17 => (1090677877 / 200000000000 : ℝ)
  | 18 => (548751289 / 100000000000 : ℝ)
  | 19 => (1380352747 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch009Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((180 : ℝ) + (j.val : ℝ)) / 1600)
      (((180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch009Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch009Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((180 : ℝ) + (j.val : ℝ)) / 1600)
    (((180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch009Neg40WeightLower j.val) (hpThetaShiftOneBatch009Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch009Neg40WeightLower, hpThetaShiftOneBatch009Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch009Neg40_integral_bounds :
    (20046042947 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (20412161153 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch009Lower hpThetaJensenCellsBatch009Upper
    hpThetaShiftOneBatch009Neg40WeightLower hpThetaShiftOneBatch009Neg40WeightUpper hpThetaJensenCellsBatch009_bounds hpThetaShiftOneBatch009Neg40_weight_bounds
  have hl : (20046042947 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch009Lower j * hpThetaShiftOneBatch009Neg40WeightLower j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftOneBatch009Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftOneBatch009Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch009Lower j * hpThetaShiftOneBatch009Neg40WeightUpper j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftOneBatch009Neg40WeightUpper j) / 1600) ≤ (20412161153 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftOneBatch009Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (180 : ℝ) / 1600 = 9 / 80 by norm_num,
    show ((180 : ℝ) + 20) / 1600 = (9 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch009Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1386843091 / 250000000000 : ℝ)
  | 1 => (280030657 / 50000000000 : ℝ)
  | 2 => (2826981789 / 500000000000 : ℝ)
  | 3 => (2853710387 / 500000000000 : ℝ)
  | 4 => (2880490907 / 500000000000 : ℝ)
  | 5 => (5814643773 / 1000000000000 : ℝ)
  | 6 => (5868403713 / 1000000000000 : ℝ)
  | 7 => (2961129343 / 500000000000 : ℝ)
  | 8 => (5976205733 / 1000000000000 : ℝ)
  | 9 => (6030241883 / 1000000000000 : ℝ)
  | 10 => (1216872831 / 200000000000 : ℝ)
  | 11 => (6138569557 / 1000000000000 : ℝ)
  | 12 => (3096427543 / 500000000000 : ℝ)
  | 13 => (97612777 / 15625000000 : ℝ)
  | 14 => (6301654459 / 1000000000000 : ℝ)
  | 15 => (6356162243 / 1000000000000 : ℝ)
  | 16 => (1602684509 / 250000000000 : ℝ)
  | 17 => (6465378781 / 1000000000000 : ℝ)
  | 18 => (1630020353 / 250000000000 : ℝ)
  | 19 => (1643710713 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch009Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5600613141 / 1000000000000 : ℝ)
  | 1 => (5653963579 / 1000000000000 : ℝ)
  | 2 => (228296831 / 40000000000 : ℝ)
  | 3 => (1152196363 / 200000000000 : ℝ)
  | 4 => (2907321887 / 500000000000 : ℝ)
  | 5 => (2934201857 / 500000000000 : ℝ)
  | 6 => (5922258687 / 1000000000000 : ℝ)
  | 7 => (2988102867 / 500000000000 : ℝ)
  | 8 => (1507560471 / 250000000000 : ℝ)
  | 9 => (1521091039 / 250000000000 : ℝ)
  | 10 => (3069284779 / 500000000000 : ℝ)
  | 11 => (6192855087 / 1000000000000 : ℝ)
  | 12 => (6247217729 / 1000000000000 : ℝ)
  | 13 => (315082723 / 50000000000 : ℝ)
  | 14 => (1589040561 / 250000000000 : ℝ)
  | 15 => (6410738037 / 1000000000000 : ℝ)
  | 16 => (3232689391 / 500000000000 : ℝ)
  | 17 => (6520081413 / 1000000000000 : ℝ)
  | 18 => (6574842853 / 1000000000000 : ℝ)
  | 19 => (6629660017 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch009Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((180 : ℝ) + (j.val : ℝ)) / 1600)
      (((180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch009Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch009Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((180 : ℝ) + (j.val : ℝ)) / 1600)
    (((180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch009Neg20WeightLower j.val) (hpThetaShiftOneBatch009Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch009Neg20WeightLower, hpThetaShiftOneBatch009Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch009Neg20_integral_bounds :
    (117858363499 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (120248370381 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch009Lower hpThetaJensenCellsBatch009Upper
    hpThetaShiftOneBatch009Neg20WeightLower hpThetaShiftOneBatch009Neg20WeightUpper hpThetaJensenCellsBatch009_bounds hpThetaShiftOneBatch009Neg20_weight_bounds
  have hl : (117858363499 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch009Lower j * hpThetaShiftOneBatch009Neg20WeightLower j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftOneBatch009Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftOneBatch009Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch009Lower j * hpThetaShiftOneBatch009Neg20WeightUpper j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftOneBatch009Neg20WeightUpper j) / 1600) ≤ (120248370381 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftOneBatch009Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (180 : ℝ) / 1600 = 9 / 80 by norm_num,
    show ((180 : ℝ) + 20) / 1600 = (9 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch009Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch009Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch009Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch009Neg20_integral_bounds
end HodgeProofHP
