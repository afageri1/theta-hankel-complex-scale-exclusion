/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch003

/-! Exact signed weight and batch integral certificates, batch 3 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch003Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (19739 / 125000000000 : ℝ)
  | 1 => (168461 / 1000000000000 : ℝ)
  | 2 => (179517 / 1000000000000 : ℝ)
  | 3 => (38219 / 200000000000 : ℝ)
  | 4 => (20321 / 100000000000 : ℝ)
  | 5 => (53969 / 250000000000 : ℝ)
  | 6 => (229109 / 1000000000000 : ℝ)
  | 7 => (242923 / 1000000000000 : ℝ)
  | 8 => (51467 / 200000000000 : ℝ)
  | 9 => (272359 / 1000000000000 : ℝ)
  | 10 => (28801 / 100000000000 : ℝ)
  | 11 => (60861 / 200000000000 : ℝ)
  | 12 => (160629 / 500000000000 : ℝ)
  | 13 => (67777 / 200000000000 : ℝ)
  | 14 => (178601 / 500000000000 : ℝ)
  | 15 => (15049 / 40000000000 : ℝ)
  | 16 => (6187 / 15625000000 : ℝ)
  | 17 => (6507 / 15625000000 : ℝ)
  | 18 => (5471 / 12500000000 : ℝ)
  | 19 => (2873 / 6250000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch003Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (84231 / 500000000000 : ℝ)
  | 1 => (89759 / 500000000000 : ℝ)
  | 2 => (23887 / 125000000000 : ℝ)
  | 3 => (203211 / 1000000000000 : ℝ)
  | 4 => (215877 / 1000000000000 : ℝ)
  | 5 => (22911 / 100000000000 : ℝ)
  | 6 => (60731 / 250000000000 : ℝ)
  | 7 => (32167 / 125000000000 : ℝ)
  | 8 => (6809 / 25000000000 : ℝ)
  | 9 => (288011 / 1000000000000 : ℝ)
  | 10 => (152153 / 500000000000 : ℝ)
  | 11 => (321259 / 1000000000000 : ℝ)
  | 12 => (169443 / 500000000000 : ℝ)
  | 13 => (357203 / 1000000000000 : ℝ)
  | 14 => (188113 / 500000000000 : ℝ)
  | 15 => (395969 / 1000000000000 : ℝ)
  | 16 => (416449 / 1000000000000 : ℝ)
  | 17 => (437681 / 1000000000000 : ℝ)
  | 18 => (459681 / 1000000000000 : ℝ)
  | 19 => (241233 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch003Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((60 : ℝ) + (j.val : ℝ)) / 1600)
      (((60 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch003Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch003Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((60 : ℝ) + (j.val : ℝ)) / 1600)
    (((60 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch003Neg100WeightLower j.val) (hpThetaShiftTwoBatch003Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch003Neg100WeightLower, hpThetaShiftTwoBatch003Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch003Neg100_integral_bounds :
    (6338947 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (1691251 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (60 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch003Lower hpThetaJensenCellsBatch003Upper
    hpThetaShiftTwoBatch003Neg100WeightLower hpThetaShiftTwoBatch003Neg100WeightUpper hpThetaJensenCellsBatch003_bounds hpThetaShiftTwoBatch003Neg100_weight_bounds
  have hl : (6338947 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch003Lower j * hpThetaShiftTwoBatch003Neg100WeightLower j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftTwoBatch003Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftTwoBatch003Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch003Lower j * hpThetaShiftTwoBatch003Neg100WeightUpper j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftTwoBatch003Neg100WeightUpper j) / 1600) ≤ (1691251 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftTwoBatch003Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (60 : ℝ) / 1600 = 3 / 80 by norm_num,
    show ((60 : ℝ) + 20) / 1600 = (3 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch003Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (32061 / 200000000000 : ℝ)
  | 1 => (85551 / 500000000000 : ℝ)
  | 2 => (182427 / 1000000000000 : ℝ)
  | 3 => (24287 / 125000000000 : ℝ)
  | 4 => (103363 / 500000000000 : ℝ)
  | 5 => (219733 / 1000000000000 : ℝ)
  | 6 => (233333 / 1000000000000 : ℝ)
  | 7 => (30943 / 125000000000 : ℝ)
  | 8 => (131191 / 500000000000 : ℝ)
  | 9 => (34733 / 125000000000 : ℝ)
  | 10 => (36751 / 125000000000 : ℝ)
  | 11 => (310831 / 1000000000000 : ℝ)
  | 12 => (328351 / 1000000000000 : ℝ)
  | 13 => (69317 / 200000000000 : ℝ)
  | 14 => (365551 / 1000000000000 : ℝ)
  | 15 => (96317 / 250000000000 : ℝ)
  | 16 => (50719 / 125000000000 : ℝ)
  | 17 => (427023 / 1000000000000 : ℝ)
  | 18 => (224549 / 500000000000 : ℝ)
  | 19 => (117999 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch003Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (171103 / 1000000000000 : ℝ)
  | 1 => (45607 / 250000000000 : ℝ)
  | 2 => (194297 / 1000000000000 : ℝ)
  | 3 => (206727 / 1000000000000 : ℝ)
  | 4 => (109867 / 500000000000 : ℝ)
  | 5 => (116667 / 500000000000 : ℝ)
  | 6 => (49509 / 200000000000 : ℝ)
  | 7 => (262383 / 1000000000000 : ℝ)
  | 8 => (55573 / 200000000000 : ℝ)
  | 9 => (294009 / 1000000000000 : ℝ)
  | 10 => (19427 / 62500000000 : ℝ)
  | 11 => (10261 / 31250000000 : ℝ)
  | 12 => (173293 / 500000000000 : ℝ)
  | 13 => (22847 / 62500000000 : ℝ)
  | 14 => (385269 / 1000000000000 : ℝ)
  | 15 => (405753 / 1000000000000 : ℝ)
  | 16 => (26689 / 62500000000 : ℝ)
  | 17 => (449099 / 1000000000000 : ℝ)
  | 18 => (471997 / 1000000000000 : ℝ)
  | 19 => (495737 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch003Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((60 : ℝ) + (j.val : ℝ)) / 1600)
      (((60 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch003Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch003Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((60 : ℝ) + (j.val : ℝ)) / 1600)
    (((60 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch003Neg65WeightLower j.val) (hpThetaShiftTwoBatch003Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch003Neg65WeightLower, hpThetaShiftTwoBatch003Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch003Neg65_integral_bounds :
    (25301 / 3906250000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (6916587 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (60 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch003Lower hpThetaJensenCellsBatch003Upper
    hpThetaShiftTwoBatch003Neg65WeightLower hpThetaShiftTwoBatch003Neg65WeightUpper hpThetaJensenCellsBatch003_bounds hpThetaShiftTwoBatch003Neg65_weight_bounds
  have hl : (25301 / 3906250000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch003Lower j * hpThetaShiftTwoBatch003Neg65WeightLower j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftTwoBatch003Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftTwoBatch003Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch003Lower j * hpThetaShiftTwoBatch003Neg65WeightUpper j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftTwoBatch003Neg65WeightUpper j) / 1600) ≤ (6916587 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftTwoBatch003Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (60 : ℝ) / 1600 = 3 / 80 by norm_num,
    show ((60 : ℝ) + 20) / 1600 = (3 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch003Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2021 / 12500000000 : ℝ)
  | 1 => (8631 / 50000000000 : ℝ)
  | 2 => (1841 / 10000000000 : ℝ)
  | 3 => (196137 / 1000000000000 : ℝ)
  | 4 => (208749 / 1000000000000 : ℝ)
  | 5 => (221951 / 1000000000000 : ℝ)
  | 6 => (58941 / 250000000000 : ℝ)
  | 7 => (250203 / 1000000000000 : ℝ)
  | 8 => (265287 / 1000000000000 : ℝ)
  | 9 => (140517 / 500000000000 : ℝ)
  | 10 => (148731 / 500000000000 : ℝ)
  | 11 => (31459 / 100000000000 : ℝ)
  | 12 => (332437 / 1000000000000 : ℝ)
  | 13 => (175511 / 500000000000 : ℝ)
  | 14 => (370363 / 1000000000000 : ℝ)
  | 15 => (390481 / 1000000000000 : ℝ)
  | 16 => (205697 / 500000000000 : ℝ)
  | 17 => (216561 / 500000000000 : ℝ)
  | 18 => (91137 / 200000000000 : ℝ)
  | 19 => (479103 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch003Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (172621 / 1000000000000 : ℝ)
  | 1 => (184101 / 1000000000000 : ℝ)
  | 2 => (98069 / 500000000000 : ℝ)
  | 3 => (167 / 800000000 : ℝ)
  | 4 => (867 / 3906250000 : ℝ)
  | 5 => (47153 / 200000000000 : ℝ)
  | 6 => (62551 / 250000000000 : ℝ)
  | 7 => (33161 / 125000000000 : ℝ)
  | 8 => (56207 / 200000000000 : ℝ)
  | 9 => (297463 / 1000000000000 : ℝ)
  | 10 => (314591 / 1000000000000 : ℝ)
  | 11 => (166219 / 500000000000 : ℝ)
  | 12 => (351023 / 1000000000000 : ℝ)
  | 13 => (92591 / 250000000000 : ℝ)
  | 14 => (195241 / 500000000000 : ℝ)
  | 15 => (82279 / 200000000000 : ℝ)
  | 16 => (433123 / 1000000000000 : ℝ)
  | 17 => (227843 / 500000000000 : ℝ)
  | 18 => (3743 / 7812500000 : ℝ)
  | 19 => (503397 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch003Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((60 : ℝ) + (j.val : ℝ)) / 1600)
      (((60 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch003Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch003Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((60 : ℝ) + (j.val : ℝ)) / 1600)
    (((60 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch003Neg45WeightLower j.val) (hpThetaShiftTwoBatch003Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch003Neg45WeightLower, hpThetaShiftTwoBatch003Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch003Neg45_integral_bounds :
    (1639157 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (3501971 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (60 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch003Lower hpThetaJensenCellsBatch003Upper
    hpThetaShiftTwoBatch003Neg45WeightLower hpThetaShiftTwoBatch003Neg45WeightUpper hpThetaJensenCellsBatch003_bounds hpThetaShiftTwoBatch003Neg45_weight_bounds
  have hl : (1639157 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch003Lower j * hpThetaShiftTwoBatch003Neg45WeightLower j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftTwoBatch003Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftTwoBatch003Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch003Lower j * hpThetaShiftTwoBatch003Neg45WeightUpper j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftTwoBatch003Neg45WeightUpper j) / 1600) ≤ (3501971 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftTwoBatch003Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (60 : ℝ) / 1600 = 3 / 80 by norm_num,
    show ((60 : ℝ) + 20) / 1600 = (3 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch003Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (163061 / 1000000000000 : ℝ)
  | 1 => (2721 / 15625000000 : ℝ)
  | 2 => (9289 / 50000000000 : ℝ)
  | 3 => (98993 / 500000000000 : ℝ)
  | 4 => (10539 / 50000000000 : ℝ)
  | 5 => (224181 / 1000000000000 : ℝ)
  | 6 => (119103 / 500000000000 : ℝ)
  | 7 => (2023 / 8000000000 : ℝ)
  | 8 => (268207 / 1000000000000 : ℝ)
  | 9 => (14211 / 50000000000 : ℝ)
  | 10 => (60187 / 200000000000 : ℝ)
  | 11 => (31837 / 100000000000 : ℝ)
  | 12 => (336547 / 1000000000000 : ℝ)
  | 13 => (71097 / 200000000000 : ℝ)
  | 14 => (75041 / 200000000000 : ℝ)
  | 15 => (395727 / 1000000000000 : ℝ)
  | 16 => (26067 / 62500000000 : ℝ)
  | 17 => (439261 / 1000000000000 : ℝ)
  | 18 => (462317 / 1000000000000 : ℝ)
  | 19 => (486259 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch003Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (34829 / 200000000000 : ℝ)
  | 1 => (185781 / 1000000000000 : ℝ)
  | 2 => (197987 / 1000000000000 : ℝ)
  | 3 => (210781 / 1000000000000 : ℝ)
  | 4 => (112091 / 500000000000 : ℝ)
  | 5 => (238207 / 1000000000000 : ℝ)
  | 6 => (63219 / 250000000000 : ℝ)
  | 7 => (16763 / 62500000000 : ℝ)
  | 8 => (284221 / 1000000000000 : ℝ)
  | 9 => (37617 / 125000000000 : ℝ)
  | 10 => (318371 / 1000000000000 : ℝ)
  | 11 => (84137 / 250000000000 : ℝ)
  | 12 => (177743 / 500000000000 : ℝ)
  | 13 => (187603 / 500000000000 : ℝ)
  | 14 => (24733 / 62500000000 : ℝ)
  | 15 => (417073 / 1000000000000 : ℝ)
  | 16 => (219631 / 500000000000 : ℝ)
  | 17 => (231159 / 500000000000 : ℝ)
  | 18 => (24313 / 50000000000 : ℝ)
  | 19 => (63889 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch003Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((60 : ℝ) + (j.val : ℝ)) / 1600)
      (((60 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch003Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch003Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((60 : ℝ) + (j.val : ℝ)) / 1600)
    (((60 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch003Neg25WeightLower j.val) (hpThetaShiftTwoBatch003Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch003Neg25WeightLower, hpThetaShiftTwoBatch003Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch003Neg25_integral_bounds :
    (829583 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (7091819 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (60 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch003Lower hpThetaJensenCellsBatch003Upper
    hpThetaShiftTwoBatch003Neg25WeightLower hpThetaShiftTwoBatch003Neg25WeightUpper hpThetaJensenCellsBatch003_bounds hpThetaShiftTwoBatch003Neg25_weight_bounds
  have hl : (829583 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch003Lower j * hpThetaShiftTwoBatch003Neg25WeightLower j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftTwoBatch003Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftTwoBatch003Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch003Lower j * hpThetaShiftTwoBatch003Neg25WeightUpper j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftTwoBatch003Neg25WeightUpper j) / 1600) ≤ (7091819 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftTwoBatch003Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (60 : ℝ) / 1600 = 3 / 80 by norm_num,
    show ((60 : ℝ) + 20) / 1600 = (3 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch003Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch003Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch003Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch003Neg25_integral_bounds
end HodgeProofHP
