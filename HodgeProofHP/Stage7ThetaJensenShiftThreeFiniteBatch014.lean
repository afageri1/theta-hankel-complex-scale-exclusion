/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch014

/-! Exact signed weight and batch integral certificates, batch 14 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch014Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (26941 / 250000000000 : ℝ)
  | 1 => (10931 / 100000000000 : ℝ)
  | 2 => (6929 / 62500000000 : ℝ)
  | 3 => (56213 / 500000000000 : ℝ)
  | 4 => (56997 / 500000000000 : ℝ)
  | 5 => (115569 / 1000000000000 : ℝ)
  | 6 => (117151 / 1000000000000 : ℝ)
  | 7 => (118739 / 1000000000000 : ℝ)
  | 8 => (30083 / 250000000000 : ℝ)
  | 9 => (121931 / 1000000000000 : ℝ)
  | 10 => (61767 / 500000000000 : ℝ)
  | 11 => (125143 / 1000000000000 : ℝ)
  | 12 => (25351 / 200000000000 : ℝ)
  | 13 => (128371 / 1000000000000 : ℝ)
  | 14 => (129991 / 1000000000000 : ℝ)
  | 15 => (131613 / 1000000000000 : ℝ)
  | 16 => (66619 / 500000000000 : ℝ)
  | 17 => (8429 / 62500000000 : ℝ)
  | 18 => (136493 / 1000000000000 : ℝ)
  | 19 => (69061 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch014Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (109311 / 1000000000000 : ℝ)
  | 1 => (22173 / 200000000000 : ℝ)
  | 2 => (112427 / 1000000000000 : ℝ)
  | 3 => (22799 / 200000000000 : ℝ)
  | 4 => (11557 / 100000000000 : ℝ)
  | 5 => (3661 / 31250000000 : ℝ)
  | 6 => (5937 / 50000000000 : ℝ)
  | 7 => (120333 / 1000000000000 : ℝ)
  | 8 => (30483 / 250000000000 : ℝ)
  | 9 => (24707 / 200000000000 : ℝ)
  | 10 => (15643 / 125000000000 : ℝ)
  | 11 => (31689 / 250000000000 : ℝ)
  | 12 => (32093 / 250000000000 : ℝ)
  | 13 => (16249 / 125000000000 : ℝ)
  | 14 => (65807 / 500000000000 : ℝ)
  | 15 => (133239 / 1000000000000 : ℝ)
  | 16 => (26973 / 200000000000 : ℝ)
  | 17 => (68247 / 500000000000 : ℝ)
  | 18 => (138123 / 1000000000000 : ℝ)
  | 19 => (139753 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch014Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((280 : ℝ) + (j.val : ℝ)) / 1600)
      (((280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch014Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch014Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((280 : ℝ) + (j.val : ℝ)) / 1600)
    (((280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch014Neg100WeightLower j.val) (hpThetaShiftThreeBatch014Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch014Neg100WeightLower, hpThetaShiftThreeBatch014Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch014Neg100_integral_bounds :
    (1992687 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (2042457 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch014Lower hpThetaJensenCellsBatch014Upper
    hpThetaShiftThreeBatch014Neg100WeightLower hpThetaShiftThreeBatch014Neg100WeightUpper hpThetaJensenCellsBatch014_bounds hpThetaShiftThreeBatch014Neg100_weight_bounds
  have hl : (1992687 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch014Lower j * hpThetaShiftThreeBatch014Neg100WeightLower j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftThreeBatch014Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftThreeBatch014Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch014Lower j * hpThetaShiftThreeBatch014Neg100WeightUpper j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftThreeBatch014Neg100WeightUpper j) / 1600) ≤ (2042457 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftThreeBatch014Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (280 : ℝ) / 1600 = 14 / 80 by norm_num,
    show ((280 : ℝ) + 20) / 1600 = (14 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch014Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (17759 / 125000000000 : ℝ)
  | 1 => (144523 / 1000000000000 : ℝ)
  | 2 => (147001 / 1000000000000 : ℝ)
  | 3 => (74753 / 500000000000 : ℝ)
  | 4 => (152039 / 1000000000000 : ℝ)
  | 5 => (773 / 5000000000 : ℝ)
  | 6 => (157187 / 1000000000000 : ℝ)
  | 7 => (159803 / 1000000000000 : ℝ)
  | 8 => (32489 / 200000000000 : ℝ)
  | 9 => (33023 / 200000000000 : ℝ)
  | 10 => (167813 / 1000000000000 : ℝ)
  | 11 => (170537 / 1000000000000 : ℝ)
  | 12 => (173289 / 1000000000000 : ℝ)
  | 13 => (176069 / 1000000000000 : ℝ)
  | 14 => (1431 / 8000000000 : ℝ)
  | 15 => (181709 / 1000000000000 : ℝ)
  | 16 => (184569 / 1000000000000 : ℝ)
  | 17 => (187457 / 1000000000000 : ℝ)
  | 18 => (190371 / 1000000000000 : ℝ)
  | 19 => (193313 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch014Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (36131 / 250000000000 : ℝ)
  | 1 => (73501 / 500000000000 : ℝ)
  | 2 => (149507 / 1000000000000 : ℝ)
  | 3 => (3801 / 25000000000 : ℝ)
  | 4 => (154601 / 1000000000000 : ℝ)
  | 5 => (39297 / 250000000000 : ℝ)
  | 6 => (39951 / 250000000000 : ℝ)
  | 7 => (81223 / 500000000000 : ℝ)
  | 8 => (41279 / 250000000000 : ℝ)
  | 9 => (83907 / 500000000000 : ℝ)
  | 10 => (85269 / 500000000000 : ℝ)
  | 11 => (17329 / 100000000000 : ℝ)
  | 12 => (17607 / 100000000000 : ℝ)
  | 13 => (44719 / 250000000000 : ℝ)
  | 14 => (18171 / 100000000000 : ℝ)
  | 15 => (18457 / 100000000000 : ℝ)
  | 16 => (93729 / 500000000000 : ℝ)
  | 17 => (47593 / 250000000000 : ℝ)
  | 18 => (96657 / 500000000000 : ℝ)
  | 19 => (98141 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch014Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((280 : ℝ) + (j.val : ℝ)) / 1600)
      (((280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch014Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch014Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((280 : ℝ) + (j.val : ℝ)) / 1600)
    (((280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch014Neg70WeightLower j.val) (hpThetaShiftThreeBatch014Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch014Neg70WeightLower, hpThetaShiftThreeBatch014Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch014Neg70_integral_bounds :
    (2707691 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (556823 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch014Lower hpThetaJensenCellsBatch014Upper
    hpThetaShiftThreeBatch014Neg70WeightLower hpThetaShiftThreeBatch014Neg70WeightUpper hpThetaJensenCellsBatch014_bounds hpThetaShiftThreeBatch014Neg70_weight_bounds
  have hl : (2707691 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch014Lower j * hpThetaShiftThreeBatch014Neg70WeightLower j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftThreeBatch014Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftThreeBatch014Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch014Lower j * hpThetaShiftThreeBatch014Neg70WeightUpper j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftThreeBatch014Neg70WeightUpper j) / 1600) ≤ (556823 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftThreeBatch014Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (280 : ℝ) / 1600 = 14 / 80 by norm_num,
    show ((280 : ℝ) + 20) / 1600 = (14 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch014Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (173971 / 1000000000000 : ℝ)
  | 1 => (44323 / 250000000000 : ℝ)
  | 2 => (180661 / 1000000000000 : ℝ)
  | 3 => (92039 / 500000000000 : ℝ)
  | 4 => (23443 / 125000000000 : ℝ)
  | 5 => (95529 / 500000000000 : ℝ)
  | 6 => (194621 / 1000000000000 : ℝ)
  | 7 => (198233 / 1000000000000 : ℝ)
  | 8 => (25237 / 125000000000 : ℝ)
  | 9 => (205609 / 1000000000000 : ℝ)
  | 10 => (52343 / 250000000000 : ℝ)
  | 11 => (106593 / 500000000000 : ℝ)
  | 12 => (54263 / 250000000000 : ℝ)
  | 13 => (22097 / 100000000000 : ℝ)
  | 14 => (11247 / 50000000000 : ℝ)
  | 15 => (114481 / 500000000000 : ℝ)
  | 16 => (233037 / 1000000000000 : ℝ)
  | 17 => (47433 / 200000000000 : ℝ)
  | 18 => (60337 / 250000000000 : ℝ)
  | 19 => (15349 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch014Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (177293 / 1000000000000 : ℝ)
  | 1 => (90331 / 500000000000 : ℝ)
  | 2 => (184079 / 1000000000000 : ℝ)
  | 3 => (37509 / 200000000000 : ℝ)
  | 4 => (191059 / 1000000000000 : ℝ)
  | 5 => (97311 / 500000000000 : ℝ)
  | 6 => (99117 / 500000000000 : ℝ)
  | 7 => (201897 / 1000000000000 : ℝ)
  | 8 => (20561 / 100000000000 : ℝ)
  | 9 => (209373 / 1000000000000 : ℝ)
  | 10 => (213187 / 1000000000000 : ℝ)
  | 11 => (217053 / 1000000000000 : ℝ)
  | 12 => (220971 / 1000000000000 : ℝ)
  | 13 => (224941 / 1000000000000 : ℝ)
  | 14 => (228963 / 1000000000000 : ℝ)
  | 15 => (116519 / 500000000000 : ℝ)
  | 16 => (118583 / 500000000000 : ℝ)
  | 17 => (241349 / 1000000000000 : ℝ)
  | 18 => (49117 / 200000000000 : ℝ)
  | 19 => (1999 / 8000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch014Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((280 : ℝ) + (j.val : ℝ)) / 1600)
      (((280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch014Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch014Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((280 : ℝ) + (j.val : ℝ)) / 1600)
    (((280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch014Neg45WeightLower j.val) (hpThetaShiftThreeBatch014Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch014Neg45WeightLower, hpThetaShiftThreeBatch014Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch014Neg45_integral_bounds :
    (675807 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (1740583 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch014Lower hpThetaJensenCellsBatch014Upper
    hpThetaShiftThreeBatch014Neg45WeightLower hpThetaShiftThreeBatch014Neg45WeightUpper hpThetaJensenCellsBatch014_bounds hpThetaShiftThreeBatch014Neg45_weight_bounds
  have hl : (675807 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch014Lower j * hpThetaShiftThreeBatch014Neg45WeightLower j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftThreeBatch014Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftThreeBatch014Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch014Lower j * hpThetaShiftThreeBatch014Neg45WeightUpper j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftThreeBatch014Neg45WeightUpper j) / 1600) ≤ (1740583 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftThreeBatch014Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (280 : ℝ) / 1600 = 14 / 80 by norm_num,
    show ((280 : ℝ) + 20) / 1600 = (14 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch014Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (100869 / 500000000000 : ℝ)
  | 1 => (205837 / 1000000000000 : ℝ)
  | 2 => (105001 / 500000000000 : ℝ)
  | 3 => (107117 / 500000000000 : ℝ)
  | 4 => (109267 / 500000000000 : ℝ)
  | 5 => (111451 / 500000000000 : ℝ)
  | 6 => (227339 / 1000000000000 : ℝ)
  | 7 => (231847 / 1000000000000 : ℝ)
  | 8 => (9457 / 40000000000 : ℝ)
  | 9 => (9643 / 40000000000 : ℝ)
  | 10 => (122899 / 500000000000 : ℝ)
  | 11 => (250593 / 1000000000000 : ℝ)
  | 12 => (255463 / 1000000000000 : ℝ)
  | 13 => (32551 / 125000000000 : ℝ)
  | 14 => (66357 / 250000000000 : ℝ)
  | 15 => (10821 / 40000000000 : ℝ)
  | 16 => (2757 / 10000000000 : ℝ)
  | 17 => (35119 / 125000000000 : ℝ)
  | 18 => (286283 / 1000000000000 : ℝ)
  | 19 => (58339 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch014Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (102919 / 500000000000 : ℝ)
  | 1 => (210003 / 1000000000000 : ℝ)
  | 2 => (42847 / 200000000000 : ℝ)
  | 3 => (43707 / 200000000000 : ℝ)
  | 4 => (222903 / 1000000000000 : ℝ)
  | 5 => (11367 / 50000000000 : ℝ)
  | 6 => (28981 / 125000000000 : ℝ)
  | 7 => (118213 / 500000000000 : ℝ)
  | 8 => (60269 / 250000000000 : ℝ)
  | 9 => (245799 / 1000000000000 : ℝ)
  | 10 => (125297 / 500000000000 : ℝ)
  | 11 => (31933 / 125000000000 : ℝ)
  | 12 => (260409 / 1000000000000 : ℝ)
  | 13 => (265429 / 1000000000000 : ℝ)
  | 14 => (135263 / 500000000000 : ℝ)
  | 15 => (275701 / 1000000000000 : ℝ)
  | 16 => (280953 / 1000000000000 : ℝ)
  | 17 => (71571 / 250000000000 : ℝ)
  | 18 => (18231 / 62500000000 : ℝ)
  | 19 => (74297 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch014Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((280 : ℝ) + (j.val : ℝ)) / 1600)
      (((280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch014Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch014Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((280 : ℝ) + (j.val : ℝ)) / 1600)
    (((280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch014Neg25WeightLower j.val) (hpThetaShiftThreeBatch014Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch014Neg25WeightLower, hpThetaShiftThreeBatch014Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch014Neg25_integral_bounds :
    (1983803 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (818541 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch014Lower hpThetaJensenCellsBatch014Upper
    hpThetaShiftThreeBatch014Neg25WeightLower hpThetaShiftThreeBatch014Neg25WeightUpper hpThetaJensenCellsBatch014_bounds hpThetaShiftThreeBatch014Neg25_weight_bounds
  have hl : (1983803 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch014Lower j * hpThetaShiftThreeBatch014Neg25WeightLower j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftThreeBatch014Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftThreeBatch014Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch014Lower j * hpThetaShiftThreeBatch014Neg25WeightUpper j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftThreeBatch014Neg25WeightUpper j) / 1600) ≤ (818541 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftThreeBatch014Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (280 : ℝ) / 1600 = 14 / 80 by norm_num,
    show ((280 : ℝ) + 20) / 1600 = (14 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch014Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch014Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch014Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch014Neg25_integral_bounds
end HodgeProofHP
