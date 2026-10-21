/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch008

/-! Exact signed weight and batch integral certificates, batch 8 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch008Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (6008597 / 1000000000000 : ℝ)
  | 1 => (6132579 / 1000000000000 : ℝ)
  | 2 => (1251581 / 200000000000 : ℝ)
  | 3 => (1596141 / 250000000000 : ℝ)
  | 4 => (3256273 / 500000000000 : ℝ)
  | 5 => (1660459 / 250000000000 : ℝ)
  | 6 => (3386211 / 500000000000 : ℝ)
  | 7 => (6904289 / 1000000000000 : ℝ)
  | 8 => (439839 / 62500000000 : ℝ)
  | 9 => (717181 / 100000000000 : ℝ)
  | 10 => (7307433 / 1000000000000 : ℝ)
  | 11 => (3722137 / 500000000000 : ℝ)
  | 12 => (3791159 / 500000000000 : ℝ)
  | 13 => (1544309 / 200000000000 : ℝ)
  | 14 => (7861937 / 1000000000000 : ℝ)
  | 15 => (4001737 / 500000000000 : ℝ)
  | 16 => (8146137 / 1000000000000 : ℝ)
  | 17 => (518119 / 62500000000 : ℝ)
  | 18 => (8434753 / 1000000000000 : ℝ)
  | 19 => (8580663 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch008Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (306629 / 50000000000 : ℝ)
  | 1 => (3128953 / 500000000000 : ℝ)
  | 2 => (1276913 / 200000000000 : ℝ)
  | 3 => (6512547 / 1000000000000 : ℝ)
  | 4 => (6641837 / 1000000000000 : ℝ)
  | 5 => (6772423 / 1000000000000 : ℝ)
  | 6 => (690429 / 100000000000 : ℝ)
  | 7 => (281497 / 40000000000 : ℝ)
  | 8 => (7171811 / 1000000000000 : ℝ)
  | 9 => (3653717 / 500000000000 : ℝ)
  | 10 => (297771 / 40000000000 : ℝ)
  | 11 => (7582319 / 1000000000000 : ℝ)
  | 12 => (3860773 / 500000000000 : ℝ)
  | 13 => (3930969 / 500000000000 : ℝ)
  | 14 => (320139 / 40000000000 : ℝ)
  | 15 => (4073069 / 500000000000 : ℝ)
  | 16 => (1657981 / 200000000000 : ℝ)
  | 17 => (4217377 / 500000000000 : ℝ)
  | 18 => (1072583 / 125000000000 : ℝ)
  | 19 => (872761 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch008Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((160 : ℝ) + (j.val : ℝ)) / 1600)
      (((160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch008Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch008Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((160 : ℝ) + (j.val : ℝ)) / 1600)
    (((160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch008Neg100WeightLower j.val) (hpThetaShiftTwoBatch008Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch008Neg100WeightLower, hpThetaShiftTwoBatch008Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch008Neg100_integral_bounds :
    (36249677 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (149362457 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch008Lower hpThetaJensenCellsBatch008Upper
    hpThetaShiftTwoBatch008Neg100WeightLower hpThetaShiftTwoBatch008Neg100WeightUpper hpThetaJensenCellsBatch008_bounds hpThetaShiftTwoBatch008Neg100_weight_bounds
  have hl : (36249677 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch008Lower j * hpThetaShiftTwoBatch008Neg100WeightLower j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftTwoBatch008Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftTwoBatch008Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch008Lower j * hpThetaShiftTwoBatch008Neg100WeightUpper j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftTwoBatch008Neg100WeightUpper j) / 1600) ≤ (149362457 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftTwoBatch008Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (160 : ℝ) / 1600 = 8 / 80 by norm_num,
    show ((160 : ℝ) + 20) / 1600 = (8 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch008Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (6782871 / 1000000000000 : ℝ)
  | 1 => (3467533 / 500000000000 : ℝ)
  | 2 => (7089431 / 1000000000000 : ℝ)
  | 3 => (3622987 / 500000000000 : ℝ)
  | 4 => (74047 / 10000000000 : ℝ)
  | 5 => (472851 / 62500000000 : ℝ)
  | 6 => (7728727 / 1000000000000 : ℝ)
  | 7 => (7894037 / 1000000000000 : ℝ)
  | 8 => (503847 / 62500000000 : ℝ)
  | 9 => (2057819 / 250000000000 : ℝ)
  | 10 => (8403211 / 1000000000000 : ℝ)
  | 11 => (8577361 / 1000000000000 : ℝ)
  | 12 => (8753729 / 1000000000000 : ℝ)
  | 13 => (8932317 / 1000000000000 : ℝ)
  | 14 => (9113127 / 1000000000000 : ℝ)
  | 15 => (58101 / 6250000000 : ℝ)
  | 16 => (9481417 / 1000000000000 : ℝ)
  | 17 => (9668897 / 1000000000000 : ℝ)
  | 18 => (4929301 / 500000000000 : ℝ)
  | 19 => (10050529 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch008Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (6935067 / 1000000000000 : ℝ)
  | 1 => (886179 / 125000000000 : ℝ)
  | 2 => (289839 / 40000000000 : ℝ)
  | 3 => (7404701 / 1000000000000 : ℝ)
  | 4 => (7565617 / 1000000000000 : ℝ)
  | 5 => (966091 / 125000000000 : ℝ)
  | 6 => (3947019 / 500000000000 : ℝ)
  | 7 => (8061553 / 1000000000000 : ℝ)
  | 8 => (8231277 / 1000000000000 : ℝ)
  | 9 => (2100803 / 250000000000 : ℝ)
  | 10 => (4288681 / 500000000000 : ℝ)
  | 11 => (875373 / 100000000000 : ℝ)
  | 12 => (4466159 / 500000000000 : ℝ)
  | 13 => (1139141 / 125000000000 : ℝ)
  | 14 => (9296161 / 1000000000000 : ℝ)
  | 15 => (4740709 / 500000000000 : ℝ)
  | 16 => (4834449 / 500000000000 : ℝ)
  | 17 => (9858603 / 1000000000000 : ℝ)
  | 18 => (1005053 / 100000000000 : ℝ)
  | 19 => (10244679 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch008Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((160 : ℝ) + (j.val : ℝ)) / 1600)
      (((160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch008Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch008Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((160 : ℝ) + (j.val : ℝ)) / 1600)
    (((160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch008Neg65WeightLower j.val) (hpThetaShiftTwoBatch008Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch008Neg65WeightLower, hpThetaShiftTwoBatch008Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch008Neg65_integral_bounds :
    (83416801 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (172190699 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch008Lower hpThetaJensenCellsBatch008Upper
    hpThetaShiftTwoBatch008Neg65WeightLower hpThetaShiftTwoBatch008Neg65WeightUpper hpThetaJensenCellsBatch008_bounds hpThetaShiftTwoBatch008Neg65_weight_bounds
  have hl : (83416801 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch008Lower j * hpThetaShiftTwoBatch008Neg65WeightLower j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftTwoBatch008Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftTwoBatch008Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch008Lower j * hpThetaShiftTwoBatch008Neg65WeightUpper j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftTwoBatch008Neg65WeightUpper j) / 1600) ≤ (172190699 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftTwoBatch008Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (160 : ℝ) / 1600 = 8 / 80 by norm_num,
    show ((160 : ℝ) + 20) / 1600 = (8 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch008Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (226381 / 31250000000 : ℝ)
  | 1 => (7413463 / 1000000000000 : ℝ)
  | 2 => (7585419 / 1000000000000 : ℝ)
  | 3 => (3880039 / 500000000000 : ℝ)
  | 4 => (3968729 / 500000000000 : ℝ)
  | 5 => (8117577 / 1000000000000 : ℝ)
  | 6 => (8300453 / 1000000000000 : ℝ)
  | 7 => (1060763 / 125000000000 : ℝ)
  | 8 => (4337273 / 500000000000 : ℝ)
  | 9 => (2216449 / 250000000000 : ℝ)
  | 10 => (283121 / 31250000000 : ℝ)
  | 11 => (925679 / 100000000000 : ℝ)
  | 12 => (4728283 / 500000000000 : ℝ)
  | 13 => (1931843 / 200000000000 : ℝ)
  | 14 => (9864753 / 1000000000000 : ℝ)
  | 15 => (2518299 / 250000000000 : ℝ)
  | 16 => (10284559 / 1000000000000 : ℝ)
  | 17 => (1312357 / 125000000000 : ℝ)
  | 18 => (10716101 / 1000000000000 : ℝ)
  | 19 => (10936309 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch008Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (926683 / 125000000000 : ℝ)
  | 1 => (379271 / 50000000000 : ℝ)
  | 2 => (7760079 / 1000000000000 : ℝ)
  | 3 => (7937459 / 1000000000000 : ℝ)
  | 4 => (4058789 / 500000000000 : ℝ)
  | 5 => (4150227 / 500000000000 : ℝ)
  | 6 => (1697221 / 200000000000 : ℝ)
  | 7 => (8674547 / 1000000000000 : ℝ)
  | 8 => (8865797 / 1000000000000 : ℝ)
  | 9 => (9059873 / 1000000000000 : ℝ)
  | 10 => (9256791 / 1000000000000 : ℝ)
  | 11 => (9456567 / 1000000000000 : ℝ)
  | 12 => (603701 / 62500000000 : ℝ)
  | 13 => (4932377 / 500000000000 : ℝ)
  | 14 => (10073197 / 1000000000000 : ℝ)
  | 15 => (128557 / 12500000000 : ℝ)
  | 16 => (10498857 / 1000000000000 : ℝ)
  | 17 => (5358051 / 500000000000 : ℝ)
  | 18 => (1093631 / 100000000000 : ℝ)
  | 19 => (5579747 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch008Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((160 : ℝ) + (j.val : ℝ)) / 1600)
      (((160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch008Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch008Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((160 : ℝ) + (j.val : ℝ)) / 1600)
    (((160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch008Neg45WeightLower j.val) (hpThetaShiftTwoBatch008Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch008Neg45WeightLower, hpThetaShiftTwoBatch008Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch008Neg45_integral_bounds :
    (7196961 / 40000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (18588489 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch008Lower hpThetaJensenCellsBatch008Upper
    hpThetaShiftTwoBatch008Neg45WeightLower hpThetaShiftTwoBatch008Neg45WeightUpper hpThetaJensenCellsBatch008_bounds hpThetaShiftTwoBatch008Neg45_weight_bounds
  have hl : (7196961 / 40000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch008Lower j * hpThetaShiftTwoBatch008Neg45WeightLower j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftTwoBatch008Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftTwoBatch008Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch008Lower j * hpThetaShiftTwoBatch008Neg45WeightUpper j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftTwoBatch008Neg45WeightUpper j) / 1600) ≤ (18588489 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftTwoBatch008Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (160 : ℝ) / 1600 = 8 / 80 by norm_num,
    show ((160 : ℝ) + 20) / 1600 = (8 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch008Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3859721 / 500000000000 : ℝ)
  | 1 => (7906497 / 1000000000000 : ℝ)
  | 2 => (8096781 / 1000000000000 : ℝ)
  | 3 => (4145163 / 500000000000 : ℝ)
  | 4 => (2121791 / 250000000000 : ℝ)
  | 5 => (347493 / 40000000000 : ℝ)
  | 6 => (8890841 / 1000000000000 : ℝ)
  | 7 => (568609 / 62500000000 : ℝ)
  | 8 => (290877 / 31250000000 : ℝ)
  | 9 => (9521833 / 1000000000000 : ℝ)
  | 10 => (9739081 / 1000000000000 : ℝ)
  | 11 => (4979921 / 500000000000 : ℝ)
  | 12 => (636509 / 62500000000 : ℝ)
  | 13 => (520601 / 50000000000 : ℝ)
  | 14 => (21287 / 2000000000 : ℝ)
  | 15 => (2175723 / 200000000000 : ℝ)
  | 16 => (11117397 / 1000000000000 : ℝ)
  | 17 => (2839969 / 250000000000 : ℝ)
  | 18 => (11606083 / 1000000000000 : ℝ)
  | 19 => (741003 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch008Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3953249 / 500000000000 : ℝ)
  | 1 => (4048391 / 500000000000 : ℝ)
  | 2 => (8290327 / 1000000000000 : ℝ)
  | 3 => (1697433 / 200000000000 : ℝ)
  | 4 => (4343663 / 500000000000 : ℝ)
  | 5 => (4445421 / 500000000000 : ℝ)
  | 6 => (1819549 / 200000000000 : ℝ)
  | 7 => (1861613 / 200000000000 : ℝ)
  | 8 => (4760917 / 500000000000 : ℝ)
  | 9 => (4869541 / 500000000000 : ℝ)
  | 10 => (9959843 / 1000000000000 : ℝ)
  | 11 => (2036829 / 200000000000 : ℝ)
  | 12 => (10412021 / 1000000000000 : ℝ)
  | 13 => (10643501 / 1000000000000 : ℝ)
  | 14 => (1359827 / 125000000000 : ℝ)
  | 15 => (5558699 / 500000000000 : ℝ)
  | 16 => (11359877 / 1000000000000 : ℝ)
  | 17 => (2901521 / 250000000000 : ℝ)
  | 18 => (11856049 / 1000000000000 : ℝ)
  | 19 => (12109803 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch008Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((160 : ℝ) + (j.val : ℝ)) / 1600)
      (((160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch008Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch008Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((160 : ℝ) + (j.val : ℝ)) / 1600)
    (((160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch008Neg25WeightLower j.val) (hpThetaShiftTwoBatch008Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch008Neg25WeightLower, hpThetaShiftTwoBatch008Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch008Neg25_integral_bounds :
    (48366981 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (200059371 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch008Lower hpThetaJensenCellsBatch008Upper
    hpThetaShiftTwoBatch008Neg25WeightLower hpThetaShiftTwoBatch008Neg25WeightUpper hpThetaJensenCellsBatch008_bounds hpThetaShiftTwoBatch008Neg25_weight_bounds
  have hl : (48366981 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch008Lower j * hpThetaShiftTwoBatch008Neg25WeightLower j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftTwoBatch008Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftTwoBatch008Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch008Lower j * hpThetaShiftTwoBatch008Neg25WeightUpper j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftTwoBatch008Neg25WeightUpper j) / 1600) ≤ (200059371 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftTwoBatch008Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (160 : ℝ) / 1600 = 8 / 80 by norm_num,
    show ((160 : ℝ) + 20) / 1600 = (8 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch008Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch008Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch008Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch008Neg25_integral_bounds
end HodgeProofHP
