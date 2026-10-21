/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch012

/-! Exact signed weight and batch integral certificates, batch 12 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch012Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4524209 / 250000000000 : ℝ)
  | 1 => (18231697 / 1000000000000 : ℝ)
  | 2 => (9182297 / 500000000000 : ℝ)
  | 3 => (18495453 / 1000000000000 : ℝ)
  | 4 => (18624199 / 1000000000000 : ℝ)
  | 5 => (9375379 / 500000000000 : ℝ)
  | 6 => (9437527 / 500000000000 : ℝ)
  | 7 => (18997009 / 1000000000000 : ℝ)
  | 8 => (9558273 / 500000000000 : ℝ)
  | 9 => (4808397 / 250000000000 : ℝ)
  | 10 => (9674027 / 500000000000 : ℝ)
  | 11 => (19459867 / 1000000000000 : ℝ)
  | 12 => (3913789 / 200000000000 : ℝ)
  | 13 => (19675207 / 1000000000000 : ℝ)
  | 14 => (4944643 / 250000000000 : ℝ)
  | 15 => (9939479 / 500000000000 : ℝ)
  | 16 => (9988141 / 500000000000 : ℝ)
  | 17 => (1003523 / 50000000000 : ℝ)
  | 18 => (157511 / 7812500000 : ℝ)
  | 19 => (10124521 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch012Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (9115849 / 500000000000 : ℝ)
  | 1 => (3672919 / 200000000000 : ℝ)
  | 2 => (9247727 / 500000000000 : ℝ)
  | 3 => (93121 / 5000000000 : ℝ)
  | 4 => (18750759 / 1000000000000 : ℝ)
  | 5 => (3775011 / 200000000000 : ℝ)
  | 6 => (1899701 / 100000000000 : ℝ)
  | 7 => (19116547 / 1000000000000 : ℝ)
  | 8 => (19233589 / 1000000000000 : ℝ)
  | 9 => (3869611 / 200000000000 : ℝ)
  | 10 => (4864967 / 250000000000 : ℝ)
  | 11 => (9784473 / 500000000000 : ℝ)
  | 12 => (2459401 / 125000000000 : ℝ)
  | 13 => (19778573 / 1000000000000 : ℝ)
  | 14 => (19878959 / 1000000000000 : ℝ)
  | 15 => (19976283 / 1000000000000 : ℝ)
  | 16 => (20070461 / 1000000000000 : ℝ)
  | 17 => (20161409 / 1000000000000 : ℝ)
  | 18 => (20249043 / 1000000000000 : ℝ)
  | 19 => (5083319 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch012Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((240 : ℝ) + (j.val : ℝ)) / 1600)
      (((240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch012Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch012Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((240 : ℝ) + (j.val : ℝ)) / 1600)
    (((240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch012Neg100WeightLower j.val) (hpThetaShiftTwoBatch012Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch012Neg100WeightLower, hpThetaShiftTwoBatch012Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch012Neg100_integral_bounds :
    (67832841 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (345078627 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch012Lower hpThetaJensenCellsBatch012Upper
    hpThetaShiftTwoBatch012Neg100WeightLower hpThetaShiftTwoBatch012Neg100WeightUpper hpThetaJensenCellsBatch012_bounds hpThetaShiftTwoBatch012Neg100_weight_bounds
  have hl : (67832841 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch012Lower j * hpThetaShiftTwoBatch012Neg100WeightLower j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftTwoBatch012Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftTwoBatch012Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch012Lower j * hpThetaShiftTwoBatch012Neg100WeightUpper j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftTwoBatch012Neg100WeightUpper j) / 1600) ≤ (345078627 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftTwoBatch012Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (240 : ℝ) / 1600 = 12 / 80 by norm_num,
    show ((240 : ℝ) + 20) / 1600 = (12 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch012Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1022359 / 40000000000 : ℝ)
  | 1 => (25862093 / 1000000000000 : ℝ)
  | 2 => (5233223 / 200000000000 : ℝ)
  | 3 => (5294199 / 200000000000 : ℝ)
  | 4 => (26776689 / 1000000000000 : ℝ)
  | 5 => (541663 / 20000000000 : ℝ)
  | 6 => (6847583 / 250000000000 : ℝ)
  | 7 => (13849093 / 500000000000 : ℝ)
  | 8 => (14003333 / 500000000000 : ℝ)
  | 9 => (28315721 / 1000000000000 : ℝ)
  | 10 => (28625301 / 1000000000000 : ℝ)
  | 11 => (5787071 / 200000000000 : ℝ)
  | 12 => (3655729 / 125000000000 : ℝ)
  | 13 => (29556679 / 1000000000000 : ℝ)
  | 14 => (29867843 / 1000000000000 : ℝ)
  | 15 => (3017927 / 100000000000 : ℝ)
  | 16 => (3811363 / 125000000000 : ℝ)
  | 17 => (3080269 / 100000000000 : ℝ)
  | 18 => (31114571 / 1000000000000 : ℝ)
  | 19 => (31426489 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch012Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (12931047 / 500000000000 : ℝ)
  | 1 => (6541529 / 250000000000 : ℝ)
  | 2 => (6617749 / 250000000000 : ℝ)
  | 3 => (2677669 / 100000000000 : ℝ)
  | 4 => (27083151 / 1000000000000 : ℝ)
  | 5 => (27390333 / 1000000000000 : ℝ)
  | 6 => (27698187 / 1000000000000 : ℝ)
  | 7 => (28006667 / 1000000000000 : ℝ)
  | 8 => (14157861 / 500000000000 : ℝ)
  | 9 => (14312651 / 500000000000 : ℝ)
  | 10 => (7233839 / 250000000000 : ℝ)
  | 11 => (29245833 / 1000000000000 : ℝ)
  | 12 => (738917 / 25000000000 : ℝ)
  | 13 => (7466961 / 250000000000 : ℝ)
  | 14 => (30179271 / 1000000000000 : ℝ)
  | 15 => (6098181 / 200000000000 : ℝ)
  | 16 => (30802691 / 1000000000000 : ℝ)
  | 17 => (7778643 / 250000000000 : ℝ)
  | 18 => (3142649 / 100000000000 : ℝ)
  | 19 => (31738387 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch012Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((240 : ℝ) + (j.val : ℝ)) / 1600)
      (((240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch012Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch012Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((240 : ℝ) + (j.val : ℝ)) / 1600)
    (((240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch012Neg65WeightLower j.val) (hpThetaShiftTwoBatch012Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch012Neg65WeightLower, hpThetaShiftTwoBatch012Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch012Neg65_integral_bounds :
    (100333967 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (256486819 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch012Lower hpThetaJensenCellsBatch012Upper
    hpThetaShiftTwoBatch012Neg65WeightLower hpThetaShiftTwoBatch012Neg65WeightUpper hpThetaJensenCellsBatch012_bounds hpThetaShiftTwoBatch012Neg65_weight_bounds
  have hl : (100333967 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch012Lower j * hpThetaShiftTwoBatch012Neg65WeightLower j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftTwoBatch012Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftTwoBatch012Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch012Lower j * hpThetaShiftTwoBatch012Neg65WeightUpper j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftTwoBatch012Neg65WeightUpper j) / 1600) ≤ (256486819 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftTwoBatch012Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (240 : ℝ) / 1600 = 12 / 80 by norm_num,
    show ((240 : ℝ) + 20) / 1600 = (12 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch012Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (30282429 / 1000000000000 : ℝ)
  | 1 => (7674213 / 250000000000 : ℝ)
  | 2 => (3889281 / 125000000000 : ℝ)
  | 3 => (15767299 / 500000000000 : ℝ)
  | 4 => (7989471 / 250000000000 : ℝ)
  | 5 => (32384089 / 1000000000000 : ℝ)
  | 6 => (4101649 / 125000000000 : ℝ)
  | 7 => (16622587 / 500000000000 : ℝ)
  | 8 => (16840007 / 500000000000 : ℝ)
  | 9 => (3411769 / 100000000000 : ℝ)
  | 10 => (17279091 / 500000000000 : ℝ)
  | 11 => (7000293 / 200000000000 : ℝ)
  | 12 => (17723759 / 500000000000 : ℝ)
  | 13 => (7179263 / 200000000000 : ℝ)
  | 14 => (4543479 / 125000000000 : ℝ)
  | 15 => (36802043 / 1000000000000 : ℝ)
  | 16 => (37258923 / 1000000000000 : ℝ)
  | 17 => (7543689 / 200000000000 : ℝ)
  | 18 => (1909029 / 50000000000 : ℝ)
  | 19 => (38645301 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch012Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (30696853 / 1000000000000 : ℝ)
  | 1 => (31114249 / 1000000000000 : ℝ)
  | 2 => (31534599 / 1000000000000 : ℝ)
  | 3 => (6391577 / 200000000000 : ℝ)
  | 4 => (3238409 / 100000000000 : ℝ)
  | 5 => (32813193 / 1000000000000 : ℝ)
  | 6 => (1329807 / 40000000000 : ℝ)
  | 7 => (6736003 / 200000000000 : ℝ)
  | 8 => (34117691 / 1000000000000 : ℝ)
  | 9 => (34558183 / 1000000000000 : ℝ)
  | 10 => (17500733 / 500000000000 : ℝ)
  | 11 => (35447519 / 1000000000000 : ℝ)
  | 12 => (8974079 / 250000000000 : ℝ)
  | 13 => (36347833 / 1000000000000 : ℝ)
  | 14 => (9200511 / 250000000000 : ℝ)
  | 15 => (9314731 / 250000000000 : ℝ)
  | 16 => (18859223 / 500000000000 : ℝ)
  | 17 => (38180581 / 1000000000000 : ℝ)
  | 18 => (19322651 / 500000000000 : ℝ)
  | 19 => (1955629 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch012Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((240 : ℝ) + (j.val : ℝ)) / 1600)
      (((240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch012Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch012Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((240 : ℝ) + (j.val : ℝ)) / 1600)
    (((240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch012Neg45WeightLower j.val) (hpThetaShiftTwoBatch012Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch012Neg45WeightLower, hpThetaShiftTwoBatch012Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch012Neg45_integral_bounds :
    (121124739 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (620489233 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch012Lower hpThetaJensenCellsBatch012Upper
    hpThetaShiftTwoBatch012Neg45WeightLower hpThetaShiftTwoBatch012Neg45WeightUpper hpThetaJensenCellsBatch012_bounds hpThetaShiftTwoBatch012Neg45_weight_bounds
  have hl : (121124739 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch012Lower j * hpThetaShiftTwoBatch012Neg45WeightLower j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftTwoBatch012Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftTwoBatch012Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch012Lower j * hpThetaShiftTwoBatch012Neg45WeightUpper j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftTwoBatch012Neg45WeightUpper j) / 1600) ≤ (620489233 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftTwoBatch012Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (240 : ℝ) / 1600 = 12 / 80 by norm_num,
    show ((240 : ℝ) + 20) / 1600 = (12 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch012Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4418927 / 125000000000 : ℝ)
  | 1 => (35888653 / 1000000000000 : ℝ)
  | 2 => (36431263 / 1000000000000 : ℝ)
  | 3 => (577801 / 15625000000 : ℝ)
  | 4 => (36653 / 976562500 : ℝ)
  | 5 => (7618301 / 200000000000 : ℝ)
  | 6 => (38655779 / 1000000000000 : ℝ)
  | 7 => (4903189 / 125000000000 : ℝ)
  | 8 => (39800719 / 1000000000000 : ℝ)
  | 9 => (8076283 / 200000000000 : ℝ)
  | 10 => (640119 / 15625000000 : ℝ)
  | 11 => (20779669 / 500000000000 : ℝ)
  | 12 => (21078297 / 500000000000 : ℝ)
  | 13 => (21379699 / 500000000000 : ℝ)
  | 14 => (8673553 / 200000000000 : ℝ)
  | 15 => (10995427 / 250000000000 : ℝ)
  | 16 => (44601241 / 1000000000000 : ℝ)
  | 17 => (361811 / 8000000000 : ℝ)
  | 18 => (45857123 / 1000000000000 : ℝ)
  | 19 => (46493497 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch012Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (17944327 / 500000000000 : ℝ)
  | 1 => (1138477 / 31250000000 : ℝ)
  | 2 => (7395853 / 200000000000 : ℝ)
  | 3 => (37532673 / 1000000000000 : ℝ)
  | 4 => (19045753 / 500000000000 : ℝ)
  | 5 => (1932789 / 50000000000 : ℝ)
  | 6 => (39225513 / 1000000000000 : ℝ)
  | 7 => (497509 / 12500000000 : ℝ)
  | 8 => (5047677 / 125000000000 : ℝ)
  | 9 => (40967617 / 1000000000000 : ℝ)
  | 10 => (41559339 / 1000000000000 : ℝ)
  | 11 => (8431319 / 200000000000 : ℝ)
  | 12 => (42759399 / 1000000000000 : ℝ)
  | 13 => (21683883 / 500000000000 : ℝ)
  | 14 => (43981709 / 1000000000000 : ℝ)
  | 15 => (22300621 / 500000000000 : ℝ)
  | 16 => (5653297 / 125000000000 : ℝ)
  | 17 => (11464281 / 250000000000 : ℝ)
  | 18 => (23246749 / 500000000000 : ℝ)
  | 19 => (47135509 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch012Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((240 : ℝ) + (j.val : ℝ)) / 1600)
      (((240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch012Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch012Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((240 : ℝ) + (j.val : ℝ)) / 1600)
    (((240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch012Neg25WeightLower j.val) (hpThetaShiftTwoBatch012Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch012Neg25WeightLower, hpThetaShiftTwoBatch012Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch012Neg25_integral_bounds :
    (717949329 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (368371601 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch012Lower hpThetaJensenCellsBatch012Upper
    hpThetaShiftTwoBatch012Neg25WeightLower hpThetaShiftTwoBatch012Neg25WeightUpper hpThetaJensenCellsBatch012_bounds hpThetaShiftTwoBatch012Neg25_weight_bounds
  have hl : (717949329 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch012Lower j * hpThetaShiftTwoBatch012Neg25WeightLower j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftTwoBatch012Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftTwoBatch012Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch012Lower j * hpThetaShiftTwoBatch012Neg25WeightUpper j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftTwoBatch012Neg25WeightUpper j) / 1600) ≤ (368371601 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftTwoBatch012Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (240 : ℝ) / 1600 = 12 / 80 by norm_num,
    show ((240 : ℝ) + 20) / 1600 = (12 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch012Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch012Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch012Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch012Neg25_integral_bounds
end HodgeProofHP
