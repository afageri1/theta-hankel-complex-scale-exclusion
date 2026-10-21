/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch011

/-! Exact signed weight and batch integral certificates, batch 11 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch011Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3018791 / 200000000000 : ℝ)
  | 1 => (7626899 / 500000000000 : ℝ)
  | 2 => (3853247 / 250000000000 : ℝ)
  | 3 => (15571467 / 1000000000000 : ℝ)
  | 4 => (15729177 / 1000000000000 : ℝ)
  | 5 => (15886059 / 1000000000000 : ℝ)
  | 6 => (16042051 / 1000000000000 : ℝ)
  | 7 => (4049273 / 250000000000 : ℝ)
  | 8 => (16351121 / 1000000000000 : ℝ)
  | 9 => (660163 / 40000000000 : ℝ)
  | 10 => (1665589 / 100000000000 : ℝ)
  | 11 => (8403251 / 500000000000 : ℝ)
  | 12 => (8477923 / 500000000000 : ℝ)
  | 13 => (8551927 / 500000000000 : ℝ)
  | 14 => (8625231 / 500000000000 : ℝ)
  | 15 => (43489 / 2500000000 : ℝ)
  | 16 => (17539201 / 1000000000000 : ℝ)
  | 17 => (4420299 / 250000000000 : ℝ)
  | 18 => (8910757 / 500000000000 : ℝ)
  | 19 => (4490021 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch011Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (15253799 / 1000000000000 : ℝ)
  | 1 => (15412989 / 1000000000000 : ℝ)
  | 2 => (3892867 / 250000000000 : ℝ)
  | 3 => (7864589 / 500000000000 : ℝ)
  | 4 => (794303 / 50000000000 : ℝ)
  | 5 => (4010513 / 250000000000 : ℝ)
  | 6 => (16197093 / 1000000000000 : ℝ)
  | 7 => (8175561 / 500000000000 : ℝ)
  | 8 => (4126019 / 250000000000 : ℝ)
  | 9 => (16655891 / 1000000000000 : ℝ)
  | 10 => (16806503 / 1000000000000 : ℝ)
  | 11 => (16955847 / 1000000000000 : ℝ)
  | 12 => (3420771 / 200000000000 : ℝ)
  | 13 => (17250463 / 1000000000000 : ℝ)
  | 14 => (17395601 / 1000000000000 : ℝ)
  | 15 => (8769601 / 500000000000 : ℝ)
  | 16 => (17681197 / 1000000000000 : ℝ)
  | 17 => (3564303 / 200000000000 : ℝ)
  | 18 => (3592017 / 200000000000 : ℝ)
  | 19 => (18096837 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch011Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((220 : ℝ) + (j.val : ℝ)) / 1600)
      (((220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch011Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch011Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((220 : ℝ) + (j.val : ℝ)) / 1600)
    (((220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch011Neg100WeightLower j.val) (hpThetaShiftTwoBatch011Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch011Neg100WeightLower, hpThetaShiftTwoBatch011Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch011Neg100_integral_bounds :
    (75626459 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (308744397 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch011Lower hpThetaJensenCellsBatch011Upper
    hpThetaShiftTwoBatch011Neg100WeightLower hpThetaShiftTwoBatch011Neg100WeightUpper hpThetaJensenCellsBatch011_bounds hpThetaShiftTwoBatch011Neg100_weight_bounds
  have hl : (75626459 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch011Lower j * hpThetaShiftTwoBatch011Neg100WeightLower j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftTwoBatch011Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftTwoBatch011Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch011Lower j * hpThetaShiftTwoBatch011Neg100WeightUpper j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftTwoBatch011Neg100WeightUpper j) / 1600) ≤ (308744397 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftTwoBatch011Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (220 : ℝ) / 1600 = 11 / 80 by norm_num,
    show ((220 : ℝ) + 20) / 1600 = (11 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch011Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4936879 / 250000000000 : ℝ)
  | 1 => (10012239 / 500000000000 : ℝ)
  | 2 => (10151533 / 500000000000 : ℝ)
  | 3 => (20583249 / 1000000000000 : ℝ)
  | 4 => (10432499 / 500000000000 : ℝ)
  | 5 => (5287071 / 250000000000 : ℝ)
  | 6 => (857323 / 40000000000 : ℝ)
  | 7 => (21719339 / 1000000000000 : ℝ)
  | 8 => (5501761 / 250000000000 : ℝ)
  | 9 => (22296157 / 1000000000000 : ℝ)
  | 10 => (22586643 / 1000000000000 : ℝ)
  | 11 => (22878467 / 1000000000000 : ℝ)
  | 12 => (11585797 / 500000000000 : ℝ)
  | 13 => (23465987 / 1000000000000 : ℝ)
  | 14 => (2376161 / 100000000000 : ℝ)
  | 15 => (3007303 / 125000000000 : ℝ)
  | 16 => (2435639 / 100000000000 : ℝ)
  | 17 => (24655469 / 1000000000000 : ℝ)
  | 18 => (1247781 / 50000000000 : ℝ)
  | 19 => (25256803 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch011Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (20024479 / 1000000000000 : ℝ)
  | 1 => (20303067 / 1000000000000 : ℝ)
  | 2 => (82333 / 4000000000 : ℝ)
  | 3 => (20864999 / 1000000000000 : ℝ)
  | 4 => (4229657 / 200000000000 : ℝ)
  | 5 => (5358269 / 250000000000 : ℝ)
  | 6 => (1085967 / 50000000000 : ℝ)
  | 7 => (4401409 / 200000000000 : ℝ)
  | 8 => (11148079 / 500000000000 : ℝ)
  | 9 => (5646661 / 250000000000 : ℝ)
  | 10 => (5719617 / 250000000000 : ℝ)
  | 11 => (4634319 / 200000000000 : ℝ)
  | 12 => (5866497 / 250000000000 : ℝ)
  | 13 => (23761611 / 1000000000000 : ℝ)
  | 14 => (962337 / 40000000000 : ℝ)
  | 15 => (24356391 / 1000000000000 : ℝ)
  | 16 => (2465547 / 100000000000 : ℝ)
  | 17 => (24955621 / 1000000000000 : ℝ)
  | 18 => (6314201 / 250000000000 : ℝ)
  | 19 => (399359 / 15625000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch011Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((220 : ℝ) + (j.val : ℝ)) / 1600)
      (((220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch011Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch011Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((220 : ℝ) + (j.val : ℝ)) / 1600)
    (((220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch011Neg65WeightLower j.val) (hpThetaShiftTwoBatch011Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch011Neg65WeightLower, hpThetaShiftTwoBatch011Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch011Neg65_integral_bounds :
    (410246311 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (420311277 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch011Lower hpThetaJensenCellsBatch011Upper
    hpThetaShiftTwoBatch011Neg65WeightLower hpThetaShiftTwoBatch011Neg65WeightUpper hpThetaJensenCellsBatch011_bounds hpThetaShiftTwoBatch011Neg65_weight_bounds
  have hl : (410246311 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch011Lower j * hpThetaShiftTwoBatch011Neg65WeightLower j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftTwoBatch011Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftTwoBatch011Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch011Lower j * hpThetaShiftTwoBatch011Neg65WeightUpper j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftTwoBatch011Neg65WeightUpper j) / 1600) ≤ (420311277 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftTwoBatch011Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (220 : ℝ) / 1600 = 11 / 80 by norm_num,
    show ((220 : ℝ) + 20) / 1600 = (11 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch011Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (11319607 / 500000000000 : ℝ)
  | 1 => (11495759 / 500000000000 : ℝ)
  | 2 => (5836753 / 250000000000 : ℝ)
  | 3 => (23705689 / 1000000000000 : ℝ)
  | 4 => (3008443 / 125000000000 : ℝ)
  | 5 => (24432571 / 1000000000000 : ℝ)
  | 6 => (24800763 / 1000000000000 : ℝ)
  | 7 => (25172111 / 1000000000000 : ℝ)
  | 8 => (1596663 / 62500000000 : ℝ)
  | 9 => (12962123 / 500000000000 : ℝ)
  | 10 => (5261003 / 200000000000 : ℝ)
  | 11 => (3336113 / 125000000000 : ℝ)
  | 12 => (423061 / 15625000000 : ℝ)
  | 13 => (6866501 / 250000000000 : ℝ)
  | 14 => (3482399 / 125000000000 : ℝ)
  | 15 => (5651091 / 200000000000 : ℝ)
  | 16 => (1432739 / 50000000000 : ℝ)
  | 17 => (5811431 / 200000000000 : ℝ)
  | 18 => (5892513 / 200000000000 : ℝ)
  | 19 => (5974199 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch011Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (22991519 / 1000000000000 : ℝ)
  | 1 => (23347013 / 1000000000000 : ℝ)
  | 2 => (2370569 / 100000000000 : ℝ)
  | 3 => (4813509 / 200000000000 : ℝ)
  | 4 => (6108143 / 250000000000 : ℝ)
  | 5 => (6200191 / 250000000000 : ℝ)
  | 6 => (1573257 / 62500000000 : ℝ)
  | 7 => (25546609 / 1000000000000 : ℝ)
  | 8 => (25924247 / 1000000000000 : ℝ)
  | 9 => (3288127 / 125000000000 : ℝ)
  | 10 => (5337781 / 200000000000 : ℝ)
  | 11 => (5415181 / 200000000000 : ℝ)
  | 12 => (5493201 / 200000000000 : ℝ)
  | 13 => (27859193 / 1000000000000 : ℝ)
  | 14 => (882983 / 31250000000 : ℝ)
  | 15 => (28654781 / 1000000000000 : ℝ)
  | 16 => (7264289 / 250000000000 : ℝ)
  | 17 => (14731283 / 500000000000 : ℝ)
  | 18 => (7467749 / 250000000000 : ℝ)
  | 19 => (3028243 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch011Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((220 : ℝ) + (j.val : ℝ)) / 1600)
      (((220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch011Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch011Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((220 : ℝ) + (j.val : ℝ)) / 1600)
    (((220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch011Neg45WeightLower j.val) (hpThetaShiftTwoBatch011Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch011Neg45WeightLower, hpThetaShiftTwoBatch011Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch011Neg45_integral_bounds :
    (477817931 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (15323359 / 31250000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch011Lower hpThetaJensenCellsBatch011Upper
    hpThetaShiftTwoBatch011Neg45WeightLower hpThetaShiftTwoBatch011Neg45WeightUpper hpThetaJensenCellsBatch011_bounds hpThetaShiftTwoBatch011Neg45_weight_bounds
  have hl : (477817931 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch011Lower j * hpThetaShiftTwoBatch011Neg45WeightLower j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftTwoBatch011Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftTwoBatch011Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch011Lower j * hpThetaShiftTwoBatch011Neg45WeightUpper j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftTwoBatch011Neg45WeightUpper j) / 1600) ≤ (15323359 / 31250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftTwoBatch011Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (220 : ℝ) / 1600 = 11 / 80 by norm_num,
    show ((220 : ℝ) + 20) / 1600 = (11 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch011Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2570481 / 100000000000 : ℝ)
  | 1 => (65347 / 2500000000 : ℝ)
  | 2 => (1661109 / 62500000000 : ℝ)
  | 3 => (5404333 / 200000000000 : ℝ)
  | 4 => (27470587 / 1000000000000 : ℝ)
  | 5 => (6981133 / 250000000000 : ℝ)
  | 6 => (1135341 / 40000000000 : ℝ)
  | 7 => (14423793 / 500000000000 : ℝ)
  | 8 => (14658369 / 500000000000 : ℝ)
  | 9 => (7447751 / 250000000000 : ℝ)
  | 10 => (6054081 / 200000000000 : ℝ)
  | 11 => (15377481 / 500000000000 : ℝ)
  | 12 => (31244697 / 1000000000000 : ℝ)
  | 13 => (31739631 / 1000000000000 : ℝ)
  | 14 => (4029973 / 125000000000 : ℝ)
  | 15 => (4093147 / 125000000000 : ℝ)
  | 16 => (8313957 / 250000000000 : ℝ)
  | 17 => (16885879 / 500000000000 : ℝ)
  | 18 => (34292987 / 1000000000000 : ℝ)
  | 19 => (17409767 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch011Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (26138801 / 1000000000000 : ℝ)
  | 1 => (5315549 / 200000000000 : ℝ)
  | 2 => (13510833 / 500000000000 : ℝ)
  | 3 => (6867647 / 250000000000 : ℝ)
  | 4 => (27924533 / 1000000000000 : ℝ)
  | 5 => (14191763 / 500000000000 : ℝ)
  | 6 => (28847587 / 1000000000000 : ℝ)
  | 7 => (29316739 / 1000000000000 : ℝ)
  | 8 => (5958201 / 200000000000 : ℝ)
  | 9 => (15135203 / 500000000000 : ℝ)
  | 10 => (30754963 / 1000000000000 : ℝ)
  | 11 => (15622349 / 500000000000 : ℝ)
  | 12 => (1983727 / 62500000000 : ℝ)
  | 13 => (6447957 / 200000000000 : ℝ)
  | 14 => (32745177 / 1000000000000 : ℝ)
  | 15 => (33255829 / 1000000000000 : ℝ)
  | 16 => (33771759 / 1000000000000 : ℝ)
  | 17 => (8573247 / 250000000000 : ℝ)
  | 18 => (6963907 / 200000000000 : ℝ)
  | 19 => (35351417 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch011Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((220 : ℝ) + (j.val : ℝ)) / 1600)
      (((220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch011Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch011Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((220 : ℝ) + (j.val : ℝ)) / 1600)
    (((220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch011Neg25WeightLower j.val) (hpThetaShiftTwoBatch011Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch011Neg25WeightLower, hpThetaShiftTwoBatch011Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch011Neg25_integral_bounds :
    (549894453 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (282549271 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch011Lower hpThetaJensenCellsBatch011Upper
    hpThetaShiftTwoBatch011Neg25WeightLower hpThetaShiftTwoBatch011Neg25WeightUpper hpThetaJensenCellsBatch011_bounds hpThetaShiftTwoBatch011Neg25_weight_bounds
  have hl : (549894453 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch011Lower j * hpThetaShiftTwoBatch011Neg25WeightLower j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftTwoBatch011Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftTwoBatch011Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch011Lower j * hpThetaShiftTwoBatch011Neg25WeightUpper j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftTwoBatch011Neg25WeightUpper j) / 1600) ≤ (282549271 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftTwoBatch011Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (220 : ℝ) / 1600 = 11 / 80 by norm_num,
    show ((220 : ℝ) + 20) / 1600 = (11 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch011Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch011Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch011Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch011Neg25_integral_bounds
end HodgeProofHP
