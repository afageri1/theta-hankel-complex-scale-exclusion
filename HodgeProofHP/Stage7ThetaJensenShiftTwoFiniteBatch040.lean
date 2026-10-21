/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch040

/-! Exact signed weight and batch integral certificates, batch 40 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch040Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3606564153 / 1000000000000 : ℝ)
  | 1 => (3633423019 / 1000000000000 : ℝ)
  | 2 => (3660102063 / 1000000000000 : ℝ)
  | 3 => (3686592517 / 1000000000000 : ℝ)
  | 4 => (464110683 / 125000000000 : ℝ)
  | 5 => (3738971839 / 1000000000000 : ℝ)
  | 6 => (1882421211 / 500000000000 : ℝ)
  | 7 => (1895243921 / 500000000000 : ℝ)
  | 8 => (381589857 / 100000000000 : ℝ)
  | 9 => (1920532461 / 500000000000 : ℝ)
  | 10 => (1932988527 / 500000000000 : ℝ)
  | 11 => (3890624963 / 1000000000000 : ℝ)
  | 12 => (1957499241 / 500000000000 : ℝ)
  | 13 => (49238591 / 12500000000 : ℝ)
  | 14 => (1981440431 / 500000000000 : ℝ)
  | 15 => (3986368563 / 1000000000000 : ℝ)
  | 16 => (4009539549 / 1000000000000 : ℝ)
  | 17 => (806476563 / 200000000000 : ℝ)
  | 18 => (253430449 / 62500000000 : ℝ)
  | 19 => (2038520651 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch040Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (181671151 / 50000000000 : ℝ)
  | 1 => (228756379 / 62500000000 : ℝ)
  | 2 => (1843296259 / 500000000000 : ℝ)
  | 3 => (742577093 / 200000000000 : ℝ)
  | 4 => (11684287 / 3125000000 : ℝ)
  | 5 => (3764842423 / 1000000000000 : ℝ)
  | 6 => (3790487843 / 1000000000000 : ℝ)
  | 7 => (3815898571 / 1000000000000 : ℝ)
  | 8 => (3841064923 / 1000000000000 : ℝ)
  | 9 => (773195411 / 200000000000 : ℝ)
  | 10 => (972656241 / 250000000000 : ℝ)
  | 11 => (3914998483 / 1000000000000 : ℝ)
  | 12 => (3939087281 / 1000000000000 : ℝ)
  | 13 => (3962880863 / 1000000000000 : ℝ)
  | 14 => (996592141 / 250000000000 : ℝ)
  | 15 => (80190791 / 20000000000 : ℝ)
  | 16 => (126011963 / 31250000000 : ℝ)
  | 17 => (810977437 / 200000000000 : ℝ)
  | 18 => (4077041303 / 1000000000000 : ℝ)
  | 19 => (102470841 / 25000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch040Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((800 : ℝ) + (j.val : ℝ)) / 1600)
      (((800 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch040Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch040Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((800 : ℝ) + (j.val : ℝ)) / 1600)
    (((800 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch040Neg100WeightLower j.val) (hpThetaShiftTwoBatch040Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch040Neg100WeightLower, hpThetaShiftTwoBatch040Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch040Neg100_integral_bounds :
    (5339438923 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (2731613969 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (800 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch040Lower hpThetaJensenCellsBatch040Upper
    hpThetaShiftTwoBatch040Neg100WeightLower hpThetaShiftTwoBatch040Neg100WeightUpper hpThetaJensenCellsBatch040_bounds hpThetaShiftTwoBatch040Neg100_weight_bounds
  have hl : (5339438923 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch040Lower j * hpThetaShiftTwoBatch040Neg100WeightLower j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftTwoBatch040Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftTwoBatch040Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch040Lower j * hpThetaShiftTwoBatch040Neg100WeightUpper j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftTwoBatch040Neg100WeightUpper j) / 1600) ≤ (2731613969 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftTwoBatch040Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (800 : ℝ) / 1600 = 40 / 80 by norm_num,
    show ((800 : ℝ) + 20) / 1600 = (40 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch040Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (420302941 / 1000000000000 : ℝ)
  | 1 => (219944459 / 500000000000 : ℝ)
  | 2 => (459715101 / 1000000000000 : ℝ)
  | 3 => (119945659 / 250000000000 : ℝ)
  | 4 => (500092659 / 1000000000000 : ℝ)
  | 5 => (104129259 / 200000000000 : ℝ)
  | 6 => (541444657 / 1000000000000 : ℝ)
  | 7 => (281244423 / 500000000000 : ℝ)
  | 8 => (36486247 / 62500000000 : ℝ)
  | 9 => (151329763 / 250000000000 : ℝ)
  | 10 => (627107211 / 1000000000000 : ℝ)
  | 11 => (324572741 / 500000000000 : ℝ)
  | 12 => (335717451 / 500000000000 : ℝ)
  | 13 => (693976499 / 1000000000000 : ℝ)
  | 14 => (716771283 / 1000000000000 : ℝ)
  | 15 => (184955063 / 250000000000 : ℝ)
  | 16 => (763124391 / 1000000000000 : ℝ)
  | 17 => (786684667 / 1000000000000 : ℝ)
  | 18 => (162100407 / 200000000000 : ℝ)
  | 19 => (834577433 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch040Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (439888919 / 1000000000000 : ℝ)
  | 1 => (229857551 / 500000000000 : ℝ)
  | 2 => (479782637 / 1000000000000 : ℝ)
  | 3 => (25004633 / 50000000000 : ℝ)
  | 4 => (65080787 / 125000000000 : ℝ)
  | 5 => (270722329 / 500000000000 : ℝ)
  | 6 => (562488847 / 1000000000000 : ℝ)
  | 7 => (583779953 / 1000000000000 : ℝ)
  | 8 => (605319053 / 1000000000000 : ℝ)
  | 9 => (156776803 / 250000000000 : ℝ)
  | 10 => (649145483 / 1000000000000 : ℝ)
  | 11 => (671434903 / 1000000000000 : ℝ)
  | 12 => (1387953 / 2000000000 : ℝ)
  | 13 => (179192821 / 250000000000 : ℝ)
  | 14 => (739820253 / 1000000000000 : ℝ)
  | 15 => (95390549 / 125000000000 : ℝ)
  | 16 => (196671167 / 250000000000 : ℝ)
  | 17 => (202625509 / 250000000000 : ℝ)
  | 18 => (417288717 / 500000000000 : ℝ)
  | 19 => (171782357 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch040Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((800 : ℝ) + (j.val : ℝ)) / 1600)
      (((800 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch040Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch040Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((800 : ℝ) + (j.val : ℝ)) / 1600)
    (((800 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch040Neg65WeightLower j.val) (hpThetaShiftTwoBatch040Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch040Neg65WeightLower, hpThetaShiftTwoBatch040Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch040Neg65_integral_bounds :
    (854129843 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (179850721 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (800 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch040Lower hpThetaJensenCellsBatch040Upper
    hpThetaShiftTwoBatch040Neg65WeightLower hpThetaShiftTwoBatch040Neg65WeightUpper hpThetaJensenCellsBatch040_bounds hpThetaShiftTwoBatch040Neg65_weight_bounds
  have hl : (854129843 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch040Lower j * hpThetaShiftTwoBatch040Neg65WeightLower j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftTwoBatch040Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftTwoBatch040Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch040Lower j * hpThetaShiftTwoBatch040Neg65WeightUpper j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftTwoBatch040Neg65WeightUpper j) / 1600) ≤ (179850721 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftTwoBatch040Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (800 : ℝ) / 1600 = 40 / 80 by norm_num,
    show ((800 : ℝ) + 20) / 1600 = (40 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch040Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-237711411 / 200000000000 : ℝ)
  | 1 => (-594868961 / 500000000000 : ℝ)
  | 2 => (-595410223 / 500000000000 : ℝ)
  | 3 => (-1191803357 / 1000000000000 : ℝ)
  | 4 => (-596342687 / 500000000000 : ℝ)
  | 5 => (-596732607 / 500000000000 : ℝ)
  | 6 => (-74633849 / 62500000000 : ℝ)
  | 7 => (-597356593 / 500000000000 : ℝ)
  | 8 => (-1195178717 / 1000000000000 : ℝ)
  | 9 => (-37360527 / 31250000000 : ℝ)
  | 10 => (-149473289 / 125000000000 : ℝ)
  | 11 => (-149490717 / 125000000000 : ℝ)
  | 12 => (-1195958467 / 1000000000000 : ℝ)
  | 13 => (-597976903 / 500000000000 : ℝ)
  | 14 => (-597934593 / 500000000000 : ℝ)
  | 15 => (-239134107 / 200000000000 : ℝ)
  | 16 => (-1195356503 / 1000000000000 : ℝ)
  | 17 => (-238985147 / 200000000000 : ℝ)
  | 18 => (-119437687 / 100000000000 : ℝ)
  | 19 => (-596854271 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch040Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-118727911 / 100000000000 : ℝ)
  | 1 => (-594278527 / 500000000000 : ℝ)
  | 2 => (-1189737921 / 1000000000000 : ℝ)
  | 3 => (-238164089 / 200000000000 : ℝ)
  | 4 => (-297950839 / 250000000000 : ℝ)
  | 5 => (-1192685373 / 1000000000000 : ℝ)
  | 6 => (-1193465213 / 1000000000000 : ℝ)
  | 7 => (-1194141583 / 1000000000000 : ℝ)
  | 8 => (-238942637 / 200000000000 : ℝ)
  | 9 => (-298794679 / 250000000000 : ℝ)
  | 10 => (-1195536863 / 1000000000000 : ℝ)
  | 11 => (-1195786311 / 1000000000000 : ℝ)
  | 12 => (-239185147 / 200000000000 : ℝ)
  | 13 => (-239173837 / 200000000000 : ℝ)
  | 14 => (-597835267 / 500000000000 : ℝ)
  | 15 => (-597678251 / 500000000000 : ℝ)
  | 16 => (-597462867 / 500000000000 : ℝ)
  | 17 => (-1194376869 / 1000000000000 : ℝ)
  | 18 => (-1193708541 / 1000000000000 : ℝ)
  | 19 => (-74557461 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch040Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((800 : ℝ) + (j.val : ℝ)) / 1600)
      (((800 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch040Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch040Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((800 : ℝ) + (j.val : ℝ)) / 1600)
    (((800 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch040Neg45WeightLower j.val) (hpThetaShiftTwoBatch040Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch040Neg45WeightLower, hpThetaShiftTwoBatch040Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch040Neg45_integral_bounds :
    (-843269679 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-1658087849 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (800 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch040Lower hpThetaJensenCellsBatch040Upper
    hpThetaShiftTwoBatch040Neg45WeightLower hpThetaShiftTwoBatch040Neg45WeightUpper hpThetaJensenCellsBatch040_bounds hpThetaShiftTwoBatch040Neg45_weight_bounds
  have hl : (-843269679 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch040Lower j * hpThetaShiftTwoBatch040Neg45WeightLower j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftTwoBatch040Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftTwoBatch040Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch040Lower j * hpThetaShiftTwoBatch040Neg45WeightUpper j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftTwoBatch040Neg45WeightUpper j) / 1600) ≤ (-1658087849 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftTwoBatch040Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (800 : ℝ) / 1600 = 40 / 80 by norm_num,
    show ((800 : ℝ) + 20) / 1600 = (40 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch040Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-142432673 / 200000000000 : ℝ)
  | 1 => (-361074491 / 500000000000 : ℝ)
  | 2 => (-366091987 / 500000000000 : ℝ)
  | 3 => (-371134113 / 500000000000 : ℝ)
  | 4 => (-752401619 / 1000000000000 : ℝ)
  | 5 => (-76258403 / 100000000000 : ℝ)
  | 6 => (-386407667 / 500000000000 : ℝ)
  | 7 => (-391547701 / 500000000000 : ℝ)
  | 8 => (-7934241 / 10000000000 : ℝ)
  | 9 => (-803801293 / 1000000000000 : ℝ)
  | 10 => (-20355671 / 25000000000 : ℝ)
  | 11 => (-412350299 / 500000000000 : ℝ)
  | 12 => (-835222419 / 1000000000000 : ℝ)
  | 13 => (-845792153 / 1000000000000 : ℝ)
  | 14 => (-171281929 / 200000000000 : ℝ)
  | 15 => (-867074737 / 1000000000000 : ℝ)
  | 16 => (-877787267 / 1000000000000 : ℝ)
  | 17 => (-888547069 / 1000000000000 : ℝ)
  | 18 => (-449676987 / 500000000000 : ℝ)
  | 19 => (-14221997 / 15625000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch040Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-351113617 / 500000000000 : ℝ)
  | 1 => (-178040841 / 250000000000 : ℝ)
  | 2 => (-722148981 / 1000000000000 : ℝ)
  | 3 => (-732183973 / 1000000000000 : ℝ)
  | 4 => (-29690729 / 40000000000 : ℝ)
  | 5 => (-376200809 / 500000000000 : ℝ)
  | 6 => (-762584029 / 1000000000000 : ℝ)
  | 7 => (-772815333 / 1000000000000 : ℝ)
  | 8 => (-783095401 / 1000000000000 : ℝ)
  | 9 => (-793424099 / 1000000000000 : ℝ)
  | 10 => (-200950323 / 250000000000 : ℝ)
  | 11 => (-814226839 / 1000000000000 : ℝ)
  | 12 => (-824700597 / 1000000000000 : ℝ)
  | 13 => (-417611209 / 500000000000 : ℝ)
  | 14 => (-105724019 / 125000000000 : ℝ)
  | 15 => (-214102411 / 250000000000 : ℝ)
  | 16 => (-54192171 / 62500000000 : ℝ)
  | 17 => (-438893633 / 500000000000 : ℝ)
  | 18 => (-222136767 / 250000000000 : ℝ)
  | 19 => (-899353973 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch040Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((800 : ℝ) + (j.val : ℝ)) / 1600)
      (((800 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch040Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch040Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((800 : ℝ) + (j.val : ℝ)) / 1600)
    (((800 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch040Neg25WeightLower j.val) (hpThetaShiftTwoBatch040Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch040Neg25WeightLower, hpThetaShiftTwoBatch040Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch040Neg25_integral_bounds :
    (-114014577 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-221406761 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (800 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch040Lower hpThetaJensenCellsBatch040Upper
    hpThetaShiftTwoBatch040Neg25WeightLower hpThetaShiftTwoBatch040Neg25WeightUpper hpThetaJensenCellsBatch040_bounds hpThetaShiftTwoBatch040Neg25_weight_bounds
  have hl : (-114014577 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch040Lower j * hpThetaShiftTwoBatch040Neg25WeightLower j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftTwoBatch040Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftTwoBatch040Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch040Lower j * hpThetaShiftTwoBatch040Neg25WeightUpper j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftTwoBatch040Neg25WeightUpper j) / 1600) ≤ (-221406761 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftTwoBatch040Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (800 : ℝ) / 1600 = 40 / 80 by norm_num,
    show ((800 : ℝ) + 20) / 1600 = (40 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch040Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch040Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch040Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch040Neg25_integral_bounds
end HodgeProofHP
