/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch039

/-! Exact signed weight and batch integral certificates, batch 39 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch039Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3043879469 / 1000000000000 : ℝ)
  | 1 => (1536354073 / 500000000000 : ℝ)
  | 2 => (3101503607 / 1000000000000 : ℝ)
  | 3 => (125210389 / 40000000000 : ℝ)
  | 4 => (3158970257 / 1000000000000 : ℝ)
  | 5 => (3187628839 / 1000000000000 : ℝ)
  | 6 => (1608114493 / 500000000000 : ℝ)
  | 7 => (811191023 / 250000000000 : ℝ)
  | 8 => (1636613713 / 500000000000 : ℝ)
  | 9 => (1650806067 / 500000000000 : ℝ)
  | 10 => (52029863 / 15625000000 : ℝ)
  | 11 => (839529403 / 250000000000 : ℝ)
  | 12 => (3386224033 / 1000000000000 : ℝ)
  | 13 => (5462757 / 1600000000 : ℝ)
  | 14 => (430263423 / 125000000000 : ℝ)
  | 15 => (867467293 / 250000000000 : ℝ)
  | 16 => (874375179 / 250000000000 : ℝ)
  | 17 => (3524994107 / 1000000000000 : ℝ)
  | 18 => (3552341293 / 1000000000000 : ℝ)
  | 19 => (1789767043 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch039Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3072708147 / 1000000000000 : ℝ)
  | 1 => (387687951 / 125000000000 : ℝ)
  | 2 => (1565129863 / 500000000000 : ℝ)
  | 3 => (1579485129 / 500000000000 : ℝ)
  | 4 => (79690721 / 25000000000 : ℝ)
  | 5 => (3216228987 / 1000000000000 : ℝ)
  | 6 => (3244764093 / 1000000000000 : ℝ)
  | 7 => (3273227427 / 1000000000000 : ℝ)
  | 8 => (660322427 / 200000000000 : ℝ)
  | 9 => (3329911233 / 1000000000000 : ℝ)
  | 10 => (3358117613 / 1000000000000 : ℝ)
  | 11 => (1693112017 / 500000000000 : ℝ)
  | 12 => (1707111563 / 500000000000 : ℝ)
  | 13 => (688421477 / 200000000000 : ℝ)
  | 14 => (3469869173 / 1000000000000 : ℝ)
  | 15 => (3497500717 / 1000000000000 : ℝ)
  | 16 => (881248527 / 250000000000 : ℝ)
  | 17 => (1776170647 / 500000000000 : ℝ)
  | 18 => (3579534087 / 1000000000000 : ℝ)
  | 19 => (1803282077 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch039Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((780 : ℝ) + (j.val : ℝ)) / 1600)
      (((780 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch039Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch039Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((780 : ℝ) + (j.val : ℝ)) / 1600)
    (((780 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch039Neg100WeightLower j.val) (hpThetaShiftTwoBatch039Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch039Neg100WeightLower, hpThetaShiftTwoBatch039Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch039Neg100_integral_bounds :
    (1069917363 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (2741784681 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (780 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch039Lower hpThetaJensenCellsBatch039Upper
    hpThetaShiftTwoBatch039Neg100WeightLower hpThetaShiftTwoBatch039Neg100WeightUpper hpThetaJensenCellsBatch039_bounds hpThetaShiftTwoBatch039Neg100_weight_bounds
  have hl : (1069917363 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch039Lower j * hpThetaShiftTwoBatch039Neg100WeightLower j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftTwoBatch039Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftTwoBatch039Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch039Lower j * hpThetaShiftTwoBatch039Neg100WeightUpper j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftTwoBatch039Neg100WeightUpper j) / 1600) ≤ (2741784681 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftTwoBatch039Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (780 : ℝ) / 1600 = 39 / 80 by norm_num,
    show ((780 : ℝ) + 20) / 1600 = (39 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch039Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (77176723 / 1000000000000 : ℝ)
  | 1 => (92213641 / 1000000000000 : ℝ)
  | 2 => (107465969 / 1000000000000 : ℝ)
  | 3 => (24587003 / 200000000000 : ℝ)
  | 4 => (69311041 / 500000000000 : ℝ)
  | 5 => (154528467 / 1000000000000 : ℝ)
  | 6 => (8532773 / 50000000000 : ℝ)
  | 7 => (93502173 / 500000000000 : ℝ)
  | 8 => (101788201 / 500000000000 : ℝ)
  | 9 => (220372897 / 1000000000000 : ℝ)
  | 10 => (47479019 / 200000000000 : ℝ)
  | 11 => (63661063 / 250000000000 : ℝ)
  | 12 => (136060807 / 500000000000 : ℝ)
  | 13 => (289828423 / 1000000000000 : ℝ)
  | 14 => (30776591 / 100000000000 : ℝ)
  | 15 => (325935297 / 1000000000000 : ℝ)
  | 16 => (1721689 / 5000000000 : ℝ)
  | 17 => (11342957 / 31250000000 : ℝ)
  | 18 => (190923483 / 500000000000 : ℝ)
  | 19 => (100239003 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch039Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (46106821 / 500000000000 : ℝ)
  | 1 => (10746597 / 100000000000 : ℝ)
  | 2 => (15366877 / 125000000000 : ℝ)
  | 3 => (138622083 / 1000000000000 : ℝ)
  | 4 => (38632117 / 250000000000 : ℝ)
  | 5 => (170655461 / 1000000000000 : ℝ)
  | 6 => (187004347 / 1000000000000 : ℝ)
  | 7 => (203576403 / 1000000000000 : ℝ)
  | 8 => (110186449 / 500000000000 : ℝ)
  | 9 => (29674387 / 125000000000 : ℝ)
  | 10 => (254644253 / 1000000000000 : ℝ)
  | 11 => (54424323 / 200000000000 : ℝ)
  | 12 => (36228553 / 125000000000 : ℝ)
  | 13 => (307765911 / 1000000000000 : ℝ)
  | 14 => (162967649 / 500000000000 : ℝ)
  | 15 => (344337801 / 1000000000000 : ℝ)
  | 16 => (2903797 / 8000000000 : ℝ)
  | 17 => (381846967 / 1000000000000 : ℝ)
  | 18 => (400956013 / 1000000000000 : ℝ)
  | 19 => (210151471 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch039Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((780 : ℝ) + (j.val : ℝ)) / 1600)
      (((780 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch039Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch039Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((780 : ℝ) + (j.val : ℝ)) / 1600)
    (((780 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch039Neg65WeightLower j.val) (hpThetaShiftTwoBatch039Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch039Neg65WeightLower, hpThetaShiftTwoBatch039Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch039Neg65_integral_bounds :
    (369431497 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (25225679 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (780 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch039Lower hpThetaJensenCellsBatch039Upper
    hpThetaShiftTwoBatch039Neg65WeightLower hpThetaShiftTwoBatch039Neg65WeightUpper hpThetaJensenCellsBatch039_bounds hpThetaShiftTwoBatch039Neg65_weight_bounds
  have hl : (369431497 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch039Lower j * hpThetaShiftTwoBatch039Neg65WeightLower j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftTwoBatch039Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftTwoBatch039Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch039Lower j * hpThetaShiftTwoBatch039Neg65WeightUpper j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftTwoBatch039Neg65WeightUpper j) / 1600) ≤ (25225679 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftTwoBatch039Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (780 : ℝ) / 1600 = 39 / 80 by norm_num,
    show ((780 : ℝ) + 20) / 1600 = (39 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch039Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-573094173 / 500000000000 : ℝ)
  | 1 => (-287269781 / 250000000000 : ℝ)
  | 2 => (-230379121 / 200000000000 : ℝ)
  | 3 => (-1154636649 / 1000000000000 : ℝ)
  | 4 => (-1157301113 / 1000000000000 : ℝ)
  | 5 => (-289971961 / 250000000000 : ℝ)
  | 6 => (-232479137 / 200000000000 : ℝ)
  | 7 => (-1164823469 / 1000000000000 : ℝ)
  | 8 => (-46686801 / 40000000000 : ℝ)
  | 9 => (-584717087 / 500000000000 : ℝ)
  | 10 => (-117161473 / 100000000000 : ℝ)
  | 11 => (-1173710501 / 1000000000000 : ℝ)
  | 12 => (-36741259 / 31250000000 : ℝ)
  | 13 => (-588821443 / 500000000000 : ℝ)
  | 14 => (-29486927 / 25000000000 : ℝ)
  | 15 => (-1181221653 / 1000000000000 : ℝ)
  | 16 => (-1182875379 / 1000000000000 : ℝ)
  | 17 => (-37013657 / 31250000000 : ℝ)
  | 18 => (-23718107 / 20000000000 : ℝ)
  | 19 => (-1187279111 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch039Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1143224399 / 1000000000000 : ℝ)
  | 1 => (-229237669 / 200000000000 : ℝ)
  | 2 => (-1149079123 / 1000000000000 : ℝ)
  | 3 => (-287973901 / 250000000000 : ℝ)
  | 4 => (-144329581 / 125000000000 : ℝ)
  | 5 => (-144662639 / 125000000000 : ℝ)
  | 6 => (-1159887843 / 1000000000000 : ℝ)
  | 7 => (-290598921 / 250000000000 : ℝ)
  | 8 => (-291205867 / 250000000000 : ℝ)
  | 9 => (-145896253 / 125000000000 : ℝ)
  | 10 => (-1169434173 / 1000000000000 : ℝ)
  | 11 => (-1171614729 / 1000000000000 : ℝ)
  | 12 => (-2347421 / 2000000000 : ℝ)
  | 13 => (-1175720287 / 1000000000000 : ℝ)
  | 14 => (-235528577 / 200000000000 : ℝ)
  | 15 => (-1179477079 / 1000000000000 : ℝ)
  | 16 => (-295305413 / 250000000000 : ℝ)
  | 17 => (-591437689 / 500000000000 : ℝ)
  | 18 => (-1184437023 / 1000000000000 : ℝ)
  | 19 => (-1185905349 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch039Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((780 : ℝ) + (j.val : ℝ)) / 1600)
      (((780 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch039Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch039Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((780 : ℝ) + (j.val : ℝ)) / 1600)
    (((780 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch039Neg45WeightLower j.val) (hpThetaShiftTwoBatch039Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch039Neg45WeightLower, hpThetaShiftTwoBatch039Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch039Neg45_integral_bounds :
    (-19212073 / 10000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-943315717 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (780 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch039Lower hpThetaJensenCellsBatch039Upper
    hpThetaShiftTwoBatch039Neg45WeightLower hpThetaShiftTwoBatch039Neg45WeightUpper hpThetaJensenCellsBatch039_bounds hpThetaShiftTwoBatch039Neg45_weight_bounds
  have hl : (-19212073 / 10000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch039Lower j * hpThetaShiftTwoBatch039Neg45WeightLower j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftTwoBatch039Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftTwoBatch039Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch039Lower j * hpThetaShiftTwoBatch039Neg45WeightUpper j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftTwoBatch039Neg45WeightUpper j) / 1600) ≤ (-943315717 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftTwoBatch039Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (780 : ℝ) / 1600 = 39 / 80 by norm_num,
    show ((780 : ℝ) + 20) / 1600 = (39 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch039Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-522967641 / 1000000000000 : ℝ)
  | 1 => (-265973339 / 500000000000 : ℝ)
  | 2 => (-8452761 / 15625000000 : ℝ)
  | 3 => (-550057667 / 1000000000000 : ℝ)
  | 4 => (-279594757 / 500000000000 : ℝ)
  | 5 => (-568372187 / 1000000000000 : ℝ)
  | 6 => (-144401407 / 250000000000 : ℝ)
  | 7 => (-586889773 / 1000000000000 : ℝ)
  | 8 => (-149056139 / 250000000000 : ℝ)
  | 9 => (-151402477 / 250000000000 : ℝ)
  | 10 => (-615045757 / 1000000000000 : ℝ)
  | 11 => (-624532027 / 1000000000000 : ℝ)
  | 12 => (-634068641 / 1000000000000 : ℝ)
  | 13 => (-321827757 / 500000000000 : ℝ)
  | 14 => (-163323141 / 250000000000 : ℝ)
  | 15 => (-6629797 / 10000000000 : ℝ)
  | 16 => (-672716833 / 1000000000000 : ℝ)
  | 17 => (-136500773 / 200000000000 : ℝ)
  | 18 => (-6923407 / 10000000000 : ℝ)
  | 19 => (-140445447 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch039Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-257019819 / 500000000000 : ℝ)
  | 1 => (-13074191 / 25000000000 : ℝ)
  | 2 => (-531946677 / 1000000000000 : ℝ)
  | 3 => (-540976703 / 1000000000000 : ℝ)
  | 4 => (-275028833 / 500000000000 : ℝ)
  | 5 => (-559189513 / 1000000000000 : ℝ)
  | 6 => (-284186093 / 500000000000 : ℝ)
  | 7 => (-577605627 / 1000000000000 : ℝ)
  | 8 => (-146722443 / 250000000000 : ℝ)
  | 9 => (-119244911 / 200000000000 : ℝ)
  | 10 => (-605609907 / 1000000000000 : ℝ)
  | 11 => (-153761439 / 250000000000 : ℝ)
  | 12 => (-312266013 / 500000000000 : ℝ)
  | 13 => (-3962929 / 6250000000 : ℝ)
  | 14 => (-643655513 / 1000000000000 : ℝ)
  | 15 => (-653292563 / 1000000000000 : ℝ)
  | 16 => (-662979699 / 1000000000000 : ℝ)
  | 17 => (-21022401 / 31250000000 : ℝ)
  | 18 => (-85312983 / 125000000000 : ℝ)
  | 19 => (-692340699 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch039Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((780 : ℝ) + (j.val : ℝ)) / 1600)
      (((780 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch039Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch039Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((780 : ℝ) + (j.val : ℝ)) / 1600)
    (((780 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch039Neg25WeightLower j.val) (hpThetaShiftTwoBatch039Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch039Neg25WeightLower, hpThetaShiftTwoBatch039Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch039Neg25_integral_bounds :
    (-1000924047 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-96957891 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (780 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch039Lower hpThetaJensenCellsBatch039Upper
    hpThetaShiftTwoBatch039Neg25WeightLower hpThetaShiftTwoBatch039Neg25WeightUpper hpThetaJensenCellsBatch039_bounds hpThetaShiftTwoBatch039Neg25_weight_bounds
  have hl : (-1000924047 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch039Lower j * hpThetaShiftTwoBatch039Neg25WeightLower j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftTwoBatch039Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftTwoBatch039Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch039Lower j * hpThetaShiftTwoBatch039Neg25WeightUpper j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftTwoBatch039Neg25WeightUpper j) / 1600) ≤ (-96957891 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftTwoBatch039Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (780 : ℝ) / 1600 = 39 / 80 by norm_num,
    show ((780 : ℝ) + 20) / 1600 = (39 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch039Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch039Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch039Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch039Neg25_integral_bounds
end HodgeProofHP
