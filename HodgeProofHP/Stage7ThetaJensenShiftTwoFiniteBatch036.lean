/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch036

/-! Exact signed weight and batch integral certificates, batch 36 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch036Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1424654453 / 1000000000000 : ℝ)
  | 1 => (180996193 / 125000000000 : ℝ)
  | 2 => (735724991 / 500000000000 : ℝ)
  | 3 => (93443409 / 62500000000 : ℝ)
  | 4 => (303780391 / 200000000000 : ℝ)
  | 5 => (192858861 / 125000000000 : ℝ)
  | 6 => (1566999959 / 1000000000000 : ℝ)
  | 7 => (1591287731 / 1000000000000 : ℝ)
  | 8 => (1615732711 / 1000000000000 : ℝ)
  | 9 => (410083337 / 250000000000 : ℝ)
  | 10 => (333017607 / 200000000000 : ℝ)
  | 11 => (337999021 / 200000000000 : ℝ)
  | 12 => (1715052833 / 1000000000000 : ℝ)
  | 13 => (870129717 / 500000000000 : ℝ)
  | 14 => (1765613059 / 1000000000000 : ℝ)
  | 15 => (895555901 / 500000000000 : ℝ)
  | 16 => (1816753689 / 1000000000000 : ℝ)
  | 17 => (368507337 / 200000000000 : ℝ)
  | 18 => (186845869 / 100000000000 : ℝ)
  | 19 => (1894517539 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch036Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (289593909 / 200000000000 : ℝ)
  | 1 => (1471449983 / 1000000000000 : ℝ)
  | 2 => (299018909 / 200000000000 : ℝ)
  | 3 => (379725489 / 250000000000 : ℝ)
  | 4 => (1542870889 / 1000000000000 : ℝ)
  | 5 => (39174999 / 25000000000 : ℝ)
  | 6 => (397821933 / 250000000000 : ℝ)
  | 7 => (201966589 / 125000000000 : ℝ)
  | 8 => (1640333349 / 1000000000000 : ℝ)
  | 9 => (416272009 / 250000000000 : ℝ)
  | 10 => (844997553 / 500000000000 : ℝ)
  | 11 => (857526417 / 500000000000 : ℝ)
  | 12 => (348051887 / 200000000000 : ℝ)
  | 13 => (88280653 / 50000000000 : ℝ)
  | 14 => (1791111803 / 1000000000000 : ℝ)
  | 15 => (181675369 / 100000000000 : ℝ)
  | 16 => (921268343 / 500000000000 : ℝ)
  | 17 => (1868458691 / 1000000000000 : ℝ)
  | 18 => (94725877 / 50000000000 : ℝ)
  | 19 => (1920710999 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch036Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((720 : ℝ) + (j.val : ℝ)) / 1600)
      (((720 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch036Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch036Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((720 : ℝ) + (j.val : ℝ)) / 1600)
    (((720 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch036Neg100WeightLower j.val) (hpThetaShiftTwoBatch036Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch036Neg100WeightLower, hpThetaShiftTwoBatch036Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch036Neg100_integral_bounds :
    (2038490409 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (33623547 / 8000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (720 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch036Lower hpThetaJensenCellsBatch036Upper
    hpThetaShiftTwoBatch036Neg100WeightLower hpThetaShiftTwoBatch036Neg100WeightUpper hpThetaJensenCellsBatch036_bounds hpThetaShiftTwoBatch036Neg100_weight_bounds
  have hl : (2038490409 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch036Lower j * hpThetaShiftTwoBatch036Neg100WeightLower j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftTwoBatch036Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftTwoBatch036Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch036Lower j * hpThetaShiftTwoBatch036Neg100WeightUpper j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftTwoBatch036Neg100WeightUpper j) / 1600) ≤ (33623547 / 8000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftTwoBatch036Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (720 : ℝ) / 1600 = 36 / 80 by norm_num,
    show ((720 : ℝ) + 20) / 1600 = (36 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch036Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-241166447 / 500000000000 : ℝ)
  | 1 => (-477717879 / 1000000000000 : ℝ)
  | 2 => (-472969719 / 1000000000000 : ℝ)
  | 3 => (-14627721 / 31250000000 : ℝ)
  | 4 => (-28941787 / 62500000000 : ℝ)
  | 5 => (-45791293 / 100000000000 : ℝ)
  | 6 => (-28288671 / 62500000000 : ℝ)
  | 7 => (-447184653 / 1000000000000 : ℝ)
  | 8 => (-17664373 / 40000000000 : ℝ)
  | 9 => (-435891391 / 1000000000000 : ℝ)
  | 10 => (-430029487 / 1000000000000 : ℝ)
  | 11 => (-424022247 / 1000000000000 : ℝ)
  | 12 => (-26116769 / 62500000000 : ℝ)
  | 13 => (-82313257 / 200000000000 : ℝ)
  | 14 => (-202557409 / 500000000000 : ℝ)
  | 15 => (-398512527 / 1000000000000 : ℝ)
  | 16 => (-78351607 / 200000000000 : ℝ)
  | 17 => (-192424981 / 500000000000 : ℝ)
  | 18 => (-377786927 / 1000000000000 : ℝ)
  | 19 => (-370567547 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch036Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-238858939 / 500000000000 : ℝ)
  | 1 => (-236484859 / 500000000000 : ℝ)
  | 2 => (-468087071 / 1000000000000 : ℝ)
  | 3 => (-463068591 / 1000000000000 : ℝ)
  | 4 => (-457912929 / 1000000000000 : ℝ)
  | 5 => (-90523747 / 200000000000 : ℝ)
  | 6 => (-111796163 / 250000000000 : ℝ)
  | 7 => (-110402331 / 250000000000 : ℝ)
  | 8 => (-43589139 / 100000000000 : ℝ)
  | 9 => (-215014743 / 500000000000 : ℝ)
  | 10 => (-212011123 / 500000000000 : ℝ)
  | 11 => (-417868303 / 1000000000000 : ℝ)
  | 12 => (-102891571 / 250000000000 : ℝ)
  | 13 => (-405114817 / 1000000000000 : ℝ)
  | 14 => (-199256263 / 500000000000 : ℝ)
  | 15 => (-195879017 / 500000000000 : ℝ)
  | 16 => (-384849961 / 1000000000000 : ℝ)
  | 17 => (-188893463 / 500000000000 : ℝ)
  | 18 => (-185283773 / 500000000000 : ℝ)
  | 19 => (-90797609 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch036Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((720 : ℝ) + (j.val : ℝ)) / 1600)
      (((720 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch036Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch036Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((720 : ℝ) + (j.val : ℝ)) / 1600)
    (((720 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch036Neg65WeightLower j.val) (hpThetaShiftTwoBatch036Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch036Neg65WeightLower, hpThetaShiftTwoBatch036Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch036Neg65_integral_bounds :
    (-1083974889 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-210528973 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (720 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch036Lower hpThetaJensenCellsBatch036Upper
    hpThetaShiftTwoBatch036Neg65WeightLower hpThetaShiftTwoBatch036Neg65WeightUpper hpThetaJensenCellsBatch036_bounds hpThetaShiftTwoBatch036Neg65_weight_bounds
  have hl : (-1083974889 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch036Lower j * hpThetaShiftTwoBatch036Neg65WeightLower j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftTwoBatch036Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftTwoBatch036Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch036Lower j * hpThetaShiftTwoBatch036Neg65WeightUpper j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftTwoBatch036Neg65WeightUpper j) / 1600) ≤ (-210528973 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftTwoBatch036Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (720 : ℝ) / 1600 = 36 / 80 by norm_num,
    show ((720 : ℝ) + 20) / 1600 = (36 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch036Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-21892591 / 25000000000 : ℝ)
  | 1 => (-220307693 / 250000000000 : ℝ)
  | 2 => (-35469571 / 40000000000 : ℝ)
  | 3 => (-446114211 / 500000000000 : ℝ)
  | 4 => (-22442437 / 25000000000 : ℝ)
  | 5 => (-903145707 / 1000000000000 : ℝ)
  | 6 => (-227143089 / 250000000000 : ℝ)
  | 7 => (-36559067 / 40000000000 : ℝ)
  | 8 => (-919357903 / 1000000000000 : ℝ)
  | 9 => (-115589409 / 125000000000 : ℝ)
  | 10 => (-93004801 / 100000000000 : ℝ)
  | 11 => (-187071067 / 200000000000 : ℝ)
  | 12 => (-940636461 / 1000000000000 : ℝ)
  | 13 => (-945890593 / 1000000000000 : ℝ)
  | 14 => (-237779233 / 250000000000 : ℝ)
  | 15 => (-956314669 / 1000000000000 : ℝ)
  | 16 => (-60092687 / 62500000000 : ℝ)
  | 17 => (-483310539 / 500000000000 : ℝ)
  | 18 => (-9717281 / 10000000000 : ℝ)
  | 19 => (-976803223 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch036Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-435079299 / 500000000000 : ℝ)
  | 1 => (-875703639 / 1000000000000 : ℝ)
  | 2 => (-881230771 / 1000000000000 : ℝ)
  | 3 => (-443369637 / 500000000000 : ℝ)
  | 4 => (-892228421 / 1000000000000 : ℝ)
  | 5 => (-897697479 / 1000000000000 : ℝ)
  | 6 => (-451572853 / 500000000000 : ℝ)
  | 7 => (-181714471 / 200000000000 : ℝ)
  | 8 => (-456988337 / 500000000000 : ℝ)
  | 9 => (-459678951 / 500000000000 : ℝ)
  | 10 => (-924715271 / 1000000000000 : ℝ)
  | 11 => (-930048009 / 1000000000000 : ℝ)
  | 12 => (-467677667 / 500000000000 : ℝ)
  | 13 => (-47031823 / 50000000000 : ℝ)
  | 14 => (-29559081 / 31250000000 : ℝ)
  | 15 => (-951116931 / 1000000000000 : ℝ)
  | 16 => (-239078667 / 250000000000 : ℝ)
  | 17 => (-961482991 / 1000000000000 : ℝ)
  | 18 => (-966621077 / 1000000000000 : ℝ)
  | 19 => (-971728099 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch036Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((720 : ℝ) + (j.val : ℝ)) / 1600)
      (((720 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch036Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch036Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((720 : ℝ) + (j.val : ℝ)) / 1600)
    (((720 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch036Neg45WeightLower j.val) (hpThetaShiftTwoBatch036Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch036Neg45WeightLower, hpThetaShiftTwoBatch036Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch036Neg45_integral_bounds :
    (-580916729 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-2274685357 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (720 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch036Lower hpThetaJensenCellsBatch036Upper
    hpThetaShiftTwoBatch036Neg45WeightLower hpThetaShiftTwoBatch036Neg45WeightUpper hpThetaJensenCellsBatch036_bounds hpThetaShiftTwoBatch036Neg45_weight_bounds
  have hl : (-580916729 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch036Lower j * hpThetaShiftTwoBatch036Neg45WeightLower j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftTwoBatch036Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftTwoBatch036Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch036Lower j * hpThetaShiftTwoBatch036Neg45WeightUpper j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftTwoBatch036Neg45WeightUpper j) / 1600) ≤ (-2274685357 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftTwoBatch036Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (720 : ℝ) / 1600 = 36 / 80 by norm_num,
    show ((720 : ℝ) + 20) / 1600 = (36 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch036Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-38898943 / 500000000000 : ℝ)
  | 1 => (-83727499 / 1000000000000 : ℝ)
  | 2 => (-89706359 / 1000000000000 : ℝ)
  | 3 => (-47867281 / 500000000000 : ℝ)
  | 4 => (-50906099 / 500000000000 : ℝ)
  | 5 => (-107939359 / 1000000000000 : ℝ)
  | 6 => (-57058067 / 500000000000 : ℝ)
  | 7 => (-120342609 / 1000000000000 : ℝ)
  | 8 => (-126618869 / 1000000000000 : ℝ)
  | 9 => (-132944997 / 1000000000000 : ℝ)
  | 10 => (-5572843 / 40000000000 : ℝ)
  | 11 => (-7287359 / 50000000000 : ℝ)
  | 12 => (-152223391 / 1000000000000 : ℝ)
  | 13 => (-79374891 / 500000000000 : ℝ)
  | 14 => (-82663213 / 500000000000 : ℝ)
  | 15 => (-34390679 / 200000000000 : ℝ)
  | 16 => (-44657689 / 250000000000 : ℝ)
  | 17 => (-92679289 / 500000000000 : ℝ)
  | 18 => (-48034231 / 250000000000 : ℝ)
  | 19 => (-198965857 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch036Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-71917423 / 1000000000000 : ℝ)
  | 1 => (-15559577 / 200000000000 : ℝ)
  | 2 => (-41863749 / 500000000000 : ℝ)
  | 3 => (-44853179 / 500000000000 : ℝ)
  | 4 => (-95734561 / 1000000000000 : ℝ)
  | 5 => (-101812197 / 1000000000000 : ℝ)
  | 6 => (-53969679 / 500000000000 : ℝ)
  | 7 => (-114116133 / 1000000000000 : ℝ)
  | 8 => (-7521413 / 62500000000 : ℝ)
  | 9 => (-31654717 / 250000000000 : ℝ)
  | 10 => (-33236249 / 250000000000 : ℝ)
  | 11 => (-69660537 / 500000000000 : ℝ)
  | 12 => (-145747179 / 1000000000000 : ℝ)
  | 13 => (-15222339 / 100000000000 : ℝ)
  | 14 => (-158749781 / 1000000000000 : ℝ)
  | 15 => (-6613057 / 40000000000 : ℝ)
  | 16 => (-85976697 / 500000000000 : ℝ)
  | 17 => (-35726151 / 200000000000 : ℝ)
  | 18 => (-185358577 / 1000000000000 : ℝ)
  | 19 => (-192136923 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch036Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((720 : ℝ) + (j.val : ℝ)) / 1600)
      (((720 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch036Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch036Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((720 : ℝ) + (j.val : ℝ)) / 1600)
    (((720 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch036Neg25WeightLower j.val) (hpThetaShiftTwoBatch036Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch036Neg25WeightLower, hpThetaShiftTwoBatch036Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch036Neg25_integral_bounds :
    (-13608393 / 40000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-319293067 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (720 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch036Lower hpThetaJensenCellsBatch036Upper
    hpThetaShiftTwoBatch036Neg25WeightLower hpThetaShiftTwoBatch036Neg25WeightUpper hpThetaJensenCellsBatch036_bounds hpThetaShiftTwoBatch036Neg25_weight_bounds
  have hl : (-13608393 / 40000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch036Lower j * hpThetaShiftTwoBatch036Neg25WeightLower j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftTwoBatch036Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftTwoBatch036Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch036Lower j * hpThetaShiftTwoBatch036Neg25WeightUpper j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftTwoBatch036Neg25WeightUpper j) / 1600) ≤ (-319293067 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftTwoBatch036Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (720 : ℝ) / 1600 = 36 / 80 by norm_num,
    show ((720 : ℝ) + 20) / 1600 = (36 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch036Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch036Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch036Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch036Neg25_integral_bounds
end HodgeProofHP
