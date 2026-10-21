/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch036

/-! Exact signed weight and batch integral certificates, batch 36 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch036Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3087443 / 1000000000000 : ℝ)
  | 1 => (3293991 / 1000000000000 : ℝ)
  | 2 => (3504399 / 1000000000000 : ℝ)
  | 3 => (1859353 / 500000000000 : ℝ)
  | 4 => (1968473 / 500000000000 : ℝ)
  | 5 => (2079579 / 500000000000 : ℝ)
  | 6 => (2192689 / 500000000000 : ℝ)
  | 7 => (2307821 / 500000000000 : ℝ)
  | 8 => (4849989 / 1000000000000 : ℝ)
  | 9 => (5088453 / 1000000000000 : ℝ)
  | 10 => (5331071 / 1000000000000 : ℝ)
  | 11 => (5577881 / 1000000000000 : ℝ)
  | 12 => (5828917 / 1000000000000 : ℝ)
  | 13 => (6084217 / 1000000000000 : ℝ)
  | 14 => (1268763 / 200000000000 : ℝ)
  | 15 => (6607749 / 1000000000000 : ℝ)
  | 16 => (1719013 / 250000000000 : ℝ)
  | 17 => (3574381 / 500000000000 : ℝ)
  | 18 => (7425913 / 1000000000000 : ℝ)
  | 19 => (385377 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch036Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (411749 / 125000000000 : ℝ)
  | 1 => (8761 / 2500000000 : ℝ)
  | 2 => (3718707 / 1000000000000 : ℝ)
  | 3 => (3936947 / 1000000000000 : ℝ)
  | 4 => (4159159 / 1000000000000 : ℝ)
  | 5 => (4385379 / 1000000000000 : ℝ)
  | 6 => (4615643 / 1000000000000 : ℝ)
  | 7 => (484999 / 100000000000 : ℝ)
  | 8 => (2544227 / 500000000000 : ℝ)
  | 9 => (41649 / 7812500000 : ℝ)
  | 10 => (2788941 / 500000000000 : ℝ)
  | 11 => (2914459 / 500000000000 : ℝ)
  | 12 => (3042109 / 500000000000 : ℝ)
  | 13 => (792977 / 125000000000 : ℝ)
  | 14 => (26431 / 4000000000 : ℝ)
  | 15 => (6876053 / 1000000000000 : ℝ)
  | 16 => (7148763 / 1000000000000 : ℝ)
  | 17 => (3712957 / 500000000000 : ℝ)
  | 18 => (7707541 / 1000000000000 : ℝ)
  | 19 => (7993679 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch036Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((720 : ℝ) + (j.val : ℝ)) / 1600)
      (((720 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch036Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch036Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((720 : ℝ) + (j.val : ℝ)) / 1600)
    (((720 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch036Neg100WeightLower j.val) (hpThetaShiftThreeBatch036Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch036Neg100WeightLower, hpThetaShiftThreeBatch036Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch036Neg100_integral_bounds :
    (403491 / 31250000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (13727297 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (720 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch036Lower hpThetaJensenCellsBatch036Upper
    hpThetaShiftThreeBatch036Neg100WeightLower hpThetaShiftThreeBatch036Neg100WeightUpper hpThetaJensenCellsBatch036_bounds hpThetaShiftThreeBatch036Neg100_weight_bounds
  have hl : (403491 / 31250000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch036Lower j * hpThetaShiftThreeBatch036Neg100WeightLower j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftThreeBatch036Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftThreeBatch036Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch036Lower j * hpThetaShiftThreeBatch036Neg100WeightUpper j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftThreeBatch036Neg100WeightUpper j) / 1600) ≤ (13727297 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftThreeBatch036Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (720 : ℝ) / 1600 = 36 / 80 by norm_num,
    show ((720 : ℝ) + 20) / 1600 = (36 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch036Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-11068993 / 1000000000000 : ℝ)
  | 1 => (-11119827 / 1000000000000 : ℝ)
  | 2 => (-1396203 / 125000000000 : ℝ)
  | 3 => (-2804589 / 250000000000 : ℝ)
  | 4 => (-2816499 / 250000000000 : ℝ)
  | 5 => (-5656257 / 500000000000 : ℝ)
  | 6 => (-2839471 / 250000000000 : ℝ)
  | 7 => (-11402077 / 1000000000000 : ℝ)
  | 8 => (-11445063 / 1000000000000 : ℝ)
  | 9 => (-11486813 / 1000000000000 : ℝ)
  | 10 => (-11527297 / 1000000000000 : ℝ)
  | 11 => (-5783243 / 500000000000 : ℝ)
  | 12 => (-11604349 / 1000000000000 : ℝ)
  | 13 => (-1455107 / 125000000000 : ℝ)
  | 14 => (-1459497 / 125000000000 : ℝ)
  | 15 => (-11709677 / 1000000000000 : ℝ)
  | 16 => (-1467741 / 125000000000 : ℝ)
  | 17 => (-11772697 / 1000000000000 : ℝ)
  | 18 => (-368811 / 31250000000 : ℝ)
  | 19 => (-11829659 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch036Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-11017147 / 1000000000000 : ℝ)
  | 1 => (-172953 / 15625000000 : ℝ)
  | 2 => (-5559913 / 500000000000 : ℝ)
  | 3 => (-11169623 / 1000000000000 : ℝ)
  | 4 => (-2243671 / 200000000000 : ℝ)
  | 5 => (-2253199 / 200000000000 : ℝ)
  | 6 => (-11312513 / 1000000000000 : ℝ)
  | 7 => (-11357883 / 1000000000000 : ℝ)
  | 8 => (-2850519 / 250000000000 : ℝ)
  | 9 => (-5722531 / 500000000000 : ℝ)
  | 10 => (-2871703 / 250000000000 : ℝ)
  | 11 => (-90057 / 7812500000 : ℝ)
  | 12 => (-2313297 / 200000000000 : ℝ)
  | 13 => (-2901087 / 250000000000 : ℝ)
  | 14 => (-2328171 / 200000000000 : ℝ)
  | 15 => (-467039 / 40000000000 : ℝ)
  | 16 => (-2927419 / 250000000000 : ℝ)
  | 17 => (-11741927 / 1000000000000 : ℝ)
  | 18 => (-1471587 / 125000000000 : ℝ)
  | 19 => (-11801951 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch036Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((720 : ℝ) + (j.val : ℝ)) / 1600)
      (((720 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch036Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch036Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((720 : ℝ) + (j.val : ℝ)) / 1600)
    (((720 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch036Neg70WeightLower j.val) (hpThetaShiftThreeBatch036Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch036Neg70WeightLower, hpThetaShiftThreeBatch036Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch036Neg70_integral_bounds :
    (-1152259 / 40000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-28261709 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (720 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch036Lower hpThetaJensenCellsBatch036Upper
    hpThetaShiftThreeBatch036Neg70WeightLower hpThetaShiftThreeBatch036Neg70WeightUpper hpThetaJensenCellsBatch036_bounds hpThetaShiftThreeBatch036Neg70_weight_bounds
  have hl : (-1152259 / 40000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch036Lower j * hpThetaShiftThreeBatch036Neg70WeightLower j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftThreeBatch036Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftThreeBatch036Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch036Lower j * hpThetaShiftThreeBatch036Neg70WeightUpper j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftThreeBatch036Neg70WeightUpper j) / 1600) ≤ (-28261709 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftThreeBatch036Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (720 : ℝ) / 1600 = 36 / 80 by norm_num,
    show ((720 : ℝ) + 20) / 1600 = (36 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch036Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3547703 / 500000000000 : ℝ)
  | 1 => (-57833 / 8000000000 : ℝ)
  | 2 => (-3681983 / 500000000000 : ℝ)
  | 3 => (-749993 / 100000000000 : ℝ)
  | 4 => (-7637017 / 1000000000000 : ℝ)
  | 5 => (-1943807 / 250000000000 : ℝ)
  | 6 => (-7914563 / 1000000000000 : ℝ)
  | 7 => (-4027511 / 500000000000 : ℝ)
  | 8 => (-2049151 / 250000000000 : ℝ)
  | 9 => (-8339311 / 1000000000000 : ℝ)
  | 10 => (-424157 / 50000000000 : ℝ)
  | 11 => (-2157023 / 250000000000 : ℝ)
  | 12 => (-8774167 / 1000000000000 : ℝ)
  | 13 => (-8921363 / 1000000000000 : ℝ)
  | 14 => (-113371 / 12500000000 : ℝ)
  | 15 => (-9219117 / 1000000000000 : ℝ)
  | 16 => (-1171209 / 125000000000 : ℝ)
  | 17 => (-1904269 / 200000000000 : ℝ)
  | 18 => (-4837067 / 500000000000 : ℝ)
  | 19 => (-9828037 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch036Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6962807 / 1000000000000 : ℝ)
  | 1 => (-1419081 / 200000000000 : ℝ)
  | 2 => (-1807281 / 250000000000 : ℝ)
  | 3 => (-1472793 / 200000000000 : ℝ)
  | 4 => (-7499929 / 1000000000000 : ℝ)
  | 5 => (-954627 / 125000000000 : ℝ)
  | 6 => (-7775227 / 1000000000000 : ℝ)
  | 7 => (-3957281 / 500000000000 : ℝ)
  | 8 => (-8055021 / 1000000000000 : ℝ)
  | 9 => (-8196603 / 1000000000000 : ℝ)
  | 10 => (-833931 / 100000000000 : ℝ)
  | 11 => (-8483139 / 1000000000000 : ℝ)
  | 12 => (-8628091 / 1000000000000 : ℝ)
  | 13 => (-4387083 / 500000000000 : ℝ)
  | 14 => (-4460681 / 500000000000 : ℝ)
  | 15 => (-9069679 / 1000000000000 : ℝ)
  | 16 => (-2304779 / 250000000000 : ℝ)
  | 17 => (-9369671 / 1000000000000 : ℝ)
  | 18 => (-148771 / 15625000000 : ℝ)
  | 19 => (-9674133 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch036Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((720 : ℝ) + (j.val : ℝ)) / 1600)
      (((720 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch036Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch036Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((720 : ℝ) + (j.val : ℝ)) / 1600)
    (((720 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch036Neg45WeightLower j.val) (hpThetaShiftThreeBatch036Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch036Neg45WeightLower, hpThetaShiftThreeBatch036Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch036Neg45_integral_bounds :
    (-5269537 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-20399969 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (720 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch036Lower hpThetaJensenCellsBatch036Upper
    hpThetaShiftThreeBatch036Neg45WeightLower hpThetaShiftThreeBatch036Neg45WeightUpper hpThetaJensenCellsBatch036_bounds hpThetaShiftThreeBatch036Neg45_weight_bounds
  have hl : (-5269537 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch036Lower j * hpThetaShiftThreeBatch036Neg45WeightLower j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftThreeBatch036Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftThreeBatch036Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch036Lower j * hpThetaShiftThreeBatch036Neg45WeightUpper j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftThreeBatch036Neg45WeightUpper j) / 1600) ≤ (-20399969 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftThreeBatch036Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (720 : ℝ) / 1600 = 36 / 80 by norm_num,
    show ((720 : ℝ) + 20) / 1600 = (36 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch036Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (681191 / 50000000000 : ℝ)
  | 1 => (13632201 / 1000000000000 : ℝ)
  | 2 => (340993 / 25000000000 : ℝ)
  | 3 => (13646367 / 1000000000000 : ℝ)
  | 4 => (13652131 / 1000000000000 : ℝ)
  | 5 => (6828501 / 500000000000 : ℝ)
  | 6 => (13660969 / 1000000000000 : ℝ)
  | 7 => (13664021 / 1000000000000 : ℝ)
  | 8 => (3416537 / 250000000000 : ℝ)
  | 9 => (13667339 / 1000000000000 : ℝ)
  | 10 => (13666871 / 1000000000000 : ℝ)
  | 11 => (1366519 / 100000000000 : ℝ)
  | 12 => (13662529 / 1000000000000 : ℝ)
  | 13 => (13658879 / 1000000000000 : ℝ)
  | 14 => (13654227 / 1000000000000 : ℝ)
  | 15 => (13648563 / 1000000000000 : ℝ)
  | 16 => (21827 / 1600000000 : ℝ)
  | 17 => (13634153 / 1000000000000 : ℝ)
  | 18 => (2725077 / 200000000000 : ℝ)
  | 19 => (340389 / 25000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch036Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (6816101 / 500000000000 : ℝ)
  | 1 => (13639721 / 1000000000000 : ℝ)
  | 2 => (426449 / 31250000000 : ℝ)
  | 3 => (3413033 / 250000000000 : ℝ)
  | 4 => (13657003 / 1000000000000 : ℝ)
  | 5 => (1366097 / 100000000000 : ℝ)
  | 6 => (6832011 / 500000000000 : ℝ)
  | 7 => (13666149 / 1000000000000 : ℝ)
  | 8 => (683367 / 50000000000 : ℝ)
  | 9 => (13667621 / 1000000000000 : ℝ)
  | 10 => (2733517 / 200000000000 : ℝ)
  | 11 => (1708359 / 125000000000 : ℝ)
  | 12 => (13665191 / 1000000000000 : ℝ)
  | 13 => (1366253 / 100000000000 : ℝ)
  | 14 => (10671 / 781250000 : ℝ)
  | 15 => (3413557 / 250000000000 : ℝ)
  | 16 => (3412141 / 250000000000 : ℝ)
  | 17 => (3410469 / 250000000000 : ℝ)
  | 18 => (6817077 / 500000000000 : ℝ)
  | 19 => (6812693 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch036Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((720 : ℝ) + (j.val : ℝ)) / 1600)
      (((720 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch036Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch036Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((720 : ℝ) + (j.val : ℝ)) / 1600)
    (((720 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch036Neg25WeightLower j.val) (hpThetaShiftThreeBatch036Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch036Neg25WeightLower, hpThetaShiftThreeBatch036Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch036Neg25_integral_bounds :
    (33731041 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (8567657 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (720 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch036Lower hpThetaJensenCellsBatch036Upper
    hpThetaShiftThreeBatch036Neg25WeightLower hpThetaShiftThreeBatch036Neg25WeightUpper hpThetaJensenCellsBatch036_bounds hpThetaShiftThreeBatch036Neg25_weight_bounds
  have hl : (33731041 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch036Lower j * hpThetaShiftThreeBatch036Neg25WeightLower j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftThreeBatch036Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftThreeBatch036Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch036Lower j * hpThetaShiftThreeBatch036Neg25WeightUpper j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftThreeBatch036Neg25WeightUpper j) / 1600) ≤ (8567657 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftThreeBatch036Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (720 : ℝ) / 1600 = 36 / 80 by norm_num,
    show ((720 : ℝ) + 20) / 1600 = (36 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch036Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch036Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch036Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch036Neg25_integral_bounds
end HodgeProofHP
