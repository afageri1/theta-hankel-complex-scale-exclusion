/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch001

/-! Exact signed weight and batch integral certificates, batch 1 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch001Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (253 / 125000000000 : ℝ)
  | 1 => (123 / 50000000000 : ℝ)
  | 2 => (2961 / 1000000000000 : ℝ)
  | 3 => (221 / 62500000000 : ℝ)
  | 4 => (419 / 100000000000 : ℝ)
  | 5 => (493 / 100000000000 : ℝ)
  | 6 => (1441 / 250000000000 : ℝ)
  | 7 => (67 / 10000000000 : ℝ)
  | 8 => (121 / 15625000000 : ℝ)
  | 9 => (1781 / 200000000000 : ℝ)
  | 10 => (10191 / 1000000000000 : ℝ)
  | 11 => (11611 / 1000000000000 : ℝ)
  | 12 => (13173 / 1000000000000 : ℝ)
  | 13 => (14887 / 1000000000000 : ℝ)
  | 14 => (8381 / 500000000000 : ℝ)
  | 15 => (2351 / 125000000000 : ℝ)
  | 16 => (10517 / 500000000000 : ℝ)
  | 17 => (469 / 20000000000 : ℝ)
  | 18 => (26067 / 1000000000000 : ℝ)
  | 19 => (14447 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch001Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2461 / 1000000000000 : ℝ)
  | 1 => (1481 / 500000000000 : ℝ)
  | 2 => (3537 / 1000000000000 : ℝ)
  | 3 => (4191 / 1000000000000 : ℝ)
  | 4 => (4931 / 1000000000000 : ℝ)
  | 5 => (1153 / 200000000000 : ℝ)
  | 6 => (6701 / 1000000000000 : ℝ)
  | 7 => (1549 / 200000000000 : ℝ)
  | 8 => (4453 / 500000000000 : ℝ)
  | 9 => (637 / 62500000000 : ℝ)
  | 10 => (2903 / 250000000000 : ℝ)
  | 11 => (6587 / 500000000000 : ℝ)
  | 12 => (1861 / 125000000000 : ℝ)
  | 13 => (16763 / 1000000000000 : ℝ)
  | 14 => (18809 / 1000000000000 : ℝ)
  | 15 => (4207 / 200000000000 : ℝ)
  | 16 => (23451 / 1000000000000 : ℝ)
  | 17 => (6517 / 250000000000 : ℝ)
  | 18 => (5779 / 200000000000 : ℝ)
  | 19 => (6389 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch001Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((20 : ℝ) + (j.val : ℝ)) / 1600)
      (((20 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch001Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch001Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((20 : ℝ) + (j.val : ℝ)) / 1600)
    (((20 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch001Neg100WeightLower j.val) (hpThetaShiftTwoBatch001Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch001Neg100WeightLower, hpThetaShiftTwoBatch001Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch001Neg100_integral_bounds :
    (129451 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (295133 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (20 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch001Lower hpThetaJensenCellsBatch001Upper
    hpThetaShiftTwoBatch001Neg100WeightLower hpThetaShiftTwoBatch001Neg100WeightUpper hpThetaJensenCellsBatch001_bounds hpThetaShiftTwoBatch001Neg100_weight_bounds
  have hl : (129451 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch001Lower j * hpThetaShiftTwoBatch001Neg100WeightLower j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftTwoBatch001Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftTwoBatch001Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch001Lower j * hpThetaShiftTwoBatch001Neg100WeightUpper j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftTwoBatch001Neg100WeightUpper j) / 1600) ≤ (295133 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftTwoBatch001Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (20 : ℝ) / 1600 = 1 / 80 by norm_num,
    show ((20 : ℝ) + 20) / 1600 = (1 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch001Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (507 / 250000000000 : ℝ)
  | 1 => (77 / 31250000000 : ℝ)
  | 2 => (2967 / 1000000000000 : ℝ)
  | 3 => (443 / 125000000000 : ℝ)
  | 4 => (21 / 5000000000 : ℝ)
  | 5 => (4943 / 1000000000000 : ℝ)
  | 6 => (289 / 50000000000 : ℝ)
  | 7 => (21 / 3125000000 : ℝ)
  | 8 => (7769 / 1000000000000 : ℝ)
  | 9 => (1117 / 125000000000 : ℝ)
  | 10 => (10229 / 1000000000000 : ℝ)
  | 11 => (11657 / 1000000000000 : ℝ)
  | 12 => (13229 / 1000000000000 : ℝ)
  | 13 => (7477 / 500000000000 : ℝ)
  | 14 => (16843 / 1000000000000 : ℝ)
  | 15 => (18903 / 1000000000000 : ℝ)
  | 16 => (21147 / 1000000000000 : ℝ)
  | 17 => (23583 / 1000000000000 : ℝ)
  | 18 => (26223 / 1000000000000 : ℝ)
  | 19 => (29077 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch001Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (493 / 200000000000 : ℝ)
  | 1 => (371 / 125000000000 : ℝ)
  | 2 => (709 / 200000000000 : ℝ)
  | 3 => (4201 / 1000000000000 : ℝ)
  | 4 => (309 / 62500000000 : ℝ)
  | 5 => (5781 / 1000000000000 : ℝ)
  | 6 => (6721 / 1000000000000 : ℝ)
  | 7 => (777 / 100000000000 : ℝ)
  | 8 => (8937 / 1000000000000 : ℝ)
  | 9 => (1023 / 100000000000 : ℝ)
  | 10 => (5829 / 500000000000 : ℝ)
  | 11 => (1323 / 100000000000 : ℝ)
  | 12 => (2991 / 200000000000 : ℝ)
  | 13 => (4211 / 250000000000 : ℝ)
  | 14 => (2363 / 125000000000 : ℝ)
  | 15 => (5287 / 250000000000 : ℝ)
  | 16 => (737 / 31250000000 : ℝ)
  | 17 => (1639 / 62500000000 : ℝ)
  | 18 => (14539 / 500000000000 : ℝ)
  | 19 => (32157 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch001Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((20 : ℝ) + (j.val : ℝ)) / 1600)
      (((20 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch001Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch001Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((20 : ℝ) + (j.val : ℝ)) / 1600)
    (((20 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch001Neg65WeightLower j.val) (hpThetaShiftTwoBatch001Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch001Neg65WeightLower, hpThetaShiftTwoBatch001Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch001Neg65_integral_bounds :
    (65031 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (1483 / 5000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (20 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch001Lower hpThetaJensenCellsBatch001Upper
    hpThetaShiftTwoBatch001Neg65WeightLower hpThetaShiftTwoBatch001Neg65WeightUpper hpThetaJensenCellsBatch001_bounds hpThetaShiftTwoBatch001Neg65_weight_bounds
  have hl : (65031 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch001Lower j * hpThetaShiftTwoBatch001Neg65WeightLower j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftTwoBatch001Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftTwoBatch001Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch001Lower j * hpThetaShiftTwoBatch001Neg65WeightUpper j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftTwoBatch001Neg65WeightUpper j) / 1600) ≤ (1483 / 5000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftTwoBatch001Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (20 : ℝ) / 1600 = 1 / 80 by norm_num,
    show ((20 : ℝ) + 20) / 1600 = (1 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch001Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (203 / 100000000000 : ℝ)
  | 1 => (2467 / 1000000000000 : ℝ)
  | 2 => (2971 / 1000000000000 : ℝ)
  | 3 => (887 / 250000000000 : ℝ)
  | 4 => (841 / 200000000000 : ℝ)
  | 5 => (99 / 20000000000 : ℝ)
  | 6 => (579 / 100000000000 : ℝ)
  | 7 => (6731 / 1000000000000 : ℝ)
  | 8 => (7783 / 1000000000000 : ℝ)
  | 9 => (8953 / 1000000000000 : ℝ)
  | 10 => (41 / 4000000000 : ℝ)
  | 11 => (11683 / 1000000000000 : ℝ)
  | 12 => (13261 / 1000000000000 : ℝ)
  | 13 => (14993 / 1000000000000 : ℝ)
  | 14 => (2111 / 125000000000 : ℝ)
  | 15 => (9479 / 500000000000 : ℝ)
  | 16 => (21211 / 1000000000000 : ℝ)
  | 17 => (23659 / 1000000000000 : ℝ)
  | 18 => (3289 / 125000000000 : ℝ)
  | 19 => (29181 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch001Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (617 / 250000000000 : ℝ)
  | 1 => (743 / 250000000000 : ℝ)
  | 2 => (3549 / 1000000000000 : ℝ)
  | 3 => (2103 / 500000000000 : ℝ)
  | 4 => (4951 / 1000000000000 : ℝ)
  | 5 => (5791 / 1000000000000 : ℝ)
  | 6 => (1683 / 250000000000 : ℝ)
  | 7 => (973 / 125000000000 : ℝ)
  | 8 => (4477 / 500000000000 : ℝ)
  | 9 => (10251 / 1000000000000 : ℝ)
  | 10 => (2921 / 250000000000 : ℝ)
  | 11 => (6631 / 500000000000 : ℝ)
  | 12 => (7497 / 500000000000 : ℝ)
  | 13 => (16889 / 1000000000000 : ℝ)
  | 14 => (18959 / 1000000000000 : ℝ)
  | 15 => (5303 / 250000000000 : ℝ)
  | 16 => (1183 / 50000000000 : ℝ)
  | 17 => (26313 / 1000000000000 : ℝ)
  | 18 => (14591 / 500000000000 : ℝ)
  | 19 => (16139 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch001Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((20 : ℝ) + (j.val : ℝ)) / 1600)
      (((20 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch001Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch001Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((20 : ℝ) + (j.val : ℝ)) / 1600)
    (((20 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch001Neg45WeightLower j.val) (hpThetaShiftTwoBatch001Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch001Neg45WeightLower, hpThetaShiftTwoBatch001Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch001Neg45_integral_bounds :
    (130409 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (59487 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (20 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch001Lower hpThetaJensenCellsBatch001Upper
    hpThetaShiftTwoBatch001Neg45WeightLower hpThetaShiftTwoBatch001Neg45WeightUpper hpThetaJensenCellsBatch001_bounds hpThetaShiftTwoBatch001Neg45_weight_bounds
  have hl : (130409 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch001Lower j * hpThetaShiftTwoBatch001Neg45WeightLower j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftTwoBatch001Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftTwoBatch001Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch001Lower j * hpThetaShiftTwoBatch001Neg45WeightUpper j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftTwoBatch001Neg45WeightUpper j) / 1600) ≤ (59487 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftTwoBatch001Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (20 : ℝ) / 1600 = 1 / 80 by norm_num,
    show ((20 : ℝ) + 20) / 1600 = (1 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch001Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (127 / 62500000000 : ℝ)
  | 1 => (2469 / 1000000000000 : ℝ)
  | 2 => (1487 / 500000000000 : ℝ)
  | 3 => (111 / 31250000000 : ℝ)
  | 4 => (4211 / 1000000000000 : ℝ)
  | 5 => (4957 / 1000000000000 : ℝ)
  | 6 => (5799 / 1000000000000 : ℝ)
  | 7 => (6743 / 1000000000000 : ℝ)
  | 8 => (7797 / 1000000000000 : ℝ)
  | 9 => (8971 / 1000000000000 : ℝ)
  | 10 => (321 / 31250000000 : ℝ)
  | 11 => (1171 / 100000000000 : ℝ)
  | 12 => (13293 / 1000000000000 : ℝ)
  | 13 => (15031 / 1000000000000 : ℝ)
  | 14 => (8467 / 500000000000 : ℝ)
  | 15 => (19013 / 1000000000000 : ℝ)
  | 16 => (5319 / 250000000000 : ℝ)
  | 17 => (4747 / 200000000000 : ℝ)
  | 18 => (26401 / 1000000000000 : ℝ)
  | 19 => (5857 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch001Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (247 / 100000000000 : ℝ)
  | 1 => (119 / 40000000000 : ℝ)
  | 2 => (3553 / 1000000000000 : ℝ)
  | 3 => (1053 / 250000000000 : ℝ)
  | 4 => (2479 / 500000000000 : ℝ)
  | 5 => (29 / 5000000000 : ℝ)
  | 6 => (843 / 125000000000 : ℝ)
  | 7 => (3899 / 500000000000 : ℝ)
  | 8 => (2243 / 250000000000 : ℝ)
  | 9 => (10273 / 1000000000000 : ℝ)
  | 10 => (11711 / 1000000000000 : ℝ)
  | 11 => (6647 / 500000000000 : ℝ)
  | 12 => (1879 / 125000000000 : ℝ)
  | 13 => (3387 / 200000000000 : ℝ)
  | 14 => (9507 / 500000000000 : ℝ)
  | 15 => (21277 / 1000000000000 : ℝ)
  | 16 => (2967 / 125000000000 : ℝ)
  | 17 => (13201 / 500000000000 : ℝ)
  | 18 => (14643 / 500000000000 : ℝ)
  | 19 => (81 / 2500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch001Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((20 : ℝ) + (j.val : ℝ)) / 1600)
      (((20 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch001Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch001Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((20 : ℝ) + (j.val : ℝ)) / 1600)
    (((20 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch001Neg25WeightLower j.val) (hpThetaShiftTwoBatch001Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch001Neg25WeightLower, hpThetaShiftTwoBatch001Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch001Neg25_integral_bounds :
    (65379 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (149137 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (20 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch001Lower hpThetaJensenCellsBatch001Upper
    hpThetaShiftTwoBatch001Neg25WeightLower hpThetaShiftTwoBatch001Neg25WeightUpper hpThetaJensenCellsBatch001_bounds hpThetaShiftTwoBatch001Neg25_weight_bounds
  have hl : (65379 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch001Lower j * hpThetaShiftTwoBatch001Neg25WeightLower j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftTwoBatch001Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftTwoBatch001Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch001Lower j * hpThetaShiftTwoBatch001Neg25WeightUpper j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftTwoBatch001Neg25WeightUpper j) / 1600) ≤ (149137 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftTwoBatch001Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (20 : ℝ) / 1600 = 1 / 80 by norm_num,
    show ((20 : ℝ) + 20) / 1600 = (1 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch001Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch001Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch001Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch001Neg25_integral_bounds
end HodgeProofHP
