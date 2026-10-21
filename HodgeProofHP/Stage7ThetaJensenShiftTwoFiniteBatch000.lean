/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch000

/-! Exact signed weight and batch integral certificates, batch 0 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch000Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (0 / 1 : ℝ)
  | 1 => (0 / 1 : ℝ)
  | 2 => (0 / 1 : ℝ)
  | 3 => (1 / 1000000000000 : ℝ)
  | 4 => (3 / 1000000000000 : ℝ)
  | 5 => (7 / 1000000000000 : ℝ)
  | 6 => (1 / 62500000000 : ℝ)
  | 7 => (3 / 100000000000 : ℝ)
  | 8 => (13 / 250000000000 : ℝ)
  | 9 => (83 / 1000000000000 : ℝ)
  | 10 => (127 / 1000000000000 : ℝ)
  | 11 => (37 / 200000000000 : ℝ)
  | 12 => (263 / 1000000000000 : ℝ)
  | 13 => (181 / 500000000000 : ℝ)
  | 14 => (487 / 1000000000000 : ℝ)
  | 15 => (321 / 500000000000 : ℝ)
  | 16 => (83 / 100000000000 : ℝ)
  | 17 => (529 / 500000000000 : ℝ)
  | 18 => (1329 / 1000000000000 : ℝ)
  | 19 => (33 / 20000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch000Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1 / 1000000000000 : ℝ)
  | 1 => (1 / 1000000000000 : ℝ)
  | 2 => (1 / 500000000000 : ℝ)
  | 3 => (1 / 250000000000 : ℝ)
  | 4 => (1 / 125000000000 : ℝ)
  | 5 => (17 / 1000000000000 : ℝ)
  | 6 => (31 / 1000000000000 : ℝ)
  | 7 => (53 / 1000000000000 : ℝ)
  | 8 => (21 / 250000000000 : ℝ)
  | 9 => (1 / 7812500000 : ℝ)
  | 10 => (93 / 500000000000 : ℝ)
  | 11 => (33 / 125000000000 : ℝ)
  | 12 => (363 / 1000000000000 : ℝ)
  | 13 => (61 / 125000000000 : ℝ)
  | 14 => (643 / 1000000000000 : ℝ)
  | 15 => (831 / 1000000000000 : ℝ)
  | 16 => (1059 / 1000000000000 : ℝ)
  | 17 => (133 / 100000000000 : ℝ)
  | 18 => (1651 / 1000000000000 : ℝ)
  | 19 => (81 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch000Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((0 : ℝ) + (j.val : ℝ)) / 1600)
      (((0 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch000Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch000Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((0 : ℝ) + (j.val : ℝ)) / 1600)
    (((0 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch000Neg100WeightLower j.val) (hpThetaShiftTwoBatch000Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch000Neg100WeightLower, hpThetaShiftTwoBatch000Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch000Neg100_integral_bounds :
    (7903 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (10279 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (0 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch000Lower hpThetaJensenCellsBatch000Upper
    hpThetaShiftTwoBatch000Neg100WeightLower hpThetaShiftTwoBatch000Neg100WeightUpper hpThetaJensenCellsBatch000_bounds hpThetaShiftTwoBatch000Neg100_weight_bounds
  have hl : (7903 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch000Lower j * hpThetaShiftTwoBatch000Neg100WeightLower j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftTwoBatch000Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftTwoBatch000Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch000Lower j * hpThetaShiftTwoBatch000Neg100WeightUpper j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftTwoBatch000Neg100WeightUpper j) / 1600) ≤ (10279 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftTwoBatch000Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (0 : ℝ) / 1600 = 0 / 80 by norm_num,
    show ((0 : ℝ) + 20) / 1600 = (0 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch000Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (0 / 1 : ℝ)
  | 1 => (0 / 1 : ℝ)
  | 2 => (0 / 1 : ℝ)
  | 3 => (1 / 1000000000000 : ℝ)
  | 4 => (3 / 1000000000000 : ℝ)
  | 5 => (7 / 1000000000000 : ℝ)
  | 6 => (1 / 62500000000 : ℝ)
  | 7 => (3 / 100000000000 : ℝ)
  | 8 => (13 / 250000000000 : ℝ)
  | 9 => (83 / 1000000000000 : ℝ)
  | 10 => (127 / 1000000000000 : ℝ)
  | 11 => (37 / 200000000000 : ℝ)
  | 12 => (263 / 1000000000000 : ℝ)
  | 13 => (181 / 500000000000 : ℝ)
  | 14 => (487 / 1000000000000 : ℝ)
  | 15 => (321 / 500000000000 : ℝ)
  | 16 => (831 / 1000000000000 : ℝ)
  | 17 => (1059 / 1000000000000 : ℝ)
  | 18 => (1331 / 1000000000000 : ℝ)
  | 19 => (413 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch000Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1 / 1000000000000 : ℝ)
  | 1 => (1 / 1000000000000 : ℝ)
  | 2 => (1 / 500000000000 : ℝ)
  | 3 => (1 / 250000000000 : ℝ)
  | 4 => (1 / 125000000000 : ℝ)
  | 5 => (17 / 1000000000000 : ℝ)
  | 6 => (31 / 1000000000000 : ℝ)
  | 7 => (53 / 1000000000000 : ℝ)
  | 8 => (21 / 250000000000 : ℝ)
  | 9 => (1 / 7812500000 : ℝ)
  | 10 => (93 / 500000000000 : ℝ)
  | 11 => (33 / 125000000000 : ℝ)
  | 12 => (363 / 1000000000000 : ℝ)
  | 13 => (61 / 125000000000 : ℝ)
  | 14 => (643 / 1000000000000 : ℝ)
  | 15 => (13 / 15625000000 : ℝ)
  | 16 => (53 / 50000000000 : ℝ)
  | 17 => (333 / 250000000000 : ℝ)
  | 18 => (1653 / 1000000000000 : ℝ)
  | 19 => (2029 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch000Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((0 : ℝ) + (j.val : ℝ)) / 1600)
      (((0 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch000Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch000Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((0 : ℝ) + (j.val : ℝ)) / 1600)
    (((0 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch000Neg65WeightLower j.val) (hpThetaShiftTwoBatch000Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch000Neg65WeightLower, hpThetaShiftTwoBatch000Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch000Neg65_integral_bounds :
    (7909 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (1029 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (0 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch000Lower hpThetaJensenCellsBatch000Upper
    hpThetaShiftTwoBatch000Neg65WeightLower hpThetaShiftTwoBatch000Neg65WeightUpper hpThetaJensenCellsBatch000_bounds hpThetaShiftTwoBatch000Neg65_weight_bounds
  have hl : (7909 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch000Lower j * hpThetaShiftTwoBatch000Neg65WeightLower j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftTwoBatch000Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftTwoBatch000Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch000Lower j * hpThetaShiftTwoBatch000Neg65WeightUpper j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftTwoBatch000Neg65WeightUpper j) / 1600) ≤ (1029 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftTwoBatch000Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (0 : ℝ) / 1600 = 0 / 80 by norm_num,
    show ((0 : ℝ) + 20) / 1600 = (0 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch000Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (0 / 1 : ℝ)
  | 1 => (0 / 1 : ℝ)
  | 2 => (0 / 1 : ℝ)
  | 3 => (1 / 1000000000000 : ℝ)
  | 4 => (3 / 1000000000000 : ℝ)
  | 5 => (7 / 1000000000000 : ℝ)
  | 6 => (1 / 62500000000 : ℝ)
  | 7 => (3 / 100000000000 : ℝ)
  | 8 => (13 / 250000000000 : ℝ)
  | 9 => (83 / 1000000000000 : ℝ)
  | 10 => (127 / 1000000000000 : ℝ)
  | 11 => (93 / 500000000000 : ℝ)
  | 12 => (263 / 1000000000000 : ℝ)
  | 13 => (181 / 500000000000 : ℝ)
  | 14 => (487 / 1000000000000 : ℝ)
  | 15 => (321 / 500000000000 : ℝ)
  | 16 => (13 / 15625000000 : ℝ)
  | 17 => (53 / 50000000000 : ℝ)
  | 18 => (333 / 250000000000 : ℝ)
  | 19 => (1653 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch000Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1 / 1000000000000 : ℝ)
  | 1 => (1 / 1000000000000 : ℝ)
  | 2 => (1 / 500000000000 : ℝ)
  | 3 => (1 / 250000000000 : ℝ)
  | 4 => (1 / 125000000000 : ℝ)
  | 5 => (17 / 1000000000000 : ℝ)
  | 6 => (31 / 1000000000000 : ℝ)
  | 7 => (53 / 1000000000000 : ℝ)
  | 8 => (21 / 250000000000 : ℝ)
  | 9 => (1 / 7812500000 : ℝ)
  | 10 => (187 / 1000000000000 : ℝ)
  | 11 => (33 / 125000000000 : ℝ)
  | 12 => (363 / 1000000000000 : ℝ)
  | 13 => (61 / 125000000000 : ℝ)
  | 14 => (643 / 1000000000000 : ℝ)
  | 15 => (833 / 1000000000000 : ℝ)
  | 16 => (1061 / 1000000000000 : ℝ)
  | 17 => (1333 / 1000000000000 : ℝ)
  | 18 => (827 / 500000000000 : ℝ)
  | 19 => (2031 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch000Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((0 : ℝ) + (j.val : ℝ)) / 1600)
      (((0 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch000Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch000Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((0 : ℝ) + (j.val : ℝ)) / 1600)
    (((0 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch000Neg45WeightLower j.val) (hpThetaShiftTwoBatch000Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch000Neg45WeightLower, hpThetaShiftTwoBatch000Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch000Neg45_integral_bounds :
    (1583 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (5149 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (0 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch000Lower hpThetaJensenCellsBatch000Upper
    hpThetaShiftTwoBatch000Neg45WeightLower hpThetaShiftTwoBatch000Neg45WeightUpper hpThetaJensenCellsBatch000_bounds hpThetaShiftTwoBatch000Neg45_weight_bounds
  have hl : (1583 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch000Lower j * hpThetaShiftTwoBatch000Neg45WeightLower j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftTwoBatch000Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftTwoBatch000Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch000Lower j * hpThetaShiftTwoBatch000Neg45WeightUpper j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftTwoBatch000Neg45WeightUpper j) / 1600) ≤ (5149 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftTwoBatch000Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (0 : ℝ) / 1600 = 0 / 80 by norm_num,
    show ((0 : ℝ) + 20) / 1600 = (0 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch000Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (0 / 1 : ℝ)
  | 1 => (0 / 1 : ℝ)
  | 2 => (0 / 1 : ℝ)
  | 3 => (1 / 1000000000000 : ℝ)
  | 4 => (3 / 1000000000000 : ℝ)
  | 5 => (7 / 1000000000000 : ℝ)
  | 6 => (1 / 62500000000 : ℝ)
  | 7 => (3 / 100000000000 : ℝ)
  | 8 => (13 / 250000000000 : ℝ)
  | 9 => (83 / 1000000000000 : ℝ)
  | 10 => (127 / 1000000000000 : ℝ)
  | 11 => (93 / 500000000000 : ℝ)
  | 12 => (263 / 1000000000000 : ℝ)
  | 13 => (181 / 500000000000 : ℝ)
  | 14 => (61 / 125000000000 : ℝ)
  | 15 => (643 / 1000000000000 : ℝ)
  | 16 => (13 / 15625000000 : ℝ)
  | 17 => (1061 / 1000000000000 : ℝ)
  | 18 => (1333 / 1000000000000 : ℝ)
  | 19 => (331 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch000Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1 / 1000000000000 : ℝ)
  | 1 => (1 / 1000000000000 : ℝ)
  | 2 => (1 / 500000000000 : ℝ)
  | 3 => (1 / 250000000000 : ℝ)
  | 4 => (1 / 125000000000 : ℝ)
  | 5 => (17 / 1000000000000 : ℝ)
  | 6 => (31 / 1000000000000 : ℝ)
  | 7 => (53 / 1000000000000 : ℝ)
  | 8 => (21 / 250000000000 : ℝ)
  | 9 => (1 / 7812500000 : ℝ)
  | 10 => (187 / 1000000000000 : ℝ)
  | 11 => (33 / 125000000000 : ℝ)
  | 12 => (363 / 1000000000000 : ℝ)
  | 13 => (489 / 1000000000000 : ℝ)
  | 14 => (161 / 250000000000 : ℝ)
  | 15 => (833 / 1000000000000 : ℝ)
  | 16 => (531 / 500000000000 : ℝ)
  | 17 => (667 / 500000000000 : ℝ)
  | 18 => (207 / 125000000000 : ℝ)
  | 19 => (2033 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch000Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((0 : ℝ) + (j.val : ℝ)) / 1600)
      (((0 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch000Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch000Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((0 : ℝ) + (j.val : ℝ)) / 1600)
    (((0 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch000Neg25WeightLower j.val) (hpThetaShiftTwoBatch000Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch000Neg25WeightLower, hpThetaShiftTwoBatch000Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch000Neg25_integral_bounds :
    (7921 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (10307 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (0 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch000Lower hpThetaJensenCellsBatch000Upper
    hpThetaShiftTwoBatch000Neg25WeightLower hpThetaShiftTwoBatch000Neg25WeightUpper hpThetaJensenCellsBatch000_bounds hpThetaShiftTwoBatch000Neg25_weight_bounds
  have hl : (7921 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch000Lower j * hpThetaShiftTwoBatch000Neg25WeightLower j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftTwoBatch000Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftTwoBatch000Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch000Lower j * hpThetaShiftTwoBatch000Neg25WeightUpper j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftTwoBatch000Neg25WeightUpper j) / 1600) ≤ (10307 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftTwoBatch000Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (0 : ℝ) / 1600 = 0 / 80 by norm_num,
    show ((0 : ℝ) + 20) / 1600 = (0 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch000Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch000Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch000Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch000Neg25_integral_bounds
end HodgeProofHP
