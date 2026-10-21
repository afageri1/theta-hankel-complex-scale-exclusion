/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch001

/-! Exact signed weight and batch integral certificates, batch 1 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch001Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (0 / 1 : ℝ)
  | 1 => (0 / 1 : ℝ)
  | 2 => (0 / 1 : ℝ)
  | 3 => (0 / 1 : ℝ)
  | 4 => (0 / 1 : ℝ)
  | 5 => (0 / 1 : ℝ)
  | 6 => (0 / 1 : ℝ)
  | 7 => (0 / 1 : ℝ)
  | 8 => (0 / 1 : ℝ)
  | 9 => (0 / 1 : ℝ)
  | 10 => (0 / 1 : ℝ)
  | 11 => (0 / 1 : ℝ)
  | 12 => (0 / 1 : ℝ)
  | 13 => (0 / 1 : ℝ)
  | 14 => (0 / 1 : ℝ)
  | 15 => (0 / 1 : ℝ)
  | 16 => (1 / 1000000000000 : ℝ)
  | 17 => (1 / 1000000000000 : ℝ)
  | 18 => (1 / 1000000000000 : ℝ)
  | 19 => (1 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch001Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1 / 1000000000000 : ℝ)
  | 1 => (1 / 1000000000000 : ℝ)
  | 2 => (1 / 1000000000000 : ℝ)
  | 3 => (1 / 1000000000000 : ℝ)
  | 4 => (1 / 1000000000000 : ℝ)
  | 5 => (1 / 1000000000000 : ℝ)
  | 6 => (1 / 1000000000000 : ℝ)
  | 7 => (1 / 1000000000000 : ℝ)
  | 8 => (1 / 1000000000000 : ℝ)
  | 9 => (1 / 1000000000000 : ℝ)
  | 10 => (1 / 1000000000000 : ℝ)
  | 11 => (1 / 1000000000000 : ℝ)
  | 12 => (1 / 1000000000000 : ℝ)
  | 13 => (1 / 1000000000000 : ℝ)
  | 14 => (1 / 1000000000000 : ℝ)
  | 15 => (1 / 500000000000 : ℝ)
  | 16 => (1 / 500000000000 : ℝ)
  | 17 => (1 / 500000000000 : ℝ)
  | 18 => (1 / 500000000000 : ℝ)
  | 19 => (3 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch001Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((20 : ℝ) + (j.val : ℝ)) / 1600)
      (((20 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch001Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch001Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((20 : ℝ) + (j.val : ℝ)) / 1600)
    (((20 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch001Neg100WeightLower j.val) (hpThetaShiftThreeBatch001Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch001Neg100WeightLower, hpThetaShiftThreeBatch001Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch001Neg100_integral_bounds :
    (1 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (3 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (20 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch001Lower hpThetaJensenCellsBatch001Upper
    hpThetaShiftThreeBatch001Neg100WeightLower hpThetaShiftThreeBatch001Neg100WeightUpper hpThetaJensenCellsBatch001_bounds hpThetaShiftThreeBatch001Neg100_weight_bounds
  have hl : (1 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch001Lower j * hpThetaShiftThreeBatch001Neg100WeightLower j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftThreeBatch001Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftThreeBatch001Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch001Lower j * hpThetaShiftThreeBatch001Neg100WeightUpper j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftThreeBatch001Neg100WeightUpper j) / 1600) ≤ (3 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftThreeBatch001Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (20 : ℝ) / 1600 = 1 / 80 by norm_num,
    show ((20 : ℝ) + 20) / 1600 = (1 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch001Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (0 / 1 : ℝ)
  | 1 => (0 / 1 : ℝ)
  | 2 => (0 / 1 : ℝ)
  | 3 => (0 / 1 : ℝ)
  | 4 => (0 / 1 : ℝ)
  | 5 => (0 / 1 : ℝ)
  | 6 => (0 / 1 : ℝ)
  | 7 => (0 / 1 : ℝ)
  | 8 => (0 / 1 : ℝ)
  | 9 => (0 / 1 : ℝ)
  | 10 => (0 / 1 : ℝ)
  | 11 => (0 / 1 : ℝ)
  | 12 => (0 / 1 : ℝ)
  | 13 => (0 / 1 : ℝ)
  | 14 => (0 / 1 : ℝ)
  | 15 => (0 / 1 : ℝ)
  | 16 => (1 / 1000000000000 : ℝ)
  | 17 => (1 / 1000000000000 : ℝ)
  | 18 => (1 / 1000000000000 : ℝ)
  | 19 => (1 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch001Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1 / 1000000000000 : ℝ)
  | 1 => (1 / 1000000000000 : ℝ)
  | 2 => (1 / 1000000000000 : ℝ)
  | 3 => (1 / 1000000000000 : ℝ)
  | 4 => (1 / 1000000000000 : ℝ)
  | 5 => (1 / 1000000000000 : ℝ)
  | 6 => (1 / 1000000000000 : ℝ)
  | 7 => (1 / 1000000000000 : ℝ)
  | 8 => (1 / 1000000000000 : ℝ)
  | 9 => (1 / 1000000000000 : ℝ)
  | 10 => (1 / 1000000000000 : ℝ)
  | 11 => (1 / 1000000000000 : ℝ)
  | 12 => (1 / 1000000000000 : ℝ)
  | 13 => (1 / 1000000000000 : ℝ)
  | 14 => (1 / 1000000000000 : ℝ)
  | 15 => (1 / 500000000000 : ℝ)
  | 16 => (1 / 500000000000 : ℝ)
  | 17 => (1 / 500000000000 : ℝ)
  | 18 => (1 / 500000000000 : ℝ)
  | 19 => (3 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch001Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((20 : ℝ) + (j.val : ℝ)) / 1600)
      (((20 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch001Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch001Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((20 : ℝ) + (j.val : ℝ)) / 1600)
    (((20 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch001Neg70WeightLower j.val) (hpThetaShiftThreeBatch001Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch001Neg70WeightLower, hpThetaShiftThreeBatch001Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch001Neg70_integral_bounds :
    (1 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (3 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (20 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch001Lower hpThetaJensenCellsBatch001Upper
    hpThetaShiftThreeBatch001Neg70WeightLower hpThetaShiftThreeBatch001Neg70WeightUpper hpThetaJensenCellsBatch001_bounds hpThetaShiftThreeBatch001Neg70_weight_bounds
  have hl : (1 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch001Lower j * hpThetaShiftThreeBatch001Neg70WeightLower j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftThreeBatch001Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftThreeBatch001Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch001Lower j * hpThetaShiftThreeBatch001Neg70WeightUpper j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftThreeBatch001Neg70WeightUpper j) / 1600) ≤ (3 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftThreeBatch001Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (20 : ℝ) / 1600 = 1 / 80 by norm_num,
    show ((20 : ℝ) + 20) / 1600 = (1 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch001Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (0 / 1 : ℝ)
  | 1 => (0 / 1 : ℝ)
  | 2 => (0 / 1 : ℝ)
  | 3 => (0 / 1 : ℝ)
  | 4 => (0 / 1 : ℝ)
  | 5 => (0 / 1 : ℝ)
  | 6 => (0 / 1 : ℝ)
  | 7 => (0 / 1 : ℝ)
  | 8 => (0 / 1 : ℝ)
  | 9 => (0 / 1 : ℝ)
  | 10 => (0 / 1 : ℝ)
  | 11 => (0 / 1 : ℝ)
  | 12 => (0 / 1 : ℝ)
  | 13 => (0 / 1 : ℝ)
  | 14 => (0 / 1 : ℝ)
  | 15 => (0 / 1 : ℝ)
  | 16 => (1 / 1000000000000 : ℝ)
  | 17 => (1 / 1000000000000 : ℝ)
  | 18 => (1 / 1000000000000 : ℝ)
  | 19 => (1 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch001Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1 / 1000000000000 : ℝ)
  | 1 => (1 / 1000000000000 : ℝ)
  | 2 => (1 / 1000000000000 : ℝ)
  | 3 => (1 / 1000000000000 : ℝ)
  | 4 => (1 / 1000000000000 : ℝ)
  | 5 => (1 / 1000000000000 : ℝ)
  | 6 => (1 / 1000000000000 : ℝ)
  | 7 => (1 / 1000000000000 : ℝ)
  | 8 => (1 / 1000000000000 : ℝ)
  | 9 => (1 / 1000000000000 : ℝ)
  | 10 => (1 / 1000000000000 : ℝ)
  | 11 => (1 / 1000000000000 : ℝ)
  | 12 => (1 / 1000000000000 : ℝ)
  | 13 => (1 / 1000000000000 : ℝ)
  | 14 => (1 / 1000000000000 : ℝ)
  | 15 => (1 / 500000000000 : ℝ)
  | 16 => (1 / 500000000000 : ℝ)
  | 17 => (1 / 500000000000 : ℝ)
  | 18 => (1 / 500000000000 : ℝ)
  | 19 => (3 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch001Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((20 : ℝ) + (j.val : ℝ)) / 1600)
      (((20 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch001Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch001Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((20 : ℝ) + (j.val : ℝ)) / 1600)
    (((20 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch001Neg45WeightLower j.val) (hpThetaShiftThreeBatch001Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch001Neg45WeightLower, hpThetaShiftThreeBatch001Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch001Neg45_integral_bounds :
    (1 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (3 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (20 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch001Lower hpThetaJensenCellsBatch001Upper
    hpThetaShiftThreeBatch001Neg45WeightLower hpThetaShiftThreeBatch001Neg45WeightUpper hpThetaJensenCellsBatch001_bounds hpThetaShiftThreeBatch001Neg45_weight_bounds
  have hl : (1 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch001Lower j * hpThetaShiftThreeBatch001Neg45WeightLower j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftThreeBatch001Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftThreeBatch001Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch001Lower j * hpThetaShiftThreeBatch001Neg45WeightUpper j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftThreeBatch001Neg45WeightUpper j) / 1600) ≤ (3 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftThreeBatch001Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (20 : ℝ) / 1600 = 1 / 80 by norm_num,
    show ((20 : ℝ) + 20) / 1600 = (1 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch001Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (0 / 1 : ℝ)
  | 1 => (0 / 1 : ℝ)
  | 2 => (0 / 1 : ℝ)
  | 3 => (0 / 1 : ℝ)
  | 4 => (0 / 1 : ℝ)
  | 5 => (0 / 1 : ℝ)
  | 6 => (0 / 1 : ℝ)
  | 7 => (0 / 1 : ℝ)
  | 8 => (0 / 1 : ℝ)
  | 9 => (0 / 1 : ℝ)
  | 10 => (0 / 1 : ℝ)
  | 11 => (0 / 1 : ℝ)
  | 12 => (0 / 1 : ℝ)
  | 13 => (0 / 1 : ℝ)
  | 14 => (0 / 1 : ℝ)
  | 15 => (0 / 1 : ℝ)
  | 16 => (1 / 1000000000000 : ℝ)
  | 17 => (1 / 1000000000000 : ℝ)
  | 18 => (1 / 1000000000000 : ℝ)
  | 19 => (1 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch001Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1 / 1000000000000 : ℝ)
  | 1 => (1 / 1000000000000 : ℝ)
  | 2 => (1 / 1000000000000 : ℝ)
  | 3 => (1 / 1000000000000 : ℝ)
  | 4 => (1 / 1000000000000 : ℝ)
  | 5 => (1 / 1000000000000 : ℝ)
  | 6 => (1 / 1000000000000 : ℝ)
  | 7 => (1 / 1000000000000 : ℝ)
  | 8 => (1 / 1000000000000 : ℝ)
  | 9 => (1 / 1000000000000 : ℝ)
  | 10 => (1 / 1000000000000 : ℝ)
  | 11 => (1 / 1000000000000 : ℝ)
  | 12 => (1 / 1000000000000 : ℝ)
  | 13 => (1 / 1000000000000 : ℝ)
  | 14 => (1 / 1000000000000 : ℝ)
  | 15 => (1 / 500000000000 : ℝ)
  | 16 => (1 / 500000000000 : ℝ)
  | 17 => (1 / 500000000000 : ℝ)
  | 18 => (1 / 500000000000 : ℝ)
  | 19 => (3 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch001Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((20 : ℝ) + (j.val : ℝ)) / 1600)
      (((20 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch001Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch001Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((20 : ℝ) + (j.val : ℝ)) / 1600)
    (((20 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch001Neg25WeightLower j.val) (hpThetaShiftThreeBatch001Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch001Neg25WeightLower, hpThetaShiftThreeBatch001Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch001Neg25_integral_bounds :
    (1 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (3 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (20 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch001Lower hpThetaJensenCellsBatch001Upper
    hpThetaShiftThreeBatch001Neg25WeightLower hpThetaShiftThreeBatch001Neg25WeightUpper hpThetaJensenCellsBatch001_bounds hpThetaShiftThreeBatch001Neg25_weight_bounds
  have hl : (1 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch001Lower j * hpThetaShiftThreeBatch001Neg25WeightLower j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftThreeBatch001Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftThreeBatch001Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch001Lower j * hpThetaShiftThreeBatch001Neg25WeightUpper j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftThreeBatch001Neg25WeightUpper j) / 1600) ≤ (3 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftThreeBatch001Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (20 : ℝ) / 1600 = 1 / 80 by norm_num,
    show ((20 : ℝ) + 20) / 1600 = (1 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch001Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch001Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch001Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch001Neg25_integral_bounds
end HodgeProofHP
