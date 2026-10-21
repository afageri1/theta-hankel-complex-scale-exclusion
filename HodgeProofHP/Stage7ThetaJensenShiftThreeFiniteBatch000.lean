/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch000

/-! Exact signed weight and batch integral certificates, batch 0 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch000Neg100WeightLower (j : ℕ) : ℝ :=
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
  | 16 => (0 / 1 : ℝ)
  | 17 => (0 / 1 : ℝ)
  | 18 => (0 / 1 : ℝ)
  | 19 => (0 / 1 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch000Neg100WeightUpper (j : ℕ) : ℝ :=
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
  | 15 => (1 / 1000000000000 : ℝ)
  | 16 => (1 / 1000000000000 : ℝ)
  | 17 => (1 / 1000000000000 : ℝ)
  | 18 => (1 / 1000000000000 : ℝ)
  | 19 => (1 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch000Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((0 : ℝ) + (j.val : ℝ)) / 1600)
      (((0 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch000Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch000Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((0 : ℝ) + (j.val : ℝ)) / 1600)
    (((0 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch000Neg100WeightLower j.val) (hpThetaShiftThreeBatch000Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch000Neg100WeightLower, hpThetaShiftThreeBatch000Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch000Neg100_integral_bounds :
    (0 / 1 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (23 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (0 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch000Lower hpThetaJensenCellsBatch000Upper
    hpThetaShiftThreeBatch000Neg100WeightLower hpThetaShiftThreeBatch000Neg100WeightUpper hpThetaJensenCellsBatch000_bounds hpThetaShiftThreeBatch000Neg100_weight_bounds
  have hl : (0 / 1 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch000Lower j * hpThetaShiftThreeBatch000Neg100WeightLower j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftThreeBatch000Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftThreeBatch000Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch000Lower j * hpThetaShiftThreeBatch000Neg100WeightUpper j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftThreeBatch000Neg100WeightUpper j) / 1600) ≤ (23 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftThreeBatch000Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (0 : ℝ) / 1600 = 0 / 80 by norm_num,
    show ((0 : ℝ) + 20) / 1600 = (0 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch000Neg70WeightLower (j : ℕ) : ℝ :=
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
  | 16 => (0 / 1 : ℝ)
  | 17 => (0 / 1 : ℝ)
  | 18 => (0 / 1 : ℝ)
  | 19 => (0 / 1 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch000Neg70WeightUpper (j : ℕ) : ℝ :=
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
  | 15 => (1 / 1000000000000 : ℝ)
  | 16 => (1 / 1000000000000 : ℝ)
  | 17 => (1 / 1000000000000 : ℝ)
  | 18 => (1 / 1000000000000 : ℝ)
  | 19 => (1 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch000Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((0 : ℝ) + (j.val : ℝ)) / 1600)
      (((0 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch000Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch000Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((0 : ℝ) + (j.val : ℝ)) / 1600)
    (((0 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch000Neg70WeightLower j.val) (hpThetaShiftThreeBatch000Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch000Neg70WeightLower, hpThetaShiftThreeBatch000Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch000Neg70_integral_bounds :
    (0 / 1 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (23 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (0 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch000Lower hpThetaJensenCellsBatch000Upper
    hpThetaShiftThreeBatch000Neg70WeightLower hpThetaShiftThreeBatch000Neg70WeightUpper hpThetaJensenCellsBatch000_bounds hpThetaShiftThreeBatch000Neg70_weight_bounds
  have hl : (0 / 1 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch000Lower j * hpThetaShiftThreeBatch000Neg70WeightLower j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftThreeBatch000Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftThreeBatch000Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch000Lower j * hpThetaShiftThreeBatch000Neg70WeightUpper j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftThreeBatch000Neg70WeightUpper j) / 1600) ≤ (23 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftThreeBatch000Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (0 : ℝ) / 1600 = 0 / 80 by norm_num,
    show ((0 : ℝ) + 20) / 1600 = (0 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch000Neg45WeightLower (j : ℕ) : ℝ :=
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
  | 16 => (0 / 1 : ℝ)
  | 17 => (0 / 1 : ℝ)
  | 18 => (0 / 1 : ℝ)
  | 19 => (0 / 1 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch000Neg45WeightUpper (j : ℕ) : ℝ :=
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
  | 15 => (1 / 1000000000000 : ℝ)
  | 16 => (1 / 1000000000000 : ℝ)
  | 17 => (1 / 1000000000000 : ℝ)
  | 18 => (1 / 1000000000000 : ℝ)
  | 19 => (1 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch000Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((0 : ℝ) + (j.val : ℝ)) / 1600)
      (((0 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch000Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch000Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((0 : ℝ) + (j.val : ℝ)) / 1600)
    (((0 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch000Neg45WeightLower j.val) (hpThetaShiftThreeBatch000Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch000Neg45WeightLower, hpThetaShiftThreeBatch000Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch000Neg45_integral_bounds :
    (0 / 1 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (23 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (0 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch000Lower hpThetaJensenCellsBatch000Upper
    hpThetaShiftThreeBatch000Neg45WeightLower hpThetaShiftThreeBatch000Neg45WeightUpper hpThetaJensenCellsBatch000_bounds hpThetaShiftThreeBatch000Neg45_weight_bounds
  have hl : (0 / 1 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch000Lower j * hpThetaShiftThreeBatch000Neg45WeightLower j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftThreeBatch000Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftThreeBatch000Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch000Lower j * hpThetaShiftThreeBatch000Neg45WeightUpper j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftThreeBatch000Neg45WeightUpper j) / 1600) ≤ (23 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftThreeBatch000Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (0 : ℝ) / 1600 = 0 / 80 by norm_num,
    show ((0 : ℝ) + 20) / 1600 = (0 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch000Neg25WeightLower (j : ℕ) : ℝ :=
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
  | 16 => (0 / 1 : ℝ)
  | 17 => (0 / 1 : ℝ)
  | 18 => (0 / 1 : ℝ)
  | 19 => (0 / 1 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch000Neg25WeightUpper (j : ℕ) : ℝ :=
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
  | 15 => (1 / 1000000000000 : ℝ)
  | 16 => (1 / 1000000000000 : ℝ)
  | 17 => (1 / 1000000000000 : ℝ)
  | 18 => (1 / 1000000000000 : ℝ)
  | 19 => (1 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch000Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((0 : ℝ) + (j.val : ℝ)) / 1600)
      (((0 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch000Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch000Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((0 : ℝ) + (j.val : ℝ)) / 1600)
    (((0 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch000Neg25WeightLower j.val) (hpThetaShiftThreeBatch000Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch000Neg25WeightLower, hpThetaShiftThreeBatch000Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch000Neg25_integral_bounds :
    (0 / 1 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (23 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (0 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch000Lower hpThetaJensenCellsBatch000Upper
    hpThetaShiftThreeBatch000Neg25WeightLower hpThetaShiftThreeBatch000Neg25WeightUpper hpThetaJensenCellsBatch000_bounds hpThetaShiftThreeBatch000Neg25_weight_bounds
  have hl : (0 / 1 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch000Lower j * hpThetaShiftThreeBatch000Neg25WeightLower j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftThreeBatch000Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftThreeBatch000Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch000Lower j * hpThetaShiftThreeBatch000Neg25WeightUpper j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftThreeBatch000Neg25WeightUpper j) / 1600) ≤ (23 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftThreeBatch000Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (0 : ℝ) / 1600 = 0 / 80 by norm_num,
    show ((0 : ℝ) + 20) / 1600 = (0 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch000Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch000Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch000Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch000Neg25_integral_bounds
end HodgeProofHP
