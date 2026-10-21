/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch002

/-! Exact signed weight and batch integral certificates, batch 2 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch002Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1 / 500000000000 : ℝ)
  | 1 => (1 / 500000000000 : ℝ)
  | 2 => (1 / 500000000000 : ℝ)
  | 3 => (3 / 1000000000000 : ℝ)
  | 4 => (3 / 1000000000000 : ℝ)
  | 5 => (1 / 250000000000 : ℝ)
  | 6 => (1 / 250000000000 : ℝ)
  | 7 => (1 / 200000000000 : ℝ)
  | 8 => (1 / 200000000000 : ℝ)
  | 9 => (3 / 500000000000 : ℝ)
  | 10 => (7 / 1000000000000 : ℝ)
  | 11 => (1 / 125000000000 : ℝ)
  | 12 => (9 / 1000000000000 : ℝ)
  | 13 => (1 / 100000000000 : ℝ)
  | 14 => (3 / 250000000000 : ℝ)
  | 15 => (13 / 1000000000000 : ℝ)
  | 16 => (7 / 500000000000 : ℝ)
  | 17 => (1 / 62500000000 : ℝ)
  | 18 => (9 / 500000000000 : ℝ)
  | 19 => (1 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch002Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3 / 1000000000000 : ℝ)
  | 1 => (3 / 1000000000000 : ℝ)
  | 2 => (1 / 250000000000 : ℝ)
  | 3 => (1 / 250000000000 : ℝ)
  | 4 => (1 / 200000000000 : ℝ)
  | 5 => (1 / 200000000000 : ℝ)
  | 6 => (3 / 500000000000 : ℝ)
  | 7 => (3 / 500000000000 : ℝ)
  | 8 => (7 / 1000000000000 : ℝ)
  | 9 => (1 / 125000000000 : ℝ)
  | 10 => (9 / 1000000000000 : ℝ)
  | 11 => (1 / 100000000000 : ℝ)
  | 12 => (11 / 1000000000000 : ℝ)
  | 13 => (13 / 1000000000000 : ℝ)
  | 14 => (7 / 500000000000 : ℝ)
  | 15 => (3 / 200000000000 : ℝ)
  | 16 => (17 / 1000000000000 : ℝ)
  | 17 => (19 / 1000000000000 : ℝ)
  | 18 => (21 / 1000000000000 : ℝ)
  | 19 => (23 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch002Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((40 : ℝ) + (j.val : ℝ)) / 1600)
      (((40 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch002Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch002Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((40 : ℝ) + (j.val : ℝ)) / 1600)
    (((40 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch002Neg100WeightLower j.val) (hpThetaShiftThreeBatch002Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch002Neg100WeightLower, hpThetaShiftThreeBatch002Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch002Neg100_integral_bounds :
    (179 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (113 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (40 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch002Lower hpThetaJensenCellsBatch002Upper
    hpThetaShiftThreeBatch002Neg100WeightLower hpThetaShiftThreeBatch002Neg100WeightUpper hpThetaJensenCellsBatch002_bounds hpThetaShiftThreeBatch002Neg100_weight_bounds
  have hl : (179 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch002Lower j * hpThetaShiftThreeBatch002Neg100WeightLower j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftThreeBatch002Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftThreeBatch002Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch002Lower j * hpThetaShiftThreeBatch002Neg100WeightUpper j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftThreeBatch002Neg100WeightUpper j) / 1600) ≤ (113 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftThreeBatch002Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (40 : ℝ) / 1600 = 2 / 80 by norm_num,
    show ((40 : ℝ) + 20) / 1600 = (2 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch002Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1 / 500000000000 : ℝ)
  | 1 => (1 / 500000000000 : ℝ)
  | 2 => (1 / 500000000000 : ℝ)
  | 3 => (3 / 1000000000000 : ℝ)
  | 4 => (3 / 1000000000000 : ℝ)
  | 5 => (1 / 250000000000 : ℝ)
  | 6 => (1 / 250000000000 : ℝ)
  | 7 => (1 / 200000000000 : ℝ)
  | 8 => (1 / 200000000000 : ℝ)
  | 9 => (3 / 500000000000 : ℝ)
  | 10 => (7 / 1000000000000 : ℝ)
  | 11 => (1 / 125000000000 : ℝ)
  | 12 => (9 / 1000000000000 : ℝ)
  | 13 => (1 / 100000000000 : ℝ)
  | 14 => (3 / 250000000000 : ℝ)
  | 15 => (13 / 1000000000000 : ℝ)
  | 16 => (3 / 200000000000 : ℝ)
  | 17 => (1 / 62500000000 : ℝ)
  | 18 => (9 / 500000000000 : ℝ)
  | 19 => (1 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch002Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3 / 1000000000000 : ℝ)
  | 1 => (3 / 1000000000000 : ℝ)
  | 2 => (1 / 250000000000 : ℝ)
  | 3 => (1 / 250000000000 : ℝ)
  | 4 => (1 / 200000000000 : ℝ)
  | 5 => (1 / 200000000000 : ℝ)
  | 6 => (3 / 500000000000 : ℝ)
  | 7 => (3 / 500000000000 : ℝ)
  | 8 => (7 / 1000000000000 : ℝ)
  | 9 => (1 / 125000000000 : ℝ)
  | 10 => (9 / 1000000000000 : ℝ)
  | 11 => (1 / 100000000000 : ℝ)
  | 12 => (11 / 1000000000000 : ℝ)
  | 13 => (13 / 1000000000000 : ℝ)
  | 14 => (7 / 500000000000 : ℝ)
  | 15 => (1 / 62500000000 : ℝ)
  | 16 => (17 / 1000000000000 : ℝ)
  | 17 => (19 / 1000000000000 : ℝ)
  | 18 => (21 / 1000000000000 : ℝ)
  | 19 => (23 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch002Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((40 : ℝ) + (j.val : ℝ)) / 1600)
      (((40 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch002Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch002Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((40 : ℝ) + (j.val : ℝ)) / 1600)
    (((40 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch002Neg70WeightLower j.val) (hpThetaShiftThreeBatch002Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch002Neg70WeightLower, hpThetaShiftThreeBatch002Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch002Neg70_integral_bounds :
    (9 / 50000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (227 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (40 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch002Lower hpThetaJensenCellsBatch002Upper
    hpThetaShiftThreeBatch002Neg70WeightLower hpThetaShiftThreeBatch002Neg70WeightUpper hpThetaJensenCellsBatch002_bounds hpThetaShiftThreeBatch002Neg70_weight_bounds
  have hl : (9 / 50000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch002Lower j * hpThetaShiftThreeBatch002Neg70WeightLower j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftThreeBatch002Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftThreeBatch002Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch002Lower j * hpThetaShiftThreeBatch002Neg70WeightUpper j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftThreeBatch002Neg70WeightUpper j) / 1600) ≤ (227 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftThreeBatch002Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (40 : ℝ) / 1600 = 2 / 80 by norm_num,
    show ((40 : ℝ) + 20) / 1600 = (2 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch002Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1 / 500000000000 : ℝ)
  | 1 => (1 / 500000000000 : ℝ)
  | 2 => (1 / 500000000000 : ℝ)
  | 3 => (3 / 1000000000000 : ℝ)
  | 4 => (3 / 1000000000000 : ℝ)
  | 5 => (1 / 250000000000 : ℝ)
  | 6 => (1 / 250000000000 : ℝ)
  | 7 => (1 / 200000000000 : ℝ)
  | 8 => (3 / 500000000000 : ℝ)
  | 9 => (3 / 500000000000 : ℝ)
  | 10 => (7 / 1000000000000 : ℝ)
  | 11 => (1 / 125000000000 : ℝ)
  | 12 => (9 / 1000000000000 : ℝ)
  | 13 => (1 / 100000000000 : ℝ)
  | 14 => (3 / 250000000000 : ℝ)
  | 15 => (13 / 1000000000000 : ℝ)
  | 16 => (3 / 200000000000 : ℝ)
  | 17 => (1 / 62500000000 : ℝ)
  | 18 => (9 / 500000000000 : ℝ)
  | 19 => (1 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch002Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3 / 1000000000000 : ℝ)
  | 1 => (3 / 1000000000000 : ℝ)
  | 2 => (1 / 250000000000 : ℝ)
  | 3 => (1 / 250000000000 : ℝ)
  | 4 => (1 / 200000000000 : ℝ)
  | 5 => (1 / 200000000000 : ℝ)
  | 6 => (3 / 500000000000 : ℝ)
  | 7 => (7 / 1000000000000 : ℝ)
  | 8 => (7 / 1000000000000 : ℝ)
  | 9 => (1 / 125000000000 : ℝ)
  | 10 => (9 / 1000000000000 : ℝ)
  | 11 => (1 / 100000000000 : ℝ)
  | 12 => (11 / 1000000000000 : ℝ)
  | 13 => (13 / 1000000000000 : ℝ)
  | 14 => (7 / 500000000000 : ℝ)
  | 15 => (1 / 62500000000 : ℝ)
  | 16 => (17 / 1000000000000 : ℝ)
  | 17 => (19 / 1000000000000 : ℝ)
  | 18 => (21 / 1000000000000 : ℝ)
  | 19 => (23 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch002Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((40 : ℝ) + (j.val : ℝ)) / 1600)
      (((40 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch002Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch002Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((40 : ℝ) + (j.val : ℝ)) / 1600)
    (((40 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch002Neg45WeightLower j.val) (hpThetaShiftThreeBatch002Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch002Neg45WeightLower, hpThetaShiftThreeBatch002Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch002Neg45_integral_bounds :
    (181 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (57 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (40 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch002Lower hpThetaJensenCellsBatch002Upper
    hpThetaShiftThreeBatch002Neg45WeightLower hpThetaShiftThreeBatch002Neg45WeightUpper hpThetaJensenCellsBatch002_bounds hpThetaShiftThreeBatch002Neg45_weight_bounds
  have hl : (181 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch002Lower j * hpThetaShiftThreeBatch002Neg45WeightLower j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftThreeBatch002Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftThreeBatch002Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch002Lower j * hpThetaShiftThreeBatch002Neg45WeightUpper j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftThreeBatch002Neg45WeightUpper j) / 1600) ≤ (57 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftThreeBatch002Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (40 : ℝ) / 1600 = 2 / 80 by norm_num,
    show ((40 : ℝ) + 20) / 1600 = (2 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch002Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1 / 500000000000 : ℝ)
  | 1 => (1 / 500000000000 : ℝ)
  | 2 => (1 / 500000000000 : ℝ)
  | 3 => (3 / 1000000000000 : ℝ)
  | 4 => (3 / 1000000000000 : ℝ)
  | 5 => (1 / 250000000000 : ℝ)
  | 6 => (1 / 250000000000 : ℝ)
  | 7 => (1 / 200000000000 : ℝ)
  | 8 => (3 / 500000000000 : ℝ)
  | 9 => (3 / 500000000000 : ℝ)
  | 10 => (7 / 1000000000000 : ℝ)
  | 11 => (1 / 125000000000 : ℝ)
  | 12 => (9 / 1000000000000 : ℝ)
  | 13 => (1 / 100000000000 : ℝ)
  | 14 => (3 / 250000000000 : ℝ)
  | 15 => (13 / 1000000000000 : ℝ)
  | 16 => (3 / 200000000000 : ℝ)
  | 17 => (1 / 62500000000 : ℝ)
  | 18 => (9 / 500000000000 : ℝ)
  | 19 => (1 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch002Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3 / 1000000000000 : ℝ)
  | 1 => (3 / 1000000000000 : ℝ)
  | 2 => (1 / 250000000000 : ℝ)
  | 3 => (1 / 250000000000 : ℝ)
  | 4 => (1 / 200000000000 : ℝ)
  | 5 => (1 / 200000000000 : ℝ)
  | 6 => (3 / 500000000000 : ℝ)
  | 7 => (7 / 1000000000000 : ℝ)
  | 8 => (7 / 1000000000000 : ℝ)
  | 9 => (1 / 125000000000 : ℝ)
  | 10 => (9 / 1000000000000 : ℝ)
  | 11 => (1 / 100000000000 : ℝ)
  | 12 => (11 / 1000000000000 : ℝ)
  | 13 => (13 / 1000000000000 : ℝ)
  | 14 => (7 / 500000000000 : ℝ)
  | 15 => (1 / 62500000000 : ℝ)
  | 16 => (17 / 1000000000000 : ℝ)
  | 17 => (19 / 1000000000000 : ℝ)
  | 18 => (21 / 1000000000000 : ℝ)
  | 19 => (3 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch002Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((40 : ℝ) + (j.val : ℝ)) / 1600)
      (((40 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch002Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch002Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((40 : ℝ) + (j.val : ℝ)) / 1600)
    (((40 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch002Neg25WeightLower j.val) (hpThetaShiftThreeBatch002Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch002Neg25WeightLower, hpThetaShiftThreeBatch002Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch002Neg25_integral_bounds :
    (181 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (229 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (40 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch002Lower hpThetaJensenCellsBatch002Upper
    hpThetaShiftThreeBatch002Neg25WeightLower hpThetaShiftThreeBatch002Neg25WeightUpper hpThetaJensenCellsBatch002_bounds hpThetaShiftThreeBatch002Neg25_weight_bounds
  have hl : (181 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch002Lower j * hpThetaShiftThreeBatch002Neg25WeightLower j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftThreeBatch002Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftThreeBatch002Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch002Lower j * hpThetaShiftThreeBatch002Neg25WeightUpper j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftThreeBatch002Neg25WeightUpper j) / 1600) ≤ (229 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftThreeBatch002Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (40 : ℝ) / 1600 = 2 / 80 by norm_num,
    show ((40 : ℝ) + 20) / 1600 = (2 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch002Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch002Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch002Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch002Neg25_integral_bounds
end HodgeProofHP
