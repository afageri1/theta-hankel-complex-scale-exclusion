/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch003

/-! Exact signed weight and batch integral certificates, batch 3 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch003Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (11 / 500000000000 : ℝ)
  | 1 => (3 / 125000000000 : ℝ)
  | 2 => (27 / 1000000000000 : ℝ)
  | 3 => (3 / 100000000000 : ℝ)
  | 4 => (1 / 31250000000 : ℝ)
  | 5 => (9 / 250000000000 : ℝ)
  | 6 => (39 / 1000000000000 : ℝ)
  | 7 => (43 / 1000000000000 : ℝ)
  | 8 => (47 / 1000000000000 : ℝ)
  | 9 => (51 / 1000000000000 : ℝ)
  | 10 => (7 / 125000000000 : ℝ)
  | 11 => (3 / 50000000000 : ℝ)
  | 12 => (33 / 500000000000 : ℝ)
  | 13 => (71 / 1000000000000 : ℝ)
  | 14 => (77 / 1000000000000 : ℝ)
  | 15 => (21 / 250000000000 : ℝ)
  | 16 => (91 / 1000000000000 : ℝ)
  | 17 => (49 / 500000000000 : ℝ)
  | 18 => (53 / 500000000000 : ℝ)
  | 19 => (57 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch003Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1 / 40000000000 : ℝ)
  | 1 => (7 / 250000000000 : ℝ)
  | 2 => (31 / 1000000000000 : ℝ)
  | 3 => (33 / 1000000000000 : ℝ)
  | 4 => (37 / 1000000000000 : ℝ)
  | 5 => (1 / 25000000000 : ℝ)
  | 6 => (11 / 250000000000 : ℝ)
  | 7 => (3 / 62500000000 : ℝ)
  | 8 => (13 / 250000000000 : ℝ)
  | 9 => (57 / 1000000000000 : ℝ)
  | 10 => (61 / 1000000000000 : ℝ)
  | 11 => (67 / 1000000000000 : ℝ)
  | 12 => (9 / 125000000000 : ℝ)
  | 13 => (39 / 500000000000 : ℝ)
  | 14 => (17 / 200000000000 : ℝ)
  | 15 => (23 / 250000000000 : ℝ)
  | 16 => (99 / 1000000000000 : ℝ)
  | 17 => (107 / 1000000000000 : ℝ)
  | 18 => (23 / 200000000000 : ℝ)
  | 19 => (31 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch003Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((60 : ℝ) + (j.val : ℝ)) / 1600)
      (((60 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch003Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch003Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((60 : ℝ) + (j.val : ℝ)) / 1600)
    (((60 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch003Neg100WeightLower j.val) (hpThetaShiftThreeBatch003Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch003Neg100WeightLower, hpThetaShiftThreeBatch003Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch003Neg100_integral_bounds :
    (1279 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (1427 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (60 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch003Lower hpThetaJensenCellsBatch003Upper
    hpThetaShiftThreeBatch003Neg100WeightLower hpThetaShiftThreeBatch003Neg100WeightUpper hpThetaJensenCellsBatch003_bounds hpThetaShiftThreeBatch003Neg100_weight_bounds
  have hl : (1279 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch003Lower j * hpThetaShiftThreeBatch003Neg100WeightLower j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftThreeBatch003Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftThreeBatch003Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch003Lower j * hpThetaShiftThreeBatch003Neg100WeightUpper j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftThreeBatch003Neg100WeightUpper j) / 1600) ≤ (1427 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftThreeBatch003Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (60 : ℝ) / 1600 = 3 / 80 by norm_num,
    show ((60 : ℝ) + 20) / 1600 = (3 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch003Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (11 / 500000000000 : ℝ)
  | 1 => (1 / 40000000000 : ℝ)
  | 2 => (27 / 1000000000000 : ℝ)
  | 3 => (3 / 100000000000 : ℝ)
  | 4 => (33 / 1000000000000 : ℝ)
  | 5 => (9 / 250000000000 : ℝ)
  | 6 => (1 / 25000000000 : ℝ)
  | 7 => (43 / 1000000000000 : ℝ)
  | 8 => (47 / 1000000000000 : ℝ)
  | 9 => (13 / 250000000000 : ℝ)
  | 10 => (7 / 125000000000 : ℝ)
  | 11 => (61 / 1000000000000 : ℝ)
  | 12 => (67 / 1000000000000 : ℝ)
  | 13 => (9 / 125000000000 : ℝ)
  | 14 => (39 / 500000000000 : ℝ)
  | 15 => (17 / 200000000000 : ℝ)
  | 16 => (23 / 250000000000 : ℝ)
  | 17 => (99 / 1000000000000 : ℝ)
  | 18 => (107 / 1000000000000 : ℝ)
  | 19 => (29 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch003Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (13 / 500000000000 : ℝ)
  | 1 => (7 / 250000000000 : ℝ)
  | 2 => (31 / 1000000000000 : ℝ)
  | 3 => (17 / 500000000000 : ℝ)
  | 4 => (37 / 1000000000000 : ℝ)
  | 5 => (41 / 1000000000000 : ℝ)
  | 6 => (11 / 250000000000 : ℝ)
  | 7 => (3 / 62500000000 : ℝ)
  | 8 => (53 / 1000000000000 : ℝ)
  | 9 => (57 / 1000000000000 : ℝ)
  | 10 => (31 / 500000000000 : ℝ)
  | 11 => (17 / 250000000000 : ℝ)
  | 12 => (73 / 1000000000000 : ℝ)
  | 13 => (79 / 1000000000000 : ℝ)
  | 14 => (43 / 500000000000 : ℝ)
  | 15 => (93 / 1000000000000 : ℝ)
  | 16 => (1 / 10000000000 : ℝ)
  | 17 => (27 / 250000000000 : ℝ)
  | 18 => (117 / 1000000000000 : ℝ)
  | 19 => (63 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch003Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((60 : ℝ) + (j.val : ℝ)) / 1600)
      (((60 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch003Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch003Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((60 : ℝ) + (j.val : ℝ)) / 1600)
    (((60 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch003Neg70WeightLower j.val) (hpThetaShiftThreeBatch003Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch003Neg70WeightLower, hpThetaShiftThreeBatch003Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch003Neg70_integral_bounds :
    (647 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (289 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (60 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch003Lower hpThetaJensenCellsBatch003Upper
    hpThetaShiftThreeBatch003Neg70WeightLower hpThetaShiftThreeBatch003Neg70WeightUpper hpThetaJensenCellsBatch003_bounds hpThetaShiftThreeBatch003Neg70_weight_bounds
  have hl : (647 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch003Lower j * hpThetaShiftThreeBatch003Neg70WeightLower j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftThreeBatch003Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftThreeBatch003Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch003Lower j * hpThetaShiftThreeBatch003Neg70WeightUpper j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftThreeBatch003Neg70WeightUpper j) / 1600) ≤ (289 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftThreeBatch003Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (60 : ℝ) / 1600 = 3 / 80 by norm_num,
    show ((60 : ℝ) + 20) / 1600 = (3 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch003Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (11 / 500000000000 : ℝ)
  | 1 => (1 / 40000000000 : ℝ)
  | 2 => (27 / 1000000000000 : ℝ)
  | 3 => (3 / 100000000000 : ℝ)
  | 4 => (33 / 1000000000000 : ℝ)
  | 5 => (9 / 250000000000 : ℝ)
  | 6 => (1 / 25000000000 : ℝ)
  | 7 => (11 / 250000000000 : ℝ)
  | 8 => (3 / 62500000000 : ℝ)
  | 9 => (13 / 250000000000 : ℝ)
  | 10 => (57 / 1000000000000 : ℝ)
  | 11 => (31 / 500000000000 : ℝ)
  | 12 => (67 / 1000000000000 : ℝ)
  | 13 => (73 / 1000000000000 : ℝ)
  | 14 => (79 / 1000000000000 : ℝ)
  | 15 => (43 / 500000000000 : ℝ)
  | 16 => (93 / 1000000000000 : ℝ)
  | 17 => (101 / 1000000000000 : ℝ)
  | 18 => (109 / 1000000000000 : ℝ)
  | 19 => (117 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch003Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (13 / 500000000000 : ℝ)
  | 1 => (7 / 250000000000 : ℝ)
  | 2 => (31 / 1000000000000 : ℝ)
  | 3 => (17 / 500000000000 : ℝ)
  | 4 => (37 / 1000000000000 : ℝ)
  | 5 => (41 / 1000000000000 : ℝ)
  | 6 => (9 / 200000000000 : ℝ)
  | 7 => (49 / 1000000000000 : ℝ)
  | 8 => (53 / 1000000000000 : ℝ)
  | 9 => (29 / 500000000000 : ℝ)
  | 10 => (63 / 1000000000000 : ℝ)
  | 11 => (17 / 250000000000 : ℝ)
  | 12 => (37 / 500000000000 : ℝ)
  | 13 => (1 / 12500000000 : ℝ)
  | 14 => (87 / 1000000000000 : ℝ)
  | 15 => (47 / 500000000000 : ℝ)
  | 16 => (51 / 500000000000 : ℝ)
  | 17 => (11 / 100000000000 : ℝ)
  | 18 => (59 / 500000000000 : ℝ)
  | 19 => (1 / 7812500000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch003Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((60 : ℝ) + (j.val : ℝ)) / 1600)
      (((60 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch003Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch003Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((60 : ℝ) + (j.val : ℝ)) / 1600)
    (((60 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch003Neg45WeightLower j.val) (hpThetaShiftThreeBatch003Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch003Neg45WeightLower, hpThetaShiftThreeBatch003Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch003Neg45_integral_bounds :
    (327 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (1461 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (60 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch003Lower hpThetaJensenCellsBatch003Upper
    hpThetaShiftThreeBatch003Neg45WeightLower hpThetaShiftThreeBatch003Neg45WeightUpper hpThetaJensenCellsBatch003_bounds hpThetaShiftThreeBatch003Neg45_weight_bounds
  have hl : (327 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch003Lower j * hpThetaShiftThreeBatch003Neg45WeightLower j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftThreeBatch003Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftThreeBatch003Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch003Lower j * hpThetaShiftThreeBatch003Neg45WeightUpper j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftThreeBatch003Neg45WeightUpper j) / 1600) ≤ (1461 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftThreeBatch003Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (60 : ℝ) / 1600 = 3 / 80 by norm_num,
    show ((60 : ℝ) + 20) / 1600 = (3 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch003Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (23 / 1000000000000 : ℝ)
  | 1 => (1 / 40000000000 : ℝ)
  | 2 => (27 / 1000000000000 : ℝ)
  | 3 => (3 / 100000000000 : ℝ)
  | 4 => (33 / 1000000000000 : ℝ)
  | 5 => (37 / 1000000000000 : ℝ)
  | 6 => (1 / 25000000000 : ℝ)
  | 7 => (11 / 250000000000 : ℝ)
  | 8 => (3 / 62500000000 : ℝ)
  | 9 => (53 / 1000000000000 : ℝ)
  | 10 => (57 / 1000000000000 : ℝ)
  | 11 => (31 / 500000000000 : ℝ)
  | 12 => (17 / 250000000000 : ℝ)
  | 13 => (37 / 500000000000 : ℝ)
  | 14 => (1 / 12500000000 : ℝ)
  | 15 => (87 / 1000000000000 : ℝ)
  | 16 => (47 / 500000000000 : ℝ)
  | 17 => (51 / 500000000000 : ℝ)
  | 18 => (11 / 100000000000 : ℝ)
  | 19 => (119 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch003Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (13 / 500000000000 : ℝ)
  | 1 => (7 / 250000000000 : ℝ)
  | 2 => (31 / 1000000000000 : ℝ)
  | 3 => (17 / 500000000000 : ℝ)
  | 4 => (19 / 500000000000 : ℝ)
  | 5 => (41 / 1000000000000 : ℝ)
  | 6 => (9 / 200000000000 : ℝ)
  | 7 => (49 / 1000000000000 : ℝ)
  | 8 => (27 / 500000000000 : ℝ)
  | 9 => (29 / 500000000000 : ℝ)
  | 10 => (63 / 1000000000000 : ℝ)
  | 11 => (69 / 1000000000000 : ℝ)
  | 12 => (3 / 40000000000 : ℝ)
  | 13 => (81 / 1000000000000 : ℝ)
  | 14 => (11 / 125000000000 : ℝ)
  | 15 => (19 / 200000000000 : ℝ)
  | 16 => (103 / 1000000000000 : ℝ)
  | 17 => (111 / 1000000000000 : ℝ)
  | 18 => (3 / 25000000000 : ℝ)
  | 19 => (129 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch003Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((60 : ℝ) + (j.val : ℝ)) / 1600)
      (((60 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch003Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch003Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((60 : ℝ) + (j.val : ℝ)) / 1600)
    (((60 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch003Neg25WeightLower j.val) (hpThetaShiftThreeBatch003Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch003Neg25WeightLower, hpThetaShiftThreeBatch003Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch003Neg25_integral_bounds :
    (661 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (59 / 40000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (60 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch003Lower hpThetaJensenCellsBatch003Upper
    hpThetaShiftThreeBatch003Neg25WeightLower hpThetaShiftThreeBatch003Neg25WeightUpper hpThetaJensenCellsBatch003_bounds hpThetaShiftThreeBatch003Neg25_weight_bounds
  have hl : (661 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch003Lower j * hpThetaShiftThreeBatch003Neg25WeightLower j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftThreeBatch003Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftThreeBatch003Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch003Lower j * hpThetaShiftThreeBatch003Neg25WeightUpper j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftThreeBatch003Neg25WeightUpper j) / 1600) ≤ (59 / 40000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftThreeBatch003Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (60 : ℝ) / 1600 = 3 / 80 by norm_num,
    show ((60 : ℝ) + 20) / 1600 = (3 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch003Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch003Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch003Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch003Neg25_integral_bounds
end HodgeProofHP
