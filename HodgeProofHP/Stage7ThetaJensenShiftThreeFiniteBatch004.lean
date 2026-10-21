/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch004

/-! Exact signed weight and batch integral certificates, batch 4 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch004Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (123 / 1000000000000 : ℝ)
  | 1 => (33 / 250000000000 : ℝ)
  | 2 => (71 / 500000000000 : ℝ)
  | 3 => (153 / 1000000000000 : ℝ)
  | 4 => (41 / 250000000000 : ℝ)
  | 5 => (11 / 62500000000 : ℝ)
  | 6 => (47 / 250000000000 : ℝ)
  | 7 => (201 / 1000000000000 : ℝ)
  | 8 => (43 / 200000000000 : ℝ)
  | 9 => (23 / 100000000000 : ℝ)
  | 10 => (123 / 500000000000 : ℝ)
  | 11 => (131 / 500000000000 : ℝ)
  | 12 => (7 / 25000000000 : ℝ)
  | 13 => (149 / 500000000000 : ℝ)
  | 14 => (317 / 1000000000000 : ℝ)
  | 15 => (169 / 500000000000 : ℝ)
  | 16 => (359 / 1000000000000 : ℝ)
  | 17 => (381 / 1000000000000 : ℝ)
  | 18 => (81 / 200000000000 : ℝ)
  | 19 => (43 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch004Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (133 / 1000000000000 : ℝ)
  | 1 => (143 / 1000000000000 : ℝ)
  | 2 => (77 / 500000000000 : ℝ)
  | 3 => (33 / 200000000000 : ℝ)
  | 4 => (177 / 1000000000000 : ℝ)
  | 5 => (189 / 1000000000000 : ℝ)
  | 6 => (101 / 500000000000 : ℝ)
  | 7 => (27 / 125000000000 : ℝ)
  | 8 => (231 / 1000000000000 : ℝ)
  | 9 => (247 / 1000000000000 : ℝ)
  | 10 => (263 / 1000000000000 : ℝ)
  | 11 => (281 / 1000000000000 : ℝ)
  | 12 => (299 / 1000000000000 : ℝ)
  | 13 => (159 / 500000000000 : ℝ)
  | 14 => (339 / 1000000000000 : ℝ)
  | 15 => (9 / 25000000000 : ℝ)
  | 16 => (191 / 500000000000 : ℝ)
  | 17 => (203 / 500000000000 : ℝ)
  | 18 => (431 / 1000000000000 : ℝ)
  | 19 => (457 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch004Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((80 : ℝ) + (j.val : ℝ)) / 1600)
      (((80 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch004Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch004Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((80 : ℝ) + (j.val : ℝ)) / 1600)
    (((80 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch004Neg100WeightLower j.val) (hpThetaShiftThreeBatch004Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch004Neg100WeightLower, hpThetaShiftThreeBatch004Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch004Neg100_integral_bounds :
    (5429 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (2937 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (80 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch004Lower hpThetaJensenCellsBatch004Upper
    hpThetaShiftThreeBatch004Neg100WeightLower hpThetaShiftThreeBatch004Neg100WeightUpper hpThetaJensenCellsBatch004_bounds hpThetaShiftThreeBatch004Neg100_weight_bounds
  have hl : (5429 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch004Lower j * hpThetaShiftThreeBatch004Neg100WeightLower j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftThreeBatch004Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftThreeBatch004Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch004Lower j * hpThetaShiftThreeBatch004Neg100WeightUpper j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftThreeBatch004Neg100WeightUpper j) / 1600) ≤ (2937 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftThreeBatch004Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (80 : ℝ) / 1600 = 4 / 80 by norm_num,
    show ((80 : ℝ) + 20) / 1600 = (4 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch004Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1 / 8000000000 : ℝ)
  | 1 => (67 / 500000000000 : ℝ)
  | 2 => (29 / 200000000000 : ℝ)
  | 3 => (31 / 200000000000 : ℝ)
  | 4 => (167 / 1000000000000 : ℝ)
  | 5 => (179 / 1000000000000 : ℝ)
  | 6 => (3 / 15625000000 : ℝ)
  | 7 => (41 / 200000000000 : ℝ)
  | 8 => (11 / 50000000000 : ℝ)
  | 9 => (47 / 200000000000 : ℝ)
  | 10 => (251 / 1000000000000 : ℝ)
  | 11 => (67 / 250000000000 : ℝ)
  | 12 => (143 / 500000000000 : ℝ)
  | 13 => (61 / 200000000000 : ℝ)
  | 14 => (13 / 40000000000 : ℝ)
  | 15 => (173 / 500000000000 : ℝ)
  | 16 => (23 / 62500000000 : ℝ)
  | 17 => (391 / 1000000000000 : ℝ)
  | 18 => (83 / 200000000000 : ℝ)
  | 19 => (441 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch004Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (27 / 200000000000 : ℝ)
  | 1 => (73 / 500000000000 : ℝ)
  | 2 => (39 / 250000000000 : ℝ)
  | 3 => (21 / 125000000000 : ℝ)
  | 4 => (9 / 50000000000 : ℝ)
  | 5 => (193 / 1000000000000 : ℝ)
  | 6 => (103 / 500000000000 : ℝ)
  | 7 => (221 / 1000000000000 : ℝ)
  | 8 => (59 / 250000000000 : ℝ)
  | 9 => (63 / 250000000000 : ℝ)
  | 10 => (269 / 1000000000000 : ℝ)
  | 11 => (287 / 1000000000000 : ℝ)
  | 12 => (153 / 500000000000 : ℝ)
  | 13 => (163 / 500000000000 : ℝ)
  | 14 => (347 / 1000000000000 : ℝ)
  | 15 => (369 / 1000000000000 : ℝ)
  | 16 => (49 / 125000000000 : ℝ)
  | 17 => (13 / 31250000000 : ℝ)
  | 18 => (221 / 500000000000 : ℝ)
  | 19 => (469 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch004Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((80 : ℝ) + (j.val : ℝ)) / 1600)
      (((80 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch004Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch004Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((80 : ℝ) + (j.val : ℝ)) / 1600)
    (((80 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch004Neg70WeightLower j.val) (hpThetaShiftThreeBatch004Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch004Neg70WeightLower, hpThetaShiftThreeBatch004Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch004Neg70_integral_bounds :
    (5551 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (751 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (80 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch004Lower hpThetaJensenCellsBatch004Upper
    hpThetaShiftThreeBatch004Neg70WeightLower hpThetaShiftThreeBatch004Neg70WeightUpper hpThetaJensenCellsBatch004_bounds hpThetaShiftThreeBatch004Neg70_weight_bounds
  have hl : (5551 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch004Lower j * hpThetaShiftThreeBatch004Neg70WeightLower j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftThreeBatch004Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftThreeBatch004Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch004Lower j * hpThetaShiftThreeBatch004Neg70WeightUpper j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftThreeBatch004Neg70WeightUpper j) / 1600) ≤ (751 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftThreeBatch004Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (80 : ℝ) / 1600 = 4 / 80 by norm_num,
    show ((80 : ℝ) + 20) / 1600 = (4 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch004Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (127 / 1000000000000 : ℝ)
  | 1 => (17 / 125000000000 : ℝ)
  | 2 => (147 / 1000000000000 : ℝ)
  | 3 => (79 / 500000000000 : ℝ)
  | 4 => (169 / 1000000000000 : ℝ)
  | 5 => (91 / 500000000000 : ℝ)
  | 6 => (39 / 200000000000 : ℝ)
  | 7 => (209 / 1000000000000 : ℝ)
  | 8 => (223 / 1000000000000 : ℝ)
  | 9 => (239 / 1000000000000 : ℝ)
  | 10 => (51 / 200000000000 : ℝ)
  | 11 => (273 / 1000000000000 : ℝ)
  | 12 => (291 / 1000000000000 : ℝ)
  | 13 => (31 / 100000000000 : ℝ)
  | 14 => (331 / 1000000000000 : ℝ)
  | 15 => (11 / 31250000000 : ℝ)
  | 16 => (3 / 8000000000 : ℝ)
  | 17 => (399 / 1000000000000 : ℝ)
  | 18 => (53 / 125000000000 : ℝ)
  | 19 => (9 / 20000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch004Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (137 / 1000000000000 : ℝ)
  | 1 => (37 / 250000000000 : ℝ)
  | 2 => (159 / 1000000000000 : ℝ)
  | 3 => (17 / 100000000000 : ℝ)
  | 4 => (183 / 1000000000000 : ℝ)
  | 5 => (49 / 250000000000 : ℝ)
  | 6 => (21 / 100000000000 : ℝ)
  | 7 => (7 / 31250000000 : ℝ)
  | 8 => (3 / 12500000000 : ℝ)
  | 9 => (1 / 3906250000 : ℝ)
  | 10 => (137 / 500000000000 : ℝ)
  | 11 => (73 / 250000000000 : ℝ)
  | 12 => (311 / 1000000000000 : ℝ)
  | 13 => (83 / 250000000000 : ℝ)
  | 14 => (353 / 1000000000000 : ℝ)
  | 15 => (47 / 125000000000 : ℝ)
  | 16 => (1 / 2500000000 : ℝ)
  | 17 => (17 / 40000000000 : ℝ)
  | 18 => (451 / 1000000000000 : ℝ)
  | 19 => (479 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch004Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((80 : ℝ) + (j.val : ℝ)) / 1600)
      (((80 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch004Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch004Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((80 : ℝ) + (j.val : ℝ)) / 1600)
    (((80 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch004Neg45WeightLower j.val) (hpThetaShiftThreeBatch004Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch004Neg45WeightLower, hpThetaShiftThreeBatch004Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch004Neg45_integral_bounds :
    (113 / 20000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (1529 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (80 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch004Lower hpThetaJensenCellsBatch004Upper
    hpThetaShiftThreeBatch004Neg45WeightLower hpThetaShiftThreeBatch004Neg45WeightUpper hpThetaJensenCellsBatch004_bounds hpThetaShiftThreeBatch004Neg45_weight_bounds
  have hl : (113 / 20000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch004Lower j * hpThetaShiftThreeBatch004Neg45WeightLower j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftThreeBatch004Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftThreeBatch004Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch004Lower j * hpThetaShiftThreeBatch004Neg45WeightUpper j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftThreeBatch004Neg45WeightUpper j) / 1600) ≤ (1529 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftThreeBatch004Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (80 : ℝ) / 1600 = 4 / 80 by norm_num,
    show ((80 : ℝ) + 20) / 1600 = (4 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch004Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1 / 7812500000 : ℝ)
  | 1 => (69 / 500000000000 : ℝ)
  | 2 => (37 / 250000000000 : ℝ)
  | 3 => (1 / 6250000000 : ℝ)
  | 4 => (171 / 1000000000000 : ℝ)
  | 5 => (23 / 125000000000 : ℝ)
  | 6 => (197 / 1000000000000 : ℝ)
  | 7 => (211 / 1000000000000 : ℝ)
  | 8 => (113 / 500000000000 : ℝ)
  | 9 => (121 / 500000000000 : ℝ)
  | 10 => (259 / 1000000000000 : ℝ)
  | 11 => (277 / 1000000000000 : ℝ)
  | 12 => (59 / 200000000000 : ℝ)
  | 13 => (63 / 200000000000 : ℝ)
  | 14 => (21 / 62500000000 : ℝ)
  | 15 => (179 / 500000000000 : ℝ)
  | 16 => (381 / 1000000000000 : ℝ)
  | 17 => (81 / 200000000000 : ℝ)
  | 18 => (431 / 1000000000000 : ℝ)
  | 19 => (229 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch004Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (139 / 1000000000000 : ℝ)
  | 1 => (149 / 1000000000000 : ℝ)
  | 2 => (161 / 1000000000000 : ℝ)
  | 3 => (43 / 250000000000 : ℝ)
  | 4 => (37 / 200000000000 : ℝ)
  | 5 => (99 / 500000000000 : ℝ)
  | 6 => (53 / 250000000000 : ℝ)
  | 7 => (227 / 1000000000000 : ℝ)
  | 8 => (243 / 1000000000000 : ℝ)
  | 9 => (13 / 50000000000 : ℝ)
  | 10 => (139 / 500000000000 : ℝ)
  | 11 => (37 / 125000000000 : ℝ)
  | 12 => (79 / 250000000000 : ℝ)
  | 13 => (337 / 1000000000000 : ℝ)
  | 14 => (359 / 1000000000000 : ℝ)
  | 15 => (191 / 500000000000 : ℝ)
  | 16 => (203 / 500000000000 : ℝ)
  | 17 => (27 / 62500000000 : ℝ)
  | 18 => (459 / 1000000000000 : ℝ)
  | 19 => (487 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch004Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((80 : ℝ) + (j.val : ℝ)) / 1600)
      (((80 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch004Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch004Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((80 : ℝ) + (j.val : ℝ)) / 1600)
    (((80 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch004Neg25WeightLower j.val) (hpThetaShiftThreeBatch004Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch004Neg25WeightLower, hpThetaShiftThreeBatch004Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch004Neg25_integral_bounds :
    (5731 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (3103 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (80 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch004Lower hpThetaJensenCellsBatch004Upper
    hpThetaShiftThreeBatch004Neg25WeightLower hpThetaShiftThreeBatch004Neg25WeightUpper hpThetaJensenCellsBatch004_bounds hpThetaShiftThreeBatch004Neg25_weight_bounds
  have hl : (5731 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch004Lower j * hpThetaShiftThreeBatch004Neg25WeightLower j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftThreeBatch004Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftThreeBatch004Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch004Lower j * hpThetaShiftThreeBatch004Neg25WeightUpper j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftThreeBatch004Neg25WeightUpper j) / 1600) ≤ (3103 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftThreeBatch004Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (80 : ℝ) / 1600 = 4 / 80 by norm_num,
    show ((80 : ℝ) + 20) / 1600 = (4 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch004Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch004Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch004Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch004Neg25_integral_bounds
end HodgeProofHP
