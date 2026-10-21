/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch006

/-! Exact signed weight and batch integral certificates, batch 6 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch006Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1309 / 1000000000000 : ℝ)
  | 1 => (1373 / 1000000000000 : ℝ)
  | 2 => (9 / 6250000000 : ℝ)
  | 3 => (1509 / 1000000000000 : ℝ)
  | 4 => (79 / 50000000000 : ℝ)
  | 5 => (331 / 200000000000 : ℝ)
  | 6 => (433 / 250000000000 : ℝ)
  | 7 => (453 / 250000000000 : ℝ)
  | 8 => (379 / 200000000000 : ℝ)
  | 9 => (1981 / 1000000000000 : ℝ)
  | 10 => (207 / 100000000000 : ℝ)
  | 11 => (2163 / 1000000000000 : ℝ)
  | 12 => (1129 / 500000000000 : ℝ)
  | 13 => (2357 / 1000000000000 : ℝ)
  | 14 => (123 / 50000000000 : ℝ)
  | 15 => (1283 / 500000000000 : ℝ)
  | 16 => (107 / 40000000000 : ℝ)
  | 17 => (697 / 250000000000 : ℝ)
  | 18 => (1453 / 500000000000 : ℝ)
  | 19 => (3027 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch006Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (687 / 500000000000 : ℝ)
  | 1 => (1441 / 1000000000000 : ℝ)
  | 2 => (151 / 100000000000 : ℝ)
  | 3 => (1581 / 1000000000000 : ℝ)
  | 4 => (207 / 125000000000 : ℝ)
  | 5 => (1733 / 1000000000000 : ℝ)
  | 6 => (1813 / 1000000000000 : ℝ)
  | 7 => (237 / 125000000000 : ℝ)
  | 8 => (991 / 500000000000 : ℝ)
  | 9 => (2071 / 1000000000000 : ℝ)
  | 10 => (541 / 250000000000 : ℝ)
  | 11 => (2259 / 1000000000000 : ℝ)
  | 12 => (1179 / 500000000000 : ℝ)
  | 13 => (2461 / 1000000000000 : ℝ)
  | 14 => (2567 / 1000000000000 : ℝ)
  | 15 => (669 / 250000000000 : ℝ)
  | 16 => (2789 / 1000000000000 : ℝ)
  | 17 => (2907 / 1000000000000 : ℝ)
  | 18 => (757 / 250000000000 : ℝ)
  | 19 => (3153 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch006Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((120 : ℝ) + (j.val : ℝ)) / 1600)
      (((120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch006Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch006Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((120 : ℝ) + (j.val : ℝ)) / 1600)
    (((120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch006Neg100WeightLower j.val) (hpThetaShiftThreeBatch006Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch006Neg100WeightLower, hpThetaShiftThreeBatch006Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch006Neg100_integral_bounds :
    (43353 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (9159 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch006Lower hpThetaJensenCellsBatch006Upper
    hpThetaShiftThreeBatch006Neg100WeightLower hpThetaShiftThreeBatch006Neg100WeightUpper hpThetaJensenCellsBatch006_bounds hpThetaShiftThreeBatch006Neg100_weight_bounds
  have hl : (43353 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch006Lower j * hpThetaShiftThreeBatch006Neg100WeightLower j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftThreeBatch006Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftThreeBatch006Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch006Lower j * hpThetaShiftThreeBatch006Neg100WeightUpper j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftThreeBatch006Neg100WeightUpper j) / 1600) ≤ (9159 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftThreeBatch006Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (120 : ℝ) / 1600 = 6 / 80 by norm_num,
    show ((120 : ℝ) + 20) / 1600 = (6 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch006Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (17 / 12500000000 : ℝ)
  | 1 => (357 / 250000000000 : ℝ)
  | 2 => (749 / 500000000000 : ℝ)
  | 3 => (1571 / 1000000000000 : ℝ)
  | 4 => (823 / 500000000000 : ℝ)
  | 5 => (69 / 40000000000 : ℝ)
  | 6 => (1807 / 1000000000000 : ℝ)
  | 7 => (1891 / 1000000000000 : ℝ)
  | 8 => (99 / 50000000000 : ℝ)
  | 9 => (2071 / 1000000000000 : ℝ)
  | 10 => (1083 / 500000000000 : ℝ)
  | 11 => (283 / 125000000000 : ℝ)
  | 12 => (1183 / 500000000000 : ℝ)
  | 13 => (2471 / 1000000000000 : ℝ)
  | 14 => (2581 / 1000000000000 : ℝ)
  | 15 => (1347 / 500000000000 : ℝ)
  | 16 => (2811 / 1000000000000 : ℝ)
  | 17 => (2933 / 1000000000000 : ℝ)
  | 18 => (1529 / 500000000000 : ℝ)
  | 19 => (797 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch006Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1429 / 1000000000000 : ℝ)
  | 1 => (1499 / 1000000000000 : ℝ)
  | 2 => (393 / 250000000000 : ℝ)
  | 3 => (1647 / 1000000000000 : ℝ)
  | 4 => (863 / 500000000000 : ℝ)
  | 5 => (113 / 62500000000 : ℝ)
  | 6 => (473 / 250000000000 : ℝ)
  | 7 => (1981 / 1000000000000 : ℝ)
  | 8 => (259 / 125000000000 : ℝ)
  | 9 => (2167 / 1000000000000 : ℝ)
  | 10 => (453 / 200000000000 : ℝ)
  | 11 => (2367 / 1000000000000 : ℝ)
  | 12 => (309 / 125000000000 : ℝ)
  | 13 => (1291 / 500000000000 : ℝ)
  | 14 => (539 / 200000000000 : ℝ)
  | 15 => (703 / 250000000000 : ℝ)
  | 16 => (1467 / 500000000000 : ℝ)
  | 17 => (3059 / 1000000000000 : ℝ)
  | 18 => (3189 / 1000000000000 : ℝ)
  | 19 => (831 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch006Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((120 : ℝ) + (j.val : ℝ)) / 1600)
      (((120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch006Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch006Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((120 : ℝ) + (j.val : ℝ)) / 1600)
    (((120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch006Neg70WeightLower j.val) (hpThetaShiftThreeBatch006Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch006Neg70WeightLower, hpThetaShiftThreeBatch006Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch006Neg70_integral_bounds :
    (45389 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (47981 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch006Lower hpThetaJensenCellsBatch006Upper
    hpThetaShiftThreeBatch006Neg70WeightLower hpThetaShiftThreeBatch006Neg70WeightUpper hpThetaJensenCellsBatch006_bounds hpThetaShiftThreeBatch006Neg70_weight_bounds
  have hl : (45389 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch006Lower j * hpThetaShiftThreeBatch006Neg70WeightLower j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftThreeBatch006Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftThreeBatch006Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch006Lower j * hpThetaShiftThreeBatch006Neg70WeightUpper j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftThreeBatch006Neg70WeightUpper j) / 1600) ≤ (47981 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftThreeBatch006Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (120 : ℝ) / 1600 = 6 / 80 by norm_num,
    show ((120 : ℝ) + 20) / 1600 = (6 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch006Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1403 / 1000000000000 : ℝ)
  | 1 => (737 / 500000000000 : ℝ)
  | 2 => (1547 / 1000000000000 : ℝ)
  | 3 => (1623 / 1000000000000 : ℝ)
  | 4 => (851 / 500000000000 : ℝ)
  | 5 => (223 / 125000000000 : ℝ)
  | 6 => (187 / 100000000000 : ℝ)
  | 7 => (1959 / 1000000000000 : ℝ)
  | 8 => (2051 / 1000000000000 : ℝ)
  | 9 => (2147 / 1000000000000 : ℝ)
  | 10 => (2247 / 1000000000000 : ℝ)
  | 11 => (47 / 20000000000 : ℝ)
  | 12 => (2457 / 1000000000000 : ℝ)
  | 13 => (2569 / 1000000000000 : ℝ)
  | 14 => (671 / 250000000000 : ℝ)
  | 15 => (701 / 250000000000 : ℝ)
  | 16 => (2927 / 1000000000000 : ℝ)
  | 17 => (191 / 62500000000 : ℝ)
  | 18 => (3189 / 1000000000000 : ℝ)
  | 19 => (1663 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch006Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (59 / 40000000000 : ℝ)
  | 1 => (387 / 250000000000 : ℝ)
  | 2 => (203 / 125000000000 : ℝ)
  | 3 => (1703 / 1000000000000 : ℝ)
  | 4 => (357 / 200000000000 : ℝ)
  | 5 => (1871 / 1000000000000 : ℝ)
  | 6 => (49 / 25000000000 : ℝ)
  | 7 => (513 / 250000000000 : ℝ)
  | 8 => (537 / 250000000000 : ℝ)
  | 9 => (281 / 125000000000 : ℝ)
  | 10 => (2351 / 1000000000000 : ℝ)
  | 11 => (1229 / 500000000000 : ℝ)
  | 12 => (257 / 100000000000 : ℝ)
  | 13 => (537 / 200000000000 : ℝ)
  | 14 => (561 / 200000000000 : ℝ)
  | 15 => (183 / 62500000000 : ℝ)
  | 16 => (3057 / 1000000000000 : ℝ)
  | 17 => (319 / 100000000000 : ℝ)
  | 18 => (3327 / 1000000000000 : ℝ)
  | 19 => (347 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch006Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((120 : ℝ) + (j.val : ℝ)) / 1600)
      (((120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch006Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch006Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((120 : ℝ) + (j.val : ℝ)) / 1600)
    (((120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch006Neg45WeightLower j.val) (hpThetaShiftThreeBatch006Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch006Neg45WeightLower, hpThetaShiftThreeBatch006Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch006Neg45_integral_bounds :
    (589 / 12500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (49839 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch006Lower hpThetaJensenCellsBatch006Upper
    hpThetaShiftThreeBatch006Neg45WeightLower hpThetaShiftThreeBatch006Neg45WeightUpper hpThetaJensenCellsBatch006_bounds hpThetaShiftThreeBatch006Neg45_weight_bounds
  have hl : (589 / 12500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch006Lower j * hpThetaShiftThreeBatch006Neg45WeightLower j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftThreeBatch006Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftThreeBatch006Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch006Lower j * hpThetaShiftThreeBatch006Neg45WeightUpper j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftThreeBatch006Neg45WeightUpper j) / 1600) ≤ (49839 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftThreeBatch006Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (120 : ℝ) / 1600 = 6 / 80 by norm_num,
    show ((120 : ℝ) + 20) / 1600 = (6 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch006Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (719 / 500000000000 : ℝ)
  | 1 => (1511 / 1000000000000 : ℝ)
  | 2 => (1587 / 1000000000000 : ℝ)
  | 3 => (333 / 200000000000 : ℝ)
  | 4 => (437 / 250000000000 : ℝ)
  | 5 => (1833 / 1000000000000 : ℝ)
  | 6 => (961 / 500000000000 : ℝ)
  | 7 => (1007 / 500000000000 : ℝ)
  | 8 => (211 / 100000000000 : ℝ)
  | 9 => (2209 / 1000000000000 : ℝ)
  | 10 => (2313 / 1000000000000 : ℝ)
  | 11 => (121 / 50000000000 : ℝ)
  | 12 => (633 / 250000000000 : ℝ)
  | 13 => (331 / 125000000000 : ℝ)
  | 14 => (173 / 62500000000 : ℝ)
  | 15 => (2893 / 1000000000000 : ℝ)
  | 16 => (1511 / 500000000000 : ℝ)
  | 17 => (789 / 250000000000 : ℝ)
  | 18 => (659 / 200000000000 : ℝ)
  | 19 => (3439 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch006Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (189 / 125000000000 : ℝ)
  | 1 => (397 / 250000000000 : ℝ)
  | 2 => (833 / 500000000000 : ℝ)
  | 3 => (1749 / 1000000000000 : ℝ)
  | 4 => (917 / 500000000000 : ℝ)
  | 5 => (1923 / 1000000000000 : ℝ)
  | 6 => (403 / 200000000000 : ℝ)
  | 7 => (2111 / 1000000000000 : ℝ)
  | 8 => (221 / 100000000000 : ℝ)
  | 9 => (1157 / 500000000000 : ℝ)
  | 10 => (2421 / 1000000000000 : ℝ)
  | 11 => (2533 / 1000000000000 : ℝ)
  | 12 => (2649 / 1000000000000 : ℝ)
  | 13 => (2769 / 1000000000000 : ℝ)
  | 14 => (1447 / 500000000000 : ℝ)
  | 15 => (3023 / 1000000000000 : ℝ)
  | 16 => (3157 / 1000000000000 : ℝ)
  | 17 => (103 / 31250000000 : ℝ)
  | 18 => (43 / 12500000000 : ℝ)
  | 19 => (3589 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch006Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((120 : ℝ) + (j.val : ℝ)) / 1600)
      (((120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch006Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch006Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((120 : ℝ) + (j.val : ℝ)) / 1600)
    (((120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch006Neg25WeightLower j.val) (hpThetaShiftThreeBatch006Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch006Neg25WeightLower, hpThetaShiftThreeBatch006Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch006Neg25_integral_bounds :
    (12133 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (10271 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch006Lower hpThetaJensenCellsBatch006Upper
    hpThetaShiftThreeBatch006Neg25WeightLower hpThetaShiftThreeBatch006Neg25WeightUpper hpThetaJensenCellsBatch006_bounds hpThetaShiftThreeBatch006Neg25_weight_bounds
  have hl : (12133 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch006Lower j * hpThetaShiftThreeBatch006Neg25WeightLower j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftThreeBatch006Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftThreeBatch006Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch006Lower j * hpThetaShiftThreeBatch006Neg25WeightUpper j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftThreeBatch006Neg25WeightUpper j) / 1600) ≤ (10271 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftThreeBatch006Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (120 : ℝ) / 1600 = 6 / 80 by norm_num,
    show ((120 : ℝ) + 20) / 1600 = (6 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch006Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch006Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch006Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch006Neg25_integral_bounds
end HodgeProofHP
