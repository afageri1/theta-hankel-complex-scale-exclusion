/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch005

/-! Exact signed weight and batch integral certificates, batch 5 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch005Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (57 / 125000000000 : ℝ)
  | 1 => (483 / 1000000000000 : ℝ)
  | 2 => (511 / 1000000000000 : ℝ)
  | 3 => (541 / 1000000000000 : ℝ)
  | 4 => (143 / 250000000000 : ℝ)
  | 5 => (121 / 200000000000 : ℝ)
  | 6 => (639 / 1000000000000 : ℝ)
  | 7 => (27 / 40000000000 : ℝ)
  | 8 => (713 / 1000000000000 : ℝ)
  | 9 => (47 / 62500000000 : ℝ)
  | 10 => (793 / 1000000000000 : ℝ)
  | 11 => (167 / 200000000000 : ℝ)
  | 12 => (11 / 12500000000 : ℝ)
  | 13 => (463 / 500000000000 : ℝ)
  | 14 => (487 / 500000000000 : ℝ)
  | 15 => (41 / 40000000000 : ℝ)
  | 16 => (1077 / 1000000000000 : ℝ)
  | 17 => (283 / 250000000000 : ℝ)
  | 18 => (1189 / 1000000000000 : ℝ)
  | 19 => (39 / 31250000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch005Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (121 / 250000000000 : ℝ)
  | 1 => (1 / 1953125000 : ℝ)
  | 2 => (271 / 500000000000 : ℝ)
  | 3 => (573 / 1000000000000 : ℝ)
  | 4 => (303 / 500000000000 : ℝ)
  | 5 => (1 / 1562500000 : ℝ)
  | 6 => (169 / 250000000000 : ℝ)
  | 7 => (357 / 500000000000 : ℝ)
  | 8 => (753 / 1000000000000 : ℝ)
  | 9 => (397 / 500000000000 : ℝ)
  | 10 => (209 / 250000000000 : ℝ)
  | 11 => (881 / 1000000000000 : ℝ)
  | 12 => (927 / 1000000000000 : ℝ)
  | 13 => (39 / 40000000000 : ℝ)
  | 14 => (513 / 500000000000 : ℝ)
  | 15 => (539 / 500000000000 : ℝ)
  | 16 => (1133 / 1000000000000 : ℝ)
  | 17 => (119 / 100000000000 : ℝ)
  | 18 => (1249 / 1000000000000 : ℝ)
  | 19 => (131 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch005Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((100 : ℝ) + (j.val : ℝ)) / 1600)
      (((100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch005Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch005Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((100 : ℝ) + (j.val : ℝ)) / 1600)
    (((100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch005Neg100WeightLower j.val) (hpThetaShiftThreeBatch005Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch005Neg100WeightLower, hpThetaShiftThreeBatch005Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch005Neg100_integral_bounds :
    (3403 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (18139 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch005Lower hpThetaJensenCellsBatch005Upper
    hpThetaShiftThreeBatch005Neg100WeightLower hpThetaShiftThreeBatch005Neg100WeightUpper hpThetaJensenCellsBatch005_bounds hpThetaShiftThreeBatch005Neg100_weight_bounds
  have hl : (3403 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch005Lower j * hpThetaShiftThreeBatch005Neg100WeightLower j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftThreeBatch005Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftThreeBatch005Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch005Lower j * hpThetaShiftThreeBatch005Neg100WeightUpper j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftThreeBatch005Neg100WeightUpper j) / 1600) ≤ (18139 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftThreeBatch005Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (100 : ℝ) / 1600 = 5 / 80 by norm_num,
    show ((100 : ℝ) + 20) / 1600 = (5 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch005Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (117 / 250000000000 : ℝ)
  | 1 => (31 / 62500000000 : ℝ)
  | 2 => (21 / 40000000000 : ℝ)
  | 3 => (139 / 250000000000 : ℝ)
  | 4 => (589 / 1000000000000 : ℝ)
  | 5 => (623 / 1000000000000 : ℝ)
  | 6 => (329 / 500000000000 : ℝ)
  | 7 => (87 / 125000000000 : ℝ)
  | 8 => (147 / 200000000000 : ℝ)
  | 9 => (97 / 125000000000 : ℝ)
  | 10 => (409 / 500000000000 : ℝ)
  | 11 => (863 / 1000000000000 : ℝ)
  | 12 => (909 / 1000000000000 : ℝ)
  | 13 => (479 / 500000000000 : ℝ)
  | 14 => (63 / 62500000000 : ℝ)
  | 15 => (1061 / 1000000000000 : ℝ)
  | 16 => (279 / 250000000000 : ℝ)
  | 17 => (587 / 500000000000 : ℝ)
  | 18 => (1233 / 1000000000000 : ℝ)
  | 19 => (259 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch005Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (497 / 1000000000000 : ℝ)
  | 1 => (263 / 500000000000 : ℝ)
  | 2 => (557 / 1000000000000 : ℝ)
  | 3 => (59 / 100000000000 : ℝ)
  | 4 => (39 / 62500000000 : ℝ)
  | 5 => (659 / 1000000000000 : ℝ)
  | 6 => (697 / 1000000000000 : ℝ)
  | 7 => (23 / 31250000000 : ℝ)
  | 8 => (777 / 1000000000000 : ℝ)
  | 9 => (819 / 1000000000000 : ℝ)
  | 10 => (27 / 31250000000 : ℝ)
  | 11 => (91 / 100000000000 : ℝ)
  | 12 => (959 / 1000000000000 : ℝ)
  | 13 => (1009 / 1000000000000 : ℝ)
  | 14 => (531 / 500000000000 : ℝ)
  | 15 => (1117 / 1000000000000 : ℝ)
  | 16 => (47 / 40000000000 : ℝ)
  | 17 => (617 / 500000000000 : ℝ)
  | 18 => (81 / 62500000000 : ℝ)
  | 19 => (1361 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch005Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((100 : ℝ) + (j.val : ℝ)) / 1600)
      (((100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch005Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch005Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((100 : ℝ) + (j.val : ℝ)) / 1600)
    (((100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch005Neg70WeightLower j.val) (hpThetaShiftThreeBatch005Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch005Neg70WeightLower, hpThetaShiftThreeBatch005Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch005Neg70_integral_bounds :
    (17579 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (18751 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch005Lower hpThetaJensenCellsBatch005Upper
    hpThetaShiftThreeBatch005Neg70WeightLower hpThetaShiftThreeBatch005Neg70WeightUpper hpThetaJensenCellsBatch005_bounds hpThetaShiftThreeBatch005Neg70_weight_bounds
  have hl : (17579 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch005Lower j * hpThetaShiftThreeBatch005Neg70WeightLower j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftThreeBatch005Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftThreeBatch005Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch005Lower j * hpThetaShiftThreeBatch005Neg70WeightUpper j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftThreeBatch005Neg70WeightUpper j) / 1600) ≤ (18751 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftThreeBatch005Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (100 : ℝ) / 1600 = 5 / 80 by norm_num,
    show ((100 : ℝ) + 20) / 1600 = (5 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch005Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (239 / 500000000000 : ℝ)
  | 1 => (507 / 1000000000000 : ℝ)
  | 2 => (537 / 1000000000000 : ℝ)
  | 3 => (569 / 1000000000000 : ℝ)
  | 4 => (603 / 1000000000000 : ℝ)
  | 5 => (319 / 500000000000 : ℝ)
  | 6 => (27 / 40000000000 : ℝ)
  | 7 => (713 / 1000000000000 : ℝ)
  | 8 => (753 / 1000000000000 : ℝ)
  | 9 => (199 / 250000000000 : ℝ)
  | 10 => (21 / 25000000000 : ℝ)
  | 11 => (443 / 500000000000 : ℝ)
  | 12 => (467 / 500000000000 : ℝ)
  | 13 => (123 / 125000000000 : ℝ)
  | 14 => (1037 / 1000000000000 : ℝ)
  | 15 => (273 / 250000000000 : ℝ)
  | 16 => (1149 / 1000000000000 : ℝ)
  | 17 => (1209 / 1000000000000 : ℝ)
  | 18 => (1271 / 1000000000000 : ℝ)
  | 19 => (167 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch005Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (127 / 250000000000 : ℝ)
  | 1 => (269 / 500000000000 : ℝ)
  | 2 => (57 / 100000000000 : ℝ)
  | 3 => (151 / 250000000000 : ℝ)
  | 4 => (639 / 1000000000000 : ℝ)
  | 5 => (169 / 250000000000 : ℝ)
  | 6 => (357 / 500000000000 : ℝ)
  | 7 => (377 / 500000000000 : ℝ)
  | 8 => (797 / 1000000000000 : ℝ)
  | 9 => (841 / 1000000000000 : ℝ)
  | 10 => (887 / 1000000000000 : ℝ)
  | 11 => (187 / 200000000000 : ℝ)
  | 12 => (197 / 200000000000 : ℝ)
  | 13 => (519 / 500000000000 : ℝ)
  | 14 => (1093 / 1000000000000 : ℝ)
  | 15 => (23 / 20000000000 : ℝ)
  | 16 => (121 / 100000000000 : ℝ)
  | 17 => (159 / 125000000000 : ℝ)
  | 18 => (1337 / 1000000000000 : ℝ)
  | 19 => (351 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch005Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((100 : ℝ) + (j.val : ℝ)) / 1600)
      (((100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch005Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch005Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((100 : ℝ) + (j.val : ℝ)) / 1600)
    (((100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch005Neg45WeightLower j.val) (hpThetaShiftThreeBatch005Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch005Neg45WeightLower, hpThetaShiftThreeBatch005Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch005Neg45_integral_bounds :
    (2257 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (19269 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch005Lower hpThetaJensenCellsBatch005Upper
    hpThetaShiftThreeBatch005Neg45WeightLower hpThetaShiftThreeBatch005Neg45WeightUpper hpThetaJensenCellsBatch005_bounds hpThetaShiftThreeBatch005Neg45_weight_bounds
  have hl : (2257 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch005Lower j * hpThetaShiftThreeBatch005Neg45WeightLower j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftThreeBatch005Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftThreeBatch005Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch005Lower j * hpThetaShiftThreeBatch005Neg45WeightUpper j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftThreeBatch005Neg45WeightUpper j) / 1600) ≤ (19269 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftThreeBatch005Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (100 : ℝ) / 1600 = 5 / 80 by norm_num,
    show ((100 : ℝ) + 20) / 1600 = (5 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch005Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (243 / 500000000000 : ℝ)
  | 1 => (129 / 250000000000 : ℝ)
  | 2 => (547 / 1000000000000 : ℝ)
  | 3 => (29 / 50000000000 : ℝ)
  | 4 => (307 / 500000000000 : ℝ)
  | 5 => (13 / 20000000000 : ℝ)
  | 6 => (43 / 62500000000 : ℝ)
  | 7 => (727 / 1000000000000 : ℝ)
  | 8 => (769 / 1000000000000 : ℝ)
  | 9 => (203 / 250000000000 : ℝ)
  | 10 => (857 / 1000000000000 : ℝ)
  | 11 => (181 / 200000000000 : ℝ)
  | 12 => (477 / 500000000000 : ℝ)
  | 13 => (503 / 500000000000 : ℝ)
  | 14 => (53 / 50000000000 : ℝ)
  | 15 => (1117 / 1000000000000 : ℝ)
  | 16 => (147 / 125000000000 : ℝ)
  | 17 => (1237 / 1000000000000 : ℝ)
  | 18 => (651 / 500000000000 : ℝ)
  | 19 => (1369 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch005Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (517 / 1000000000000 : ℝ)
  | 1 => (137 / 250000000000 : ℝ)
  | 2 => (581 / 1000000000000 : ℝ)
  | 3 => (123 / 200000000000 : ℝ)
  | 4 => (651 / 1000000000000 : ℝ)
  | 5 => (689 / 1000000000000 : ℝ)
  | 6 => (91 / 125000000000 : ℝ)
  | 7 => (77 / 100000000000 : ℝ)
  | 8 => (813 / 1000000000000 : ℝ)
  | 9 => (429 / 500000000000 : ℝ)
  | 10 => (453 / 500000000000 : ℝ)
  | 11 => (191 / 200000000000 : ℝ)
  | 12 => (1007 / 1000000000000 : ℝ)
  | 13 => (1061 / 1000000000000 : ℝ)
  | 14 => (559 / 500000000000 : ℝ)
  | 15 => (1177 / 1000000000000 : ℝ)
  | 16 => (619 / 500000000000 : ℝ)
  | 17 => (1303 / 1000000000000 : ℝ)
  | 18 => (137 / 100000000000 : ℝ)
  | 19 => (1439 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch005Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((100 : ℝ) + (j.val : ℝ)) / 1600)
      (((100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch005Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch005Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((100 : ℝ) + (j.val : ℝ)) / 1600)
    (((100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch005Neg25WeightLower j.val) (hpThetaShiftThreeBatch005Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch005Neg25WeightLower, hpThetaShiftThreeBatch005Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch005Neg25_integral_bounds :
    (4611 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (19689 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch005Lower hpThetaJensenCellsBatch005Upper
    hpThetaShiftThreeBatch005Neg25WeightLower hpThetaShiftThreeBatch005Neg25WeightUpper hpThetaJensenCellsBatch005_bounds hpThetaShiftThreeBatch005Neg25_weight_bounds
  have hl : (4611 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch005Lower j * hpThetaShiftThreeBatch005Neg25WeightLower j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftThreeBatch005Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftThreeBatch005Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch005Lower j * hpThetaShiftThreeBatch005Neg25WeightUpper j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftThreeBatch005Neg25WeightUpper j) / 1600) ≤ (19689 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftThreeBatch005Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (100 : ℝ) / 1600 = 5 / 80 by norm_num,
    show ((100 : ℝ) + 20) / 1600 = (5 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch005Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch005Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch005Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch005Neg25_integral_bounds
end HodgeProofHP
