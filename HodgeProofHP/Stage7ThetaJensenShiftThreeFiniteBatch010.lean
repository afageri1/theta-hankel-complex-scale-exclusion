/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch010

/-! Exact signed weight and batch integral certificates, batch 10 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch010Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (22047 / 1000000000000 : ℝ)
  | 1 => (181 / 8000000000 : ℝ)
  | 2 => (4643 / 200000000000 : ℝ)
  | 3 => (4763 / 200000000000 : ℝ)
  | 4 => (24427 / 1000000000000 : ℝ)
  | 5 => (501 / 20000000000 : ℝ)
  | 6 => (5137 / 200000000000 : ℝ)
  | 7 => (26331 / 1000000000000 : ℝ)
  | 8 => (26989 / 1000000000000 : ℝ)
  | 9 => (27659 / 1000000000000 : ℝ)
  | 10 => (1417 / 50000000000 : ℝ)
  | 11 => (14517 / 500000000000 : ℝ)
  | 12 => (29739 / 1000000000000 : ℝ)
  | 13 => (30457 / 1000000000000 : ℝ)
  | 14 => (31187 / 1000000000000 : ℝ)
  | 15 => (31929 / 1000000000000 : ℝ)
  | 16 => (8171 / 250000000000 : ℝ)
  | 17 => (33451 / 1000000000000 : ℝ)
  | 18 => (34231 / 1000000000000 : ℝ)
  | 19 => (35023 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch010Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (11313 / 500000000000 : ℝ)
  | 1 => (1451 / 62500000000 : ℝ)
  | 2 => (2977 / 125000000000 : ℝ)
  | 3 => (6107 / 250000000000 : ℝ)
  | 4 => (25051 / 1000000000000 : ℝ)
  | 5 => (12843 / 500000000000 : ℝ)
  | 6 => (6583 / 250000000000 : ℝ)
  | 7 => (2699 / 100000000000 : ℝ)
  | 8 => (1383 / 50000000000 : ℝ)
  | 9 => (28341 / 1000000000000 : ℝ)
  | 10 => (5807 / 200000000000 : ℝ)
  | 11 => (1487 / 50000000000 : ℝ)
  | 12 => (15229 / 500000000000 : ℝ)
  | 13 => (7797 / 250000000000 : ℝ)
  | 14 => (3193 / 100000000000 : ℝ)
  | 15 => (6537 / 200000000000 : ℝ)
  | 16 => (8363 / 250000000000 : ℝ)
  | 17 => (4279 / 125000000000 : ℝ)
  | 18 => (2189 / 62500000000 : ℝ)
  | 19 => (35829 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch010Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((200 : ℝ) + (j.val : ℝ)) / 1600)
      (((200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch010Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch010Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((200 : ℝ) + (j.val : ℝ)) / 1600)
    (((200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch010Neg100WeightLower j.val) (hpThetaShiftThreeBatch010Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch010Neg100WeightLower, hpThetaShiftThreeBatch010Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch010Neg100_integral_bounds :
    (66489 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (551117 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch010Lower hpThetaJensenCellsBatch010Upper
    hpThetaShiftThreeBatch010Neg100WeightLower hpThetaShiftThreeBatch010Neg100WeightUpper hpThetaJensenCellsBatch010_bounds hpThetaShiftThreeBatch010Neg100_weight_bounds
  have hl : (66489 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch010Lower j * hpThetaShiftThreeBatch010Neg100WeightLower j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftThreeBatch010Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftThreeBatch010Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch010Lower j * hpThetaShiftThreeBatch010Neg100WeightUpper j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftThreeBatch010Neg100WeightUpper j) / 1600) ≤ (551117 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftThreeBatch010Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (200 : ℝ) / 1600 = 10 / 80 by norm_num,
    show ((200 : ℝ) + 20) / 1600 = (10 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch010Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (24783 / 1000000000000 : ℝ)
  | 1 => (6367 / 250000000000 : ℝ)
  | 2 => (3271 / 125000000000 : ℝ)
  | 3 => (26883 / 1000000000000 : ℝ)
  | 4 => (6903 / 250000000000 : ℝ)
  | 5 => (28357 / 1000000000000 : ℝ)
  | 6 => (29117 / 1000000000000 : ℝ)
  | 7 => (29893 / 1000000000000 : ℝ)
  | 8 => (7671 / 250000000000 : ℝ)
  | 9 => (7873 / 250000000000 : ℝ)
  | 10 => (8079 / 250000000000 : ℝ)
  | 11 => (8289 / 250000000000 : ℝ)
  | 12 => (17007 / 500000000000 : ℝ)
  | 13 => (4361 / 125000000000 : ℝ)
  | 14 => (35779 / 1000000000000 : ℝ)
  | 15 => (36687 / 1000000000000 : ℝ)
  | 16 => (37613 / 1000000000000 : ℝ)
  | 17 => (9639 / 250000000000 : ℝ)
  | 18 => (19759 / 500000000000 : ℝ)
  | 19 => (20249 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch010Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (25469 / 1000000000000 : ℝ)
  | 1 => (26169 / 1000000000000 : ℝ)
  | 2 => (6721 / 250000000000 : ℝ)
  | 3 => (27613 / 1000000000000 : ℝ)
  | 4 => (14179 / 500000000000 : ℝ)
  | 5 => (14559 / 500000000000 : ℝ)
  | 6 => (14947 / 500000000000 : ℝ)
  | 7 => (6137 / 200000000000 : ℝ)
  | 8 => (31493 / 1000000000000 : ℝ)
  | 9 => (32317 / 1000000000000 : ℝ)
  | 10 => (33157 / 1000000000000 : ℝ)
  | 11 => (6803 / 200000000000 : ℝ)
  | 12 => (34889 / 1000000000000 : ℝ)
  | 13 => (1789 / 50000000000 : ℝ)
  | 14 => (2293 / 62500000000 : ℝ)
  | 15 => (18807 / 500000000000 : ℝ)
  | 16 => (38557 / 1000000000000 : ℝ)
  | 17 => (39519 / 1000000000000 : ℝ)
  | 18 => (40499 / 1000000000000 : ℝ)
  | 19 => (41497 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch010Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((200 : ℝ) + (j.val : ℝ)) / 1600)
      (((200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch010Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch010Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((200 : ℝ) + (j.val : ℝ)) / 1600)
    (((200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch010Neg70WeightLower j.val) (hpThetaShiftThreeBatch010Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch010Neg70WeightLower, hpThetaShiftThreeBatch010Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch010Neg70_integral_bounds :
    (303457 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (314883 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch010Lower hpThetaJensenCellsBatch010Upper
    hpThetaShiftThreeBatch010Neg70WeightLower hpThetaShiftThreeBatch010Neg70WeightUpper hpThetaJensenCellsBatch010_bounds hpThetaShiftThreeBatch010Neg70_weight_bounds
  have hl : (303457 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch010Lower j * hpThetaShiftThreeBatch010Neg70WeightLower j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftThreeBatch010Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftThreeBatch010Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch010Lower j * hpThetaShiftThreeBatch010Neg70WeightUpper j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftThreeBatch010Neg70WeightUpper j) / 1600) ≤ (314883 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftThreeBatch010Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (200 : ℝ) / 1600 = 10 / 80 by norm_num,
    show ((200 : ℝ) + 20) / 1600 = (10 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch010Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1699 / 62500000000 : ℝ)
  | 1 => (6991 / 250000000000 : ℝ)
  | 2 => (14381 / 500000000000 : ℝ)
  | 3 => (14789 / 500000000000 : ℝ)
  | 4 => (30413 / 1000000000000 : ℝ)
  | 5 => (15633 / 500000000000 : ℝ)
  | 6 => (32139 / 1000000000000 : ℝ)
  | 7 => (3303 / 100000000000 : ℝ)
  | 8 => (16971 / 500000000000 : ℝ)
  | 9 => (34873 / 1000000000000 : ℝ)
  | 10 => (1433 / 40000000000 : ℝ)
  | 11 => (36797 / 1000000000000 : ℝ)
  | 12 => (3779 / 100000000000 : ℝ)
  | 13 => (9701 / 250000000000 : ℝ)
  | 14 => (249 / 6250000000 : ℝ)
  | 15 => (20449 / 500000000000 : ℝ)
  | 16 => (20989 / 500000000000 : ℝ)
  | 17 => (43081 / 1000000000000 : ℝ)
  | 18 => (44207 / 1000000000000 : ℝ)
  | 19 => (9071 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch010Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5593 / 200000000000 : ℝ)
  | 1 => (28763 / 1000000000000 : ℝ)
  | 2 => (29579 / 1000000000000 : ℝ)
  | 3 => (15207 / 500000000000 : ℝ)
  | 4 => (31267 / 1000000000000 : ℝ)
  | 5 => (1607 / 50000000000 : ℝ)
  | 6 => (33031 / 1000000000000 : ℝ)
  | 7 => (33943 / 1000000000000 : ℝ)
  | 8 => (17437 / 500000000000 : ℝ)
  | 9 => (17913 / 500000000000 : ℝ)
  | 10 => (18399 / 500000000000 : ℝ)
  | 11 => (37791 / 1000000000000 : ℝ)
  | 12 => (7761 / 200000000000 : ℝ)
  | 13 => (39841 / 1000000000000 : ℝ)
  | 14 => (40899 / 1000000000000 : ℝ)
  | 15 => (41979 / 1000000000000 : ℝ)
  | 16 => (21541 / 500000000000 : ℝ)
  | 17 => (2763 / 62500000000 : ℝ)
  | 18 => (11339 / 250000000000 : ℝ)
  | 19 => (46529 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch010Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((200 : ℝ) + (j.val : ℝ)) / 1600)
      (((200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch010Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch010Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((200 : ℝ) + (j.val : ℝ)) / 1600)
    (((200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch010Neg45WeightLower j.val) (hpThetaShiftThreeBatch010Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch010Neg45WeightLower, hpThetaShiftThreeBatch010Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch010Neg45_integral_bounds :
    (84141 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (17481 / 25000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch010Lower hpThetaJensenCellsBatch010Upper
    hpThetaShiftThreeBatch010Neg45WeightLower hpThetaShiftThreeBatch010Neg45WeightUpper hpThetaJensenCellsBatch010_bounds hpThetaShiftThreeBatch010Neg45_weight_bounds
  have hl : (84141 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch010Lower j * hpThetaShiftThreeBatch010Neg45WeightLower j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftThreeBatch010Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftThreeBatch010Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch010Lower j * hpThetaShiftThreeBatch010Neg45WeightUpper j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftThreeBatch010Neg45WeightUpper j) / 1600) ≤ (17481 / 25000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftThreeBatch010Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (200 : ℝ) / 1600 = 10 / 80 by norm_num,
    show ((200 : ℝ) + 20) / 1600 = (10 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch010Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (5837 / 200000000000 : ℝ)
  | 1 => (6009 / 200000000000 : ℝ)
  | 2 => (15463 / 500000000000 : ℝ)
  | 3 => (7957 / 250000000000 : ℝ)
  | 4 => (2047 / 62500000000 : ℝ)
  | 5 => (33697 / 1000000000000 : ℝ)
  | 6 => (4333 / 125000000000 : ℝ)
  | 7 => (35653 / 1000000000000 : ℝ)
  | 8 => (18333 / 500000000000 : ℝ)
  | 9 => (18851 / 500000000000 : ℝ)
  | 10 => (19381 / 500000000000 : ℝ)
  | 11 => (19923 / 500000000000 : ℝ)
  | 12 => (8191 / 200000000000 : ℝ)
  | 13 => (5261 / 125000000000 : ℝ)
  | 14 => (43247 / 1000000000000 : ℝ)
  | 15 => (2777 / 62500000000 : ℝ)
  | 16 => (11411 / 250000000000 : ℝ)
  | 17 => (23441 / 500000000000 : ℝ)
  | 18 => (48147 / 1000000000000 : ℝ)
  | 19 => (309 / 6250000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch010Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (15023 / 500000000000 : ℝ)
  | 1 => (30927 / 1000000000000 : ℝ)
  | 2 => (31829 / 1000000000000 : ℝ)
  | 3 => (32753 / 1000000000000 : ℝ)
  | 4 => (16849 / 500000000000 : ℝ)
  | 5 => (6933 / 200000000000 : ℝ)
  | 6 => (17827 / 500000000000 : ℝ)
  | 7 => (36667 / 1000000000000 : ℝ)
  | 8 => (37703 / 1000000000000 : ℝ)
  | 9 => (38763 / 1000000000000 : ℝ)
  | 10 => (39847 / 1000000000000 : ℝ)
  | 11 => (10239 / 250000000000 : ℝ)
  | 12 => (42089 / 1000000000000 : ℝ)
  | 13 => (2703 / 62500000000 : ℝ)
  | 14 => (44433 / 1000000000000 : ℝ)
  | 15 => (9129 / 200000000000 : ℝ)
  | 16 => (46883 / 1000000000000 : ℝ)
  | 17 => (12037 / 250000000000 : ℝ)
  | 18 => (49441 / 1000000000000 : ℝ)
  | 19 => (25381 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch010Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((200 : ℝ) + (j.val : ℝ)) / 1600)
      (((200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch010Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch010Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((200 : ℝ) + (j.val : ℝ)) / 1600)
    (((200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch010Neg25WeightLower j.val) (hpThetaShiftThreeBatch010Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch010Neg25WeightLower, hpThetaShiftThreeBatch010Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch010Neg25_integral_bounds :
    (364293 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (47341 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch010Lower hpThetaJensenCellsBatch010Upper
    hpThetaShiftThreeBatch010Neg25WeightLower hpThetaShiftThreeBatch010Neg25WeightUpper hpThetaJensenCellsBatch010_bounds hpThetaShiftThreeBatch010Neg25_weight_bounds
  have hl : (364293 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch010Lower j * hpThetaShiftThreeBatch010Neg25WeightLower j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftThreeBatch010Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftThreeBatch010Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch010Lower j * hpThetaShiftThreeBatch010Neg25WeightUpper j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftThreeBatch010Neg25WeightUpper j) / 1600) ≤ (47341 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftThreeBatch010Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (200 : ℝ) / 1600 = 10 / 80 by norm_num,
    show ((200 : ℝ) + 20) / 1600 = (10 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch010Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch010Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch010Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch010Neg25_integral_bounds
end HodgeProofHP
