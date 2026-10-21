/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch013

/-! Exact signed weight and batch integral certificates, batch 13 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch013Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (78843 / 1000000000000 : ℝ)
  | 1 => (16037 / 200000000000 : ℝ)
  | 2 => (81539 / 1000000000000 : ℝ)
  | 3 => (16581 / 200000000000 : ℝ)
  | 4 => (42141 / 500000000000 : ℝ)
  | 5 => (85671 / 1000000000000 : ℝ)
  | 6 => (87071 / 1000000000000 : ℝ)
  | 7 => (88483 / 1000000000000 : ℝ)
  | 8 => (44953 / 500000000000 : ℝ)
  | 9 => (91339 / 1000000000000 : ℝ)
  | 10 => (92783 / 1000000000000 : ℝ)
  | 11 => (47119 / 500000000000 : ℝ)
  | 12 => (95703 / 1000000000000 : ℝ)
  | 13 => (48589 / 500000000000 : ℝ)
  | 14 => (98663 / 1000000000000 : ℝ)
  | 15 => (100157 / 1000000000000 : ℝ)
  | 16 => (101661 / 1000000000000 : ℝ)
  | 17 => (51587 / 500000000000 : ℝ)
  | 18 => (20939 / 200000000000 : ℝ)
  | 19 => (4249 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch013Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (40093 / 500000000000 : ℝ)
  | 1 => (4077 / 50000000000 : ℝ)
  | 2 => (41453 / 500000000000 : ℝ)
  | 3 => (84283 / 1000000000000 : ℝ)
  | 4 => (10709 / 125000000000 : ℝ)
  | 5 => (2721 / 31250000000 : ℝ)
  | 6 => (22121 / 250000000000 : ℝ)
  | 7 => (89907 / 1000000000000 : ℝ)
  | 8 => (4567 / 50000000000 : ℝ)
  | 9 => (5799 / 62500000000 : ℝ)
  | 10 => (94239 / 1000000000000 : ℝ)
  | 11 => (11963 / 125000000000 : ℝ)
  | 12 => (97179 / 1000000000000 : ℝ)
  | 13 => (12333 / 125000000000 : ℝ)
  | 14 => (50079 / 500000000000 : ℝ)
  | 15 => (50831 / 500000000000 : ℝ)
  | 16 => (4127 / 40000000000 : ℝ)
  | 17 => (13087 / 125000000000 : ℝ)
  | 18 => (53113 / 500000000000 : ℝ)
  | 19 => (21553 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch013Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((260 : ℝ) + (j.val : ℝ)) / 1600)
      (((260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch013Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch013Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((260 : ℝ) + (j.val : ℝ)) / 1600)
    (((260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch013Neg100WeightLower j.val) (hpThetaShiftThreeBatch013Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch013Neg100WeightLower, hpThetaShiftThreeBatch013Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch013Neg100_integral_bounds :
    (156151 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (1604523 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch013Lower hpThetaJensenCellsBatch013Upper
    hpThetaShiftThreeBatch013Neg100WeightLower hpThetaShiftThreeBatch013Neg100WeightUpper hpThetaJensenCellsBatch013_bounds hpThetaShiftThreeBatch013Neg100_weight_bounds
  have hl : (156151 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch013Lower j * hpThetaShiftThreeBatch013Neg100WeightLower j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftThreeBatch013Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftThreeBatch013Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch013Lower j * hpThetaShiftThreeBatch013Neg100WeightUpper j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftThreeBatch013Neg100WeightUpper j) / 1600) ≤ (1604523 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftThreeBatch013Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (260 : ℝ) / 1600 = 13 / 80 by norm_num,
    show ((260 : ℝ) + 20) / 1600 = (13 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch013Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (98729 / 1000000000000 : ℝ)
  | 1 => (20129 / 200000000000 : ℝ)
  | 2 => (102587 / 1000000000000 : ℝ)
  | 3 => (52277 / 500000000000 : ℝ)
  | 4 => (26637 / 250000000000 : ℝ)
  | 5 => (13571 / 125000000000 : ℝ)
  | 6 => (55307 / 500000000000 : ℝ)
  | 7 => (56343 / 500000000000 : ℝ)
  | 8 => (22957 / 200000000000 : ℝ)
  | 9 => (116911 / 1000000000000 : ℝ)
  | 10 => (119063 / 1000000000000 : ℝ)
  | 11 => (121243 / 1000000000000 : ℝ)
  | 12 => (123449 / 1000000000000 : ℝ)
  | 13 => (125681 / 1000000000000 : ℝ)
  | 14 => (127941 / 1000000000000 : ℝ)
  | 15 => (130229 / 1000000000000 : ℝ)
  | 16 => (132543 / 1000000000000 : ℝ)
  | 17 => (33721 / 250000000000 : ℝ)
  | 18 => (137253 / 1000000000000 : ℝ)
  | 19 => (139649 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch013Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (50323 / 500000000000 : ℝ)
  | 1 => (25647 / 250000000000 : ℝ)
  | 2 => (20911 / 200000000000 : ℝ)
  | 3 => (106549 / 1000000000000 : ℝ)
  | 4 => (108569 / 1000000000000 : ℝ)
  | 5 => (22123 / 200000000000 : ℝ)
  | 6 => (112687 / 1000000000000 : ℝ)
  | 7 => (57393 / 500000000000 : ℝ)
  | 8 => (7307 / 62500000000 : ℝ)
  | 9 => (14883 / 125000000000 : ℝ)
  | 10 => (30311 / 250000000000 : ℝ)
  | 11 => (2469 / 20000000000 : ℝ)
  | 12 => (62841 / 500000000000 : ℝ)
  | 13 => (63971 / 500000000000 : ℝ)
  | 14 => (13023 / 100000000000 : ℝ)
  | 15 => (2071 / 15625000000 : ℝ)
  | 16 => (26977 / 200000000000 : ℝ)
  | 17 => (68627 / 500000000000 : ℝ)
  | 18 => (2793 / 20000000000 : ℝ)
  | 19 => (142073 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch013Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((260 : ℝ) + (j.val : ℝ)) / 1600)
      (((260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch013Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch013Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((260 : ℝ) + (j.val : ℝ)) / 1600)
    (((260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch013Neg70WeightLower j.val) (hpThetaShiftThreeBatch013Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch013Neg70WeightLower, hpThetaShiftThreeBatch013Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch013Neg70_integral_bounds :
    (1002301 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (2065129 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch013Lower hpThetaJensenCellsBatch013Upper
    hpThetaShiftThreeBatch013Neg70WeightLower hpThetaShiftThreeBatch013Neg70WeightUpper hpThetaJensenCellsBatch013_bounds hpThetaShiftThreeBatch013Neg70_weight_bounds
  have hl : (1002301 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch013Lower j * hpThetaShiftThreeBatch013Neg70WeightLower j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftThreeBatch013Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftThreeBatch013Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch013Lower j * hpThetaShiftThreeBatch013Neg70WeightUpper j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftThreeBatch013Neg70WeightUpper j) / 1600) ≤ (2065129 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftThreeBatch013Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (260 : ℝ) / 1600 = 13 / 80 by norm_num,
    show ((260 : ℝ) + 20) / 1600 = (13 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch013Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (58451 / 500000000000 : ℝ)
  | 1 => (119357 / 1000000000000 : ℝ)
  | 2 => (30463 / 250000000000 : ℝ)
  | 3 => (124387 / 1000000000000 : ℝ)
  | 4 => (63481 / 500000000000 : ℝ)
  | 5 => (64789 / 500000000000 : ℝ)
  | 6 => (66117 / 500000000000 : ℝ)
  | 7 => (134933 / 1000000000000 : ℝ)
  | 8 => (137673 / 1000000000000 : ℝ)
  | 9 => (28091 / 200000000000 : ℝ)
  | 10 => (143281 / 1000000000000 : ℝ)
  | 11 => (146149 / 1000000000000 : ℝ)
  | 12 => (149061 / 1000000000000 : ℝ)
  | 13 => (152017 / 1000000000000 : ℝ)
  | 14 => (155017 / 1000000000000 : ℝ)
  | 15 => (79031 / 500000000000 : ℝ)
  | 16 => (1259 / 7812500000 : ℝ)
  | 17 => (164287 / 1000000000000 : ℝ)
  | 18 => (41867 / 250000000000 : ℝ)
  | 19 => (21337 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch013Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (59679 / 500000000000 : ℝ)
  | 1 => (121853 / 1000000000000 : ℝ)
  | 2 => (31097 / 250000000000 : ℝ)
  | 3 => (126963 / 1000000000000 : ℝ)
  | 4 => (129579 / 1000000000000 : ℝ)
  | 5 => (26447 / 200000000000 : ℝ)
  | 6 => (67467 / 500000000000 : ℝ)
  | 7 => (68837 / 500000000000 : ℝ)
  | 8 => (17557 / 125000000000 : ℝ)
  | 9 => (71641 / 500000000000 : ℝ)
  | 10 => (2923 / 20000000000 : ℝ)
  | 11 => (74531 / 500000000000 : ℝ)
  | 12 => (76009 / 500000000000 : ℝ)
  | 13 => (77509 / 500000000000 : ℝ)
  | 14 => (158063 / 1000000000000 : ℝ)
  | 15 => (161153 / 1000000000000 : ℝ)
  | 16 => (2567 / 15625000000 : ℝ)
  | 17 => (167469 / 1000000000000 : ℝ)
  | 18 => (170697 / 1000000000000 : ℝ)
  | 19 => (43493 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch013Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((260 : ℝ) + (j.val : ℝ)) / 1600)
      (((260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch013Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch013Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((260 : ℝ) + (j.val : ℝ)) / 1600)
    (((260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch013Neg45WeightLower j.val) (hpThetaShiftThreeBatch013Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch013Neg45WeightLower, hpThetaShiftThreeBatch013Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch013Neg45_integral_bounds :
    (2413077 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (2490117 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch013Lower hpThetaJensenCellsBatch013Upper
    hpThetaShiftThreeBatch013Neg45WeightLower hpThetaShiftThreeBatch013Neg45WeightUpper hpThetaJensenCellsBatch013_bounds hpThetaShiftThreeBatch013Neg45_weight_bounds
  have hl : (2413077 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch013Lower j * hpThetaShiftThreeBatch013Neg45WeightLower j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftThreeBatch013Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftThreeBatch013Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch013Lower j * hpThetaShiftThreeBatch013Neg45WeightUpper j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftThreeBatch013Neg45WeightUpper j) / 1600) ≤ (2490117 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftThreeBatch013Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (260 : ℝ) / 1600 = 13 / 80 by norm_num,
    show ((260 : ℝ) + 20) / 1600 = (13 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch013Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (66261 / 500000000000 : ℝ)
  | 1 => (135451 / 1000000000000 : ℝ)
  | 2 => (2163 / 15625000000 : ℝ)
  | 3 => (28293 / 200000000000 : ℝ)
  | 4 => (144551 / 1000000000000 : ℝ)
  | 5 => (36923 / 250000000000 : ℝ)
  | 6 => (150887 / 1000000000000 : ℝ)
  | 7 => (154137 / 1000000000000 : ℝ)
  | 8 => (157443 / 1000000000000 : ℝ)
  | 9 => (32161 / 200000000000 : ℝ)
  | 10 => (82113 / 500000000000 : ℝ)
  | 11 => (20963 / 125000000000 : ℝ)
  | 12 => (4281 / 25000000000 : ℝ)
  | 13 => (174837 / 1000000000000 : ℝ)
  | 14 => (178493 / 1000000000000 : ℝ)
  | 15 => (182211 / 1000000000000 : ℝ)
  | 16 => (18599 / 100000000000 : ℝ)
  | 17 => (23729 / 125000000000 : ℝ)
  | 18 => (24217 / 125000000000 : ℝ)
  | 19 => (39541 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch013Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (33863 / 250000000000 : ℝ)
  | 1 => (138433 / 1000000000000 : ℝ)
  | 2 => (70733 / 500000000000 : ℝ)
  | 3 => (18069 / 125000000000 : ℝ)
  | 4 => (147693 / 1000000000000 : ℝ)
  | 5 => (18861 / 125000000000 : ℝ)
  | 6 => (77069 / 500000000000 : ℝ)
  | 7 => (39361 / 250000000000 : ℝ)
  | 8 => (80403 / 500000000000 : ℝ)
  | 9 => (164227 / 1000000000000 : ℝ)
  | 10 => (33541 / 200000000000 : ℝ)
  | 11 => (171241 / 1000000000000 : ℝ)
  | 12 => (87419 / 500000000000 : ℝ)
  | 13 => (89247 / 500000000000 : ℝ)
  | 14 => (45553 / 250000000000 : ℝ)
  | 15 => (185991 / 1000000000000 : ℝ)
  | 16 => (189833 / 1000000000000 : ℝ)
  | 17 => (193737 / 1000000000000 : ℝ)
  | 18 => (98853 / 500000000000 : ℝ)
  | 19 => (201739 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch013Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((260 : ℝ) + (j.val : ℝ)) / 1600)
      (((260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch013Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch013Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((260 : ℝ) + (j.val : ℝ)) / 1600)
    (((260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch013Neg25WeightLower j.val) (hpThetaShiftThreeBatch013Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch013Neg25WeightLower, hpThetaShiftThreeBatch013Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch013Neg25_integral_bounds :
    (553291 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (1429007 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch013Lower hpThetaJensenCellsBatch013Upper
    hpThetaShiftThreeBatch013Neg25WeightLower hpThetaShiftThreeBatch013Neg25WeightUpper hpThetaJensenCellsBatch013_bounds hpThetaShiftThreeBatch013Neg25_weight_bounds
  have hl : (553291 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch013Lower j * hpThetaShiftThreeBatch013Neg25WeightLower j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftThreeBatch013Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftThreeBatch013Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch013Lower j * hpThetaShiftThreeBatch013Neg25WeightUpper j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftThreeBatch013Neg25WeightUpper j) / 1600) ≤ (1429007 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftThreeBatch013Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (260 : ℝ) / 1600 = 13 / 80 by norm_num,
    show ((260 : ℝ) + 20) / 1600 = (13 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch013Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch013Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch013Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch013Neg25_integral_bounds
end HodgeProofHP
