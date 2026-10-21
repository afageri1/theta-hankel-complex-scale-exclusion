/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch011

/-! Exact signed weight and batch integral certificates, batch 11 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch011Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (8957 / 250000000000 : ℝ)
  | 1 => (18323 / 500000000000 : ℝ)
  | 2 => (37477 / 1000000000000 : ℝ)
  | 3 => (479 / 12500000000 : ℝ)
  | 4 => (39177 / 1000000000000 : ℝ)
  | 5 => (20023 / 500000000000 : ℝ)
  | 6 => (40929 / 1000000000000 : ℝ)
  | 7 => (1673 / 40000000000 : ℝ)
  | 8 => (21367 / 500000000000 : ℝ)
  | 9 => (5457 / 125000000000 : ℝ)
  | 10 => (44591 / 1000000000000 : ℝ)
  | 11 => (2277 / 50000000000 : ℝ)
  | 12 => (23251 / 500000000000 : ℝ)
  | 13 => (47477 / 1000000000000 : ℝ)
  | 14 => (24233 / 500000000000 : ℝ)
  | 15 => (49469 / 1000000000000 : ℝ)
  | 16 => (12621 / 250000000000 : ℝ)
  | 17 => (51513 / 1000000000000 : ℝ)
  | 18 => (13139 / 250000000000 : ℝ)
  | 19 => (13403 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch011Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (36647 / 1000000000000 : ℝ)
  | 1 => (18739 / 500000000000 : ℝ)
  | 2 => (38321 / 1000000000000 : ℝ)
  | 3 => (19589 / 500000000000 : ℝ)
  | 4 => (40047 / 1000000000000 : ℝ)
  | 5 => (4093 / 100000000000 : ℝ)
  | 6 => (20913 / 500000000000 : ℝ)
  | 7 => (8547 / 200000000000 : ℝ)
  | 8 => (43657 / 1000000000000 : ℝ)
  | 9 => (2787 / 62500000000 : ℝ)
  | 10 => (45541 / 1000000000000 : ℝ)
  | 11 => (46503 / 1000000000000 : ℝ)
  | 12 => (23739 / 500000000000 : ℝ)
  | 13 => (48467 / 1000000000000 : ℝ)
  | 14 => (4947 / 100000000000 : ℝ)
  | 15 => (10097 / 200000000000 : ℝ)
  | 16 => (25757 / 500000000000 : ℝ)
  | 17 => (52557 / 1000000000000 : ℝ)
  | 18 => (53613 / 1000000000000 : ℝ)
  | 19 => (27341 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch011Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((220 : ℝ) + (j.val : ℝ)) / 1600)
      (((220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch011Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch011Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((220 : ℝ) + (j.val : ℝ)) / 1600)
    (((220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch011Neg100WeightLower j.val) (hpThetaShiftThreeBatch011Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch011Neg100WeightLower, hpThetaShiftThreeBatch011Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch011Neg100_integral_bounds :
    (809427 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (418061 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch011Lower hpThetaJensenCellsBatch011Upper
    hpThetaShiftThreeBatch011Neg100WeightLower hpThetaShiftThreeBatch011Neg100WeightUpper hpThetaJensenCellsBatch011_bounds hpThetaShiftThreeBatch011Neg100_weight_bounds
  have hl : (809427 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch011Lower j * hpThetaShiftThreeBatch011Neg100WeightLower j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftThreeBatch011Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftThreeBatch011Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch011Lower j * hpThetaShiftThreeBatch011Neg100WeightUpper j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftThreeBatch011Neg100WeightUpper j) / 1600) ≤ (418061 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftThreeBatch011Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (220 : ℝ) / 1600 = 11 / 80 by norm_num,
    show ((220 : ℝ) + 20) / 1600 = (11 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch011Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (5187 / 125000000000 : ℝ)
  | 1 => (2657 / 62500000000 : ℝ)
  | 2 => (43547 / 1000000000000 : ℝ)
  | 3 => (22301 / 500000000000 : ℝ)
  | 4 => (1827 / 40000000000 : ℝ)
  | 5 => (2923 / 62500000000 : ℝ)
  | 6 => (1197 / 25000000000 : ℝ)
  | 7 => (12253 / 250000000000 : ℝ)
  | 8 => (10033 / 200000000000 : ℝ)
  | 9 => (51337 / 1000000000000 : ℝ)
  | 10 => (5253 / 100000000000 : ℝ)
  | 11 => (53743 / 1000000000000 : ℝ)
  | 12 => (54977 / 1000000000000 : ℝ)
  | 13 => (7029 / 125000000000 : ℝ)
  | 14 => (14377 / 250000000000 : ℝ)
  | 15 => (29403 / 500000000000 : ℝ)
  | 16 => (481 / 8000000000 : ℝ)
  | 17 => (30733 / 500000000000 : ℝ)
  | 18 => (62829 / 1000000000000 : ℝ)
  | 19 => (32107 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch011Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (42513 / 1000000000000 : ℝ)
  | 1 => (10887 / 250000000000 : ℝ)
  | 2 => (44603 / 1000000000000 : ℝ)
  | 3 => (11419 / 250000000000 : ℝ)
  | 4 => (46769 / 1000000000000 : ℝ)
  | 5 => (47881 / 1000000000000 : ℝ)
  | 6 => (49013 / 1000000000000 : ℝ)
  | 7 => (25083 / 500000000000 : ℝ)
  | 8 => (25669 / 500000000000 : ℝ)
  | 9 => (52531 / 1000000000000 : ℝ)
  | 10 => (3359 / 62500000000 : ℝ)
  | 11 => (27489 / 500000000000 : ℝ)
  | 12 => (56233 / 1000000000000 : ℝ)
  | 13 => (57509 / 1000000000000 : ℝ)
  | 14 => (58807 / 1000000000000 : ℝ)
  | 15 => (30063 / 500000000000 : ℝ)
  | 16 => (61467 / 1000000000000 : ℝ)
  | 17 => (6283 / 100000000000 : ℝ)
  | 18 => (12843 / 200000000000 : ℝ)
  | 19 => (65623 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch011Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((220 : ℝ) + (j.val : ℝ)) / 1600)
      (((220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch011Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch011Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((220 : ℝ) + (j.val : ℝ)) / 1600)
    (((220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch011Neg70WeightLower j.val) (hpThetaShiftThreeBatch011Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch011Neg70WeightLower, hpThetaShiftThreeBatch011Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch011Neg70_integral_bounds :
    (954063 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (12341 / 12500000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch011Lower hpThetaJensenCellsBatch011Upper
    hpThetaShiftThreeBatch011Neg70WeightLower hpThetaShiftThreeBatch011Neg70WeightUpper hpThetaJensenCellsBatch011_bounds hpThetaShiftThreeBatch011Neg70_weight_bounds
  have hl : (954063 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch011Lower j * hpThetaShiftThreeBatch011Neg70WeightLower j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftThreeBatch011Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftThreeBatch011Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch011Lower j * hpThetaShiftThreeBatch011Neg70WeightUpper j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftThreeBatch011Neg70WeightUpper j) / 1600) ≤ (12341 / 12500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftThreeBatch011Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (220 : ℝ) / 1600 = 11 / 80 by norm_num,
    show ((220 : ℝ) + 20) / 1600 = (11 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch011Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (727 / 15625000000 : ℝ)
  | 1 => (11931 / 250000000000 : ℝ)
  | 2 => (9789 / 200000000000 : ℝ)
  | 3 => (5019 / 100000000000 : ℝ)
  | 4 => (2573 / 50000000000 : ℝ)
  | 5 => (10551 / 200000000000 : ℝ)
  | 6 => (13519 / 250000000000 : ℝ)
  | 7 => (55423 / 1000000000000 : ℝ)
  | 8 => (56797 / 1000000000000 : ℝ)
  | 9 => (58197 / 1000000000000 : ℝ)
  | 10 => (7453 / 125000000000 : ℝ)
  | 11 => (61079 / 1000000000000 : ℝ)
  | 12 => (62561 / 1000000000000 : ℝ)
  | 13 => (8009 / 125000000000 : ℝ)
  | 14 => (65611 / 1000000000000 : ℝ)
  | 15 => (3359 / 50000000000 : ℝ)
  | 16 => (68777 / 1000000000000 : ℝ)
  | 17 => (17601 / 250000000000 : ℝ)
  | 18 => (72061 / 1000000000000 : ℝ)
  | 19 => (73749 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch011Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1909 / 40000000000 : ℝ)
  | 1 => (24473 / 500000000000 : ℝ)
  | 2 => (50191 / 1000000000000 : ℝ)
  | 3 => (51461 / 1000000000000 : ℝ)
  | 4 => (13189 / 250000000000 : ℝ)
  | 5 => (54077 / 1000000000000 : ℝ)
  | 6 => (433 / 7812500000 : ℝ)
  | 7 => (28399 / 500000000000 : ℝ)
  | 8 => (29099 / 500000000000 : ℝ)
  | 9 => (477 / 8000000000 : ℝ)
  | 10 => (1527 / 25000000000 : ℝ)
  | 11 => (31281 / 500000000000 : ℝ)
  | 12 => (64073 / 1000000000000 : ℝ)
  | 13 => (16403 / 250000000000 : ℝ)
  | 14 => (67181 / 1000000000000 : ℝ)
  | 15 => (34389 / 500000000000 : ℝ)
  | 16 => (14081 / 200000000000 : ℝ)
  | 17 => (36031 / 500000000000 : ℝ)
  | 18 => (59 / 800000000 : ℝ)
  | 19 => (18867 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch011Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((220 : ℝ) + (j.val : ℝ)) / 1600)
      (((220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch011Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch011Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((220 : ℝ) + (j.val : ℝ)) / 1600)
    (((220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch011Neg45WeightLower j.val) (hpThetaShiftThreeBatch011Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch011Neg45WeightLower, hpThetaShiftThreeBatch011Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch011Neg45_integral_bounds :
    (1083383 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (561261 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch011Lower hpThetaJensenCellsBatch011Upper
    hpThetaShiftThreeBatch011Neg45WeightLower hpThetaShiftThreeBatch011Neg45WeightUpper hpThetaJensenCellsBatch011_bounds hpThetaShiftThreeBatch011Neg45_weight_bounds
  have hl : (1083383 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch011Lower j * hpThetaShiftThreeBatch011Neg45WeightLower j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftThreeBatch011Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftThreeBatch011Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch011Lower j * hpThetaShiftThreeBatch011Neg45WeightUpper j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftThreeBatch011Neg45WeightUpper j) / 1600) ≤ (561261 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftThreeBatch011Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (220 : ℝ) / 1600 = 11 / 80 by norm_num,
    show ((220 : ℝ) + 20) / 1600 = (11 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch011Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (50761 / 1000000000000 : ℝ)
  | 1 => (5211 / 100000000000 : ℝ)
  | 2 => (53489 / 1000000000000 : ℝ)
  | 3 => (54897 / 1000000000000 : ℝ)
  | 4 => (11267 / 200000000000 : ℝ)
  | 5 => (14451 / 250000000000 : ℝ)
  | 6 => (7413 / 125000000000 : ℝ)
  | 7 => (12167 / 200000000000 : ℝ)
  | 8 => (31199 / 500000000000 : ℝ)
  | 9 => (63993 / 1000000000000 : ℝ)
  | 10 => (32811 / 500000000000 : ℝ)
  | 11 => (16821 / 250000000000 : ℝ)
  | 12 => (3449 / 50000000000 : ℝ)
  | 13 => (7071 / 100000000000 : ℝ)
  | 14 => (2899 / 40000000000 : ℝ)
  | 15 => (74277 / 1000000000000 : ℝ)
  | 16 => (38057 / 500000000000 : ℝ)
  | 17 => (19497 / 250000000000 : ℝ)
  | 18 => (79899 / 1000000000000 : ℝ)
  | 19 => (81847 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch011Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (52111 / 1000000000000 : ℝ)
  | 1 => (5349 / 100000000000 : ℝ)
  | 2 => (27449 / 500000000000 : ℝ)
  | 3 => (3521 / 62500000000 : ℝ)
  | 4 => (11561 / 200000000000 : ℝ)
  | 5 => (11861 / 200000000000 : ℝ)
  | 6 => (15209 / 250000000000 : ℝ)
  | 7 => (62399 / 1000000000000 : ℝ)
  | 8 => (31997 / 500000000000 : ℝ)
  | 9 => (65623 / 1000000000000 : ℝ)
  | 10 => (13457 / 200000000000 : ℝ)
  | 11 => (68981 / 1000000000000 : ℝ)
  | 12 => (70711 / 1000000000000 : ℝ)
  | 13 => (18119 / 250000000000 : ℝ)
  | 14 => (37139 / 500000000000 : ℝ)
  | 15 => (15223 / 200000000000 : ℝ)
  | 16 => (77989 / 1000000000000 : ℝ)
  | 17 => (799 / 10000000000 : ℝ)
  | 18 => (10231 / 125000000000 : ℝ)
  | 19 => (16767 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch011Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((220 : ℝ) + (j.val : ℝ)) / 1600)
      (((220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch011Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch011Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((220 : ℝ) + (j.val : ℝ)) / 1600)
    (((220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch011Neg25WeightLower j.val) (hpThetaShiftThreeBatch011Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch011Neg25WeightLower, hpThetaShiftThreeBatch011Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch011Neg25_integral_bounds :
    (149093 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (1236949 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch011Lower hpThetaJensenCellsBatch011Upper
    hpThetaShiftThreeBatch011Neg25WeightLower hpThetaShiftThreeBatch011Neg25WeightUpper hpThetaJensenCellsBatch011_bounds hpThetaShiftThreeBatch011Neg25_weight_bounds
  have hl : (149093 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch011Lower j * hpThetaShiftThreeBatch011Neg25WeightLower j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftThreeBatch011Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftThreeBatch011Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch011Lower j * hpThetaShiftThreeBatch011Neg25WeightUpper j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftThreeBatch011Neg25WeightUpper j) / 1600) ≤ (1236949 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftThreeBatch011Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (220 : ℝ) / 1600 = 11 / 80 by norm_num,
    show ((220 : ℝ) + 20) / 1600 = (11 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch011Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch011Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch011Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch011Neg25_integral_bounds
end HodgeProofHP
