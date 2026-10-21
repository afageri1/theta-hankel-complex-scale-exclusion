/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch009

/-! Exact signed weight and batch integral certificates, batch 9 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch009Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3157 / 250000000000 : ℝ)
  | 1 => (13009 / 1000000000000 : ℝ)
  | 2 => (13399 / 1000000000000 : ℝ)
  | 3 => (6899 / 500000000000 : ℝ)
  | 4 => (7103 / 500000000000 : ℝ)
  | 5 => (14623 / 1000000000000 : ℝ)
  | 6 => (15049 / 1000000000000 : ℝ)
  | 7 => (3871 / 250000000000 : ℝ)
  | 8 => (15929 / 1000000000000 : ℝ)
  | 9 => (16383 / 1000000000000 : ℝ)
  | 10 => (1053 / 62500000000 : ℝ)
  | 11 => (17321 / 1000000000000 : ℝ)
  | 12 => (3561 / 200000000000 : ℝ)
  | 13 => (18299 / 1000000000000 : ℝ)
  | 14 => (18803 / 1000000000000 : ℝ)
  | 15 => (19317 / 1000000000000 : ℝ)
  | 16 => (9921 / 500000000000 : ℝ)
  | 17 => (20377 / 1000000000000 : ℝ)
  | 18 => (20923 / 1000000000000 : ℝ)
  | 19 => (537 / 25000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch009Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1301 / 100000000000 : ℝ)
  | 1 => (67 / 5000000000 : ℝ)
  | 2 => (13799 / 1000000000000 : ℝ)
  | 3 => (14207 / 1000000000000 : ℝ)
  | 4 => (457 / 31250000000 : ℝ)
  | 5 => (301 / 20000000000 : ℝ)
  | 6 => (3097 / 200000000000 : ℝ)
  | 7 => (1593 / 100000000000 : ℝ)
  | 8 => (4 / 244140625 : ℝ)
  | 9 => (16849 / 1000000000000 : ℝ)
  | 10 => (8661 / 500000000000 : ℝ)
  | 11 => (8903 / 500000000000 : ℝ)
  | 12 => (183 / 10000000000 : ℝ)
  | 13 => (4701 / 250000000000 : ℝ)
  | 14 => (9659 / 500000000000 : ℝ)
  | 15 => (19843 / 1000000000000 : ℝ)
  | 16 => (10189 / 500000000000 : ℝ)
  | 17 => (5231 / 250000000000 : ℝ)
  | 18 => (21481 / 1000000000000 : ℝ)
  | 19 => (689 / 31250000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch009Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((180 : ℝ) + (j.val : ℝ)) / 1600)
      (((180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch009Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch009Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((180 : ℝ) + (j.val : ℝ)) / 1600)
    (((180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch009Neg100WeightLower j.val) (hpThetaShiftThreeBatch009Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch009Neg100WeightLower, hpThetaShiftThreeBatch009Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch009Neg100_integral_bounds :
    (326053 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (339 / 1000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch009Lower hpThetaJensenCellsBatch009Upper
    hpThetaShiftThreeBatch009Neg100WeightLower hpThetaShiftThreeBatch009Neg100WeightUpper hpThetaJensenCellsBatch009_bounds hpThetaShiftThreeBatch009Neg100_weight_bounds
  have hl : (326053 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch009Lower j * hpThetaShiftThreeBatch009Neg100WeightLower j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftThreeBatch009Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftThreeBatch009Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch009Lower j * hpThetaShiftThreeBatch009Neg100WeightUpper j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftThreeBatch009Neg100WeightUpper j) / 1600) ≤ (339 / 1000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftThreeBatch009Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (180 : ℝ) / 1600 = 9 / 80 by norm_num,
    show ((180 : ℝ) + 20) / 1600 = (9 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch009Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (6921 / 500000000000 : ℝ)
  | 1 => (14277 / 1000000000000 : ℝ)
  | 2 => (7361 / 500000000000 : ℝ)
  | 3 => (7589 / 500000000000 : ℝ)
  | 4 => (3129 / 200000000000 : ℝ)
  | 5 => (4031 / 250000000000 : ℝ)
  | 6 => (8307 / 500000000000 : ℝ)
  | 7 => (3423 / 200000000000 : ℝ)
  | 8 => (17629 / 1000000000000 : ℝ)
  | 9 => (9077 / 500000000000 : ℝ)
  | 10 => (4673 / 250000000000 : ℝ)
  | 11 => (9621 / 500000000000 : ℝ)
  | 12 => (4951 / 250000000000 : ℝ)
  | 13 => (1019 / 50000000000 : ℝ)
  | 14 => (2621 / 125000000000 : ℝ)
  | 15 => (2157 / 100000000000 : ℝ)
  | 16 => (4437 / 200000000000 : ℝ)
  | 17 => (11407 / 500000000000 : ℝ)
  | 18 => (733 / 31250000000 : ℝ)
  | 19 => (24113 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch009Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (7139 / 500000000000 : ℝ)
  | 1 => (14723 / 1000000000000 : ℝ)
  | 2 => (15179 / 1000000000000 : ℝ)
  | 3 => (7823 / 500000000000 : ℝ)
  | 4 => (129 / 8000000000 : ℝ)
  | 5 => (3323 / 200000000000 : ℝ)
  | 6 => (4279 / 250000000000 : ℝ)
  | 7 => (1763 / 100000000000 : ℝ)
  | 8 => (3631 / 200000000000 : ℝ)
  | 9 => (18693 / 1000000000000 : ℝ)
  | 10 => (19243 / 1000000000000 : ℝ)
  | 11 => (3961 / 200000000000 : ℝ)
  | 12 => (20381 / 1000000000000 : ℝ)
  | 13 => (20969 / 1000000000000 : ℝ)
  | 14 => (21571 / 1000000000000 : ℝ)
  | 15 => (11093 / 500000000000 : ℝ)
  | 16 => (4563 / 200000000000 : ℝ)
  | 17 => (23457 / 1000000000000 : ℝ)
  | 18 => (12057 / 500000000000 : ℝ)
  | 19 => (1549 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch009Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((180 : ℝ) + (j.val : ℝ)) / 1600)
      (((180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch009Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch009Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((180 : ℝ) + (j.val : ℝ)) / 1600)
    (((180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch009Neg70WeightLower j.val) (hpThetaShiftThreeBatch009Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch009Neg70WeightLower, hpThetaShiftThreeBatch009Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch009Neg70_integral_bounds :
    (90497 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (75367 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch009Lower hpThetaJensenCellsBatch009Upper
    hpThetaShiftThreeBatch009Neg70WeightLower hpThetaShiftThreeBatch009Neg70WeightUpper hpThetaJensenCellsBatch009_bounds hpThetaShiftThreeBatch009Neg70_weight_bounds
  have hl : (90497 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch009Lower j * hpThetaShiftThreeBatch009Neg70WeightLower j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftThreeBatch009Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftThreeBatch009Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch009Lower j * hpThetaShiftThreeBatch009Neg70WeightUpper j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftThreeBatch009Neg70WeightUpper j) / 1600) ≤ (75367 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftThreeBatch009Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (180 : ℝ) / 1600 = 9 / 80 by norm_num,
    show ((180 : ℝ) + 20) / 1600 = (9 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch009Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (931 / 62500000000 : ℝ)
  | 1 => (7689 / 500000000000 : ℝ)
  | 2 => (15871 / 1000000000000 : ℝ)
  | 3 => (8189 / 500000000000 : ℝ)
  | 4 => (16897 / 1000000000000 : ℝ)
  | 5 => (1743 / 100000000000 : ℝ)
  | 6 => (2247 / 125000000000 : ℝ)
  | 7 => (2317 / 125000000000 : ℝ)
  | 8 => (1911 / 100000000000 : ℝ)
  | 9 => (9849 / 500000000000 : ℝ)
  | 10 => (20301 / 1000000000000 : ℝ)
  | 11 => (10459 / 500000000000 : ℝ)
  | 12 => (21551 / 1000000000000 : ℝ)
  | 13 => (11099 / 500000000000 : ℝ)
  | 14 => (11431 / 500000000000 : ℝ)
  | 15 => (23541 / 1000000000000 : ℝ)
  | 16 => (6059 / 250000000000 : ℝ)
  | 17 => (6237 / 250000000000 : ℝ)
  | 18 => (6419 / 250000000000 : ℝ)
  | 19 => (26421 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch009Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (15379 / 1000000000000 : ℝ)
  | 1 => (31 / 1953125000 : ℝ)
  | 2 => (16379 / 1000000000000 : ℝ)
  | 3 => (8449 / 500000000000 : ℝ)
  | 4 => (17431 / 1000000000000 : ℝ)
  | 5 => (17977 / 1000000000000 : ℝ)
  | 6 => (18537 / 1000000000000 : ℝ)
  | 7 => (19111 / 1000000000000 : ℝ)
  | 8 => (19699 / 1000000000000 : ℝ)
  | 9 => (10151 / 500000000000 : ℝ)
  | 10 => (20919 / 1000000000000 : ℝ)
  | 11 => (1347 / 62500000000 : ℝ)
  | 12 => (22199 / 1000000000000 : ℝ)
  | 13 => (22863 / 1000000000000 : ℝ)
  | 14 => (11771 / 500000000000 : ℝ)
  | 15 => (24237 / 1000000000000 : ℝ)
  | 16 => (24949 / 1000000000000 : ℝ)
  | 17 => (25677 / 1000000000000 : ℝ)
  | 18 => (13211 / 500000000000 : ℝ)
  | 19 => (5437 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch009Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((180 : ℝ) + (j.val : ℝ)) / 1600)
      (((180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch009Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch009Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((180 : ℝ) + (j.val : ℝ)) / 1600)
    (((180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch009Neg45WeightLower j.val) (hpThetaShiftThreeBatch009Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch009Neg45WeightLower, hpThetaShiftThreeBatch009Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch009Neg45_integral_bounds :
    (98339 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (204939 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch009Lower hpThetaJensenCellsBatch009Upper
    hpThetaShiftThreeBatch009Neg45WeightLower hpThetaShiftThreeBatch009Neg45WeightUpper hpThetaJensenCellsBatch009_bounds hpThetaShiftThreeBatch009Neg45_weight_bounds
  have hl : (98339 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch009Lower j * hpThetaShiftThreeBatch009Neg45WeightLower j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftThreeBatch009Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftThreeBatch009Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch009Lower j * hpThetaShiftThreeBatch009Neg45WeightUpper j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftThreeBatch009Neg45WeightUpper j) / 1600) ≤ (204939 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftThreeBatch009Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (180 : ℝ) / 1600 = 9 / 80 by norm_num,
    show ((180 : ℝ) + 20) / 1600 = (9 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch009Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1971 / 125000000000 : ℝ)
  | 1 => (509 / 31250000000 : ℝ)
  | 2 => (16823 / 1000000000000 : ℝ)
  | 3 => (17371 / 1000000000000 : ℝ)
  | 4 => (8967 / 500000000000 : ℝ)
  | 5 => (1157 / 62500000000 : ℝ)
  | 6 => (9553 / 500000000000 : ℝ)
  | 7 => (9857 / 500000000000 : ℝ)
  | 8 => (20339 / 1000000000000 : ℝ)
  | 9 => (20979 / 1000000000000 : ℝ)
  | 10 => (21637 / 1000000000000 : ℝ)
  | 11 => (2231 / 100000000000 : ℝ)
  | 12 => (23001 / 1000000000000 : ℝ)
  | 13 => (2371 / 100000000000 : ℝ)
  | 14 => (6109 / 250000000000 : ℝ)
  | 15 => (1259 / 50000000000 : ℝ)
  | 16 => (25943 / 1000000000000 : ℝ)
  | 17 => (6681 / 250000000000 : ℝ)
  | 18 => (1101 / 40000000000 : ℝ)
  | 19 => (5669 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch009Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (16289 / 1000000000000 : ℝ)
  | 1 => (2103 / 125000000000 : ℝ)
  | 2 => (4343 / 250000000000 : ℝ)
  | 3 => (3587 / 200000000000 : ℝ)
  | 4 => (18513 / 1000000000000 : ℝ)
  | 5 => (19107 / 1000000000000 : ℝ)
  | 6 => (3943 / 200000000000 : ℝ)
  | 7 => (1017 / 50000000000 : ℝ)
  | 8 => (1049 / 50000000000 : ℝ)
  | 9 => (10819 / 500000000000 : ℝ)
  | 10 => (22311 / 1000000000000 : ℝ)
  | 11 => (11501 / 500000000000 : ℝ)
  | 12 => (23711 / 1000000000000 : ℝ)
  | 13 => (24437 / 1000000000000 : ℝ)
  | 14 => (25181 / 1000000000000 : ℝ)
  | 15 => (3243 / 125000000000 : ℝ)
  | 16 => (1069 / 40000000000 : ℝ)
  | 17 => (13763 / 500000000000 : ℝ)
  | 18 => (14173 / 500000000000 : ℝ)
  | 19 => (14593 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch009Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((180 : ℝ) + (j.val : ℝ)) / 1600)
      (((180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch009Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch009Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((180 : ℝ) + (j.val : ℝ)) / 1600)
    (((180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch009Neg25WeightLower j.val) (hpThetaShiftThreeBatch009Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch009Neg25WeightLower, hpThetaShiftThreeBatch009Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch009Neg25_integral_bounds :
    (83881 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (43733 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch009Lower hpThetaJensenCellsBatch009Upper
    hpThetaShiftThreeBatch009Neg25WeightLower hpThetaShiftThreeBatch009Neg25WeightUpper hpThetaJensenCellsBatch009_bounds hpThetaShiftThreeBatch009Neg25_weight_bounds
  have hl : (83881 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch009Lower j * hpThetaShiftThreeBatch009Neg25WeightLower j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftThreeBatch009Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftThreeBatch009Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch009Lower j * hpThetaShiftThreeBatch009Neg25WeightUpper j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftThreeBatch009Neg25WeightUpper j) / 1600) ≤ (43733 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftThreeBatch009Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (180 : ℝ) / 1600 = 9 / 80 by norm_num,
    show ((180 : ℝ) + 20) / 1600 = (9 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch009Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch009Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch009Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch009Neg25_integral_bounds
end HodgeProofHP
