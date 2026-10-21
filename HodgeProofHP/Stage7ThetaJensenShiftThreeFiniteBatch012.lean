/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch012

/-! Exact signed weight and batch integral certificates, batch 12 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch012Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (54681 / 1000000000000 : ℝ)
  | 1 => (13941 / 250000000000 : ℝ)
  | 2 => (2843 / 50000000000 : ℝ)
  | 3 => (5797 / 100000000000 : ℝ)
  | 4 => (59093 / 1000000000000 : ℝ)
  | 5 => (60229 / 1000000000000 : ℝ)
  | 6 => (61379 / 1000000000000 : ℝ)
  | 7 => (31271 / 500000000000 : ℝ)
  | 8 => (63719 / 1000000000000 : ℝ)
  | 9 => (16227 / 250000000000 : ℝ)
  | 10 => (66111 / 1000000000000 : ℝ)
  | 11 => (33663 / 500000000000 : ℝ)
  | 12 => (13711 / 200000000000 : ℝ)
  | 13 => (69797 / 1000000000000 : ℝ)
  | 14 => (71051 / 1000000000000 : ℝ)
  | 15 => (72319 / 1000000000000 : ℝ)
  | 16 => (73599 / 1000000000000 : ℝ)
  | 17 => (74891 / 1000000000000 : ℝ)
  | 18 => (19049 / 250000000000 : ℝ)
  | 19 => (38757 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch012Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (11153 / 200000000000 : ℝ)
  | 1 => (56861 / 1000000000000 : ℝ)
  | 2 => (57971 / 1000000000000 : ℝ)
  | 3 => (29547 / 500000000000 : ℝ)
  | 4 => (6023 / 100000000000 : ℝ)
  | 5 => (3069 / 50000000000 : ℝ)
  | 6 => (62543 / 1000000000000 : ℝ)
  | 7 => (1593 / 25000000000 : ℝ)
  | 8 => (64909 / 1000000000000 : ℝ)
  | 9 => (1033 / 15625000000 : ℝ)
  | 10 => (67327 / 1000000000000 : ℝ)
  | 11 => (17139 / 250000000000 : ℝ)
  | 12 => (34899 / 500000000000 : ℝ)
  | 13 => (17763 / 250000000000 : ℝ)
  | 14 => (113 / 1562500000 : ℝ)
  | 15 => (23 / 312500000 : ℝ)
  | 16 => (18723 / 250000000000 : ℝ)
  | 17 => (76197 / 1000000000000 : ℝ)
  | 18 => (15503 / 200000000000 : ℝ)
  | 19 => (19711 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch012Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((240 : ℝ) + (j.val : ℝ)) / 1600)
      (((240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch012Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch012Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((240 : ℝ) + (j.val : ℝ)) / 1600)
    (((240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch012Neg100WeightLower j.val) (hpThetaShiftThreeBatch012Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch012Neg100WeightLower, hpThetaShiftThreeBatch012Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch012Neg100_integral_bounds :
    (1157249 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (238433 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch012Lower hpThetaJensenCellsBatch012Upper
    hpThetaShiftThreeBatch012Neg100WeightLower hpThetaShiftThreeBatch012Neg100WeightUpper hpThetaJensenCellsBatch012_bounds hpThetaShiftThreeBatch012Neg100_weight_bounds
  have hl : (1157249 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch012Lower j * hpThetaShiftThreeBatch012Neg100WeightLower j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftThreeBatch012Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftThreeBatch012Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch012Lower j * hpThetaShiftThreeBatch012Neg100WeightUpper j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftThreeBatch012Neg100WeightUpper j) / 1600) ≤ (238433 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftThreeBatch012Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (240 : ℝ) / 1600 = 12 / 80 by norm_num,
    show ((240 : ℝ) + 20) / 1600 = (12 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch012Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (32811 / 500000000000 : ℝ)
  | 1 => (67051 / 1000000000000 : ℝ)
  | 2 => (8563 / 125000000000 : ℝ)
  | 3 => (3499 / 50000000000 : ℝ)
  | 4 => (35739 / 500000000000 : ℝ)
  | 5 => (73 / 1000000000 : ℝ)
  | 6 => (14909 / 200000000000 : ℝ)
  | 7 => (38057 / 500000000000 : ℝ)
  | 8 => (77707 / 1000000000000 : ℝ)
  | 9 => (79323 / 1000000000000 : ℝ)
  | 10 => (20241 / 250000000000 : ℝ)
  | 11 => (82629 / 1000000000000 : ℝ)
  | 12 => (42159 / 500000000000 : ℝ)
  | 13 => (5377 / 62500000000 : ℝ)
  | 14 => (8777 / 100000000000 : ℝ)
  | 15 => (44767 / 500000000000 : ℝ)
  | 16 => (45661 / 500000000000 : ℝ)
  | 17 => (5821 / 62500000000 : ℝ)
  | 18 => (3799 / 40000000000 : ℝ)
  | 19 => (96839 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch012Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (16763 / 250000000000 : ℝ)
  | 1 => (13701 / 200000000000 : ℝ)
  | 2 => (69981 / 1000000000000 : ℝ)
  | 3 => (71479 / 1000000000000 : ℝ)
  | 4 => (73001 / 1000000000000 : ℝ)
  | 5 => (37273 / 500000000000 : ℝ)
  | 6 => (15223 / 200000000000 : ℝ)
  | 7 => (19427 / 250000000000 : ℝ)
  | 8 => (19831 / 250000000000 : ℝ)
  | 9 => (16193 / 200000000000 : ℝ)
  | 10 => (8263 / 100000000000 : ℝ)
  | 11 => (84319 / 1000000000000 : ℝ)
  | 12 => (86033 / 1000000000000 : ℝ)
  | 13 => (87771 / 1000000000000 : ℝ)
  | 14 => (17907 / 200000000000 : ℝ)
  | 15 => (91323 / 1000000000000 : ℝ)
  | 16 => (93137 / 1000000000000 : ℝ)
  | 17 => (371 / 3906250000 : ℝ)
  | 18 => (2421 / 25000000000 : ℝ)
  | 19 => (9873 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch012Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((240 : ℝ) + (j.val : ℝ)) / 1600)
      (((240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch012Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch012Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((240 : ℝ) + (j.val : ℝ)) / 1600)
    (((240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch012Neg70WeightLower j.val) (hpThetaShiftThreeBatch012Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch012Neg70WeightLower, hpThetaShiftThreeBatch012Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch012Neg70_integral_bounds :
    (28359 / 20000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (9149 / 6250000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch012Lower hpThetaJensenCellsBatch012Upper
    hpThetaShiftThreeBatch012Neg70WeightLower hpThetaShiftThreeBatch012Neg70WeightUpper hpThetaJensenCellsBatch012_bounds hpThetaShiftThreeBatch012Neg70_weight_bounds
  have hl : (28359 / 20000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch012Lower j * hpThetaShiftThreeBatch012Neg70WeightLower j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftThreeBatch012Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftThreeBatch012Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch012Lower j * hpThetaShiftThreeBatch012Neg70WeightUpper j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftThreeBatch012Neg70WeightUpper j) / 1600) ≤ (9149 / 6250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftThreeBatch012Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (240 : ℝ) / 1600 = 12 / 80 by norm_num,
    show ((240 : ℝ) + 20) / 1600 = (12 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch012Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (75467 / 1000000000000 : ℝ)
  | 1 => (77217 / 1000000000000 : ℝ)
  | 2 => (39499 / 500000000000 : ℝ)
  | 3 => (80811 / 1000000000000 : ℝ)
  | 4 => (82657 / 1000000000000 : ℝ)
  | 5 => (16907 / 200000000000 : ℝ)
  | 6 => (43223 / 500000000000 : ℝ)
  | 7 => (88391 / 1000000000000 : ℝ)
  | 8 => (9037 / 100000000000 : ℝ)
  | 9 => (92383 / 1000000000000 : ℝ)
  | 10 => (9443 / 100000000000 : ℝ)
  | 11 => (96513 / 1000000000000 : ℝ)
  | 12 => (98631 / 1000000000000 : ℝ)
  | 13 => (20157 / 200000000000 : ℝ)
  | 14 => (1609 / 15625000000 : ℝ)
  | 15 => (105203 / 1000000000000 : ℝ)
  | 16 => (107467 / 1000000000000 : ℝ)
  | 17 => (13721 / 125000000000 : ℝ)
  | 18 => (28027 / 250000000000 : ℝ)
  | 19 => (22897 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch012Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (38609 / 500000000000 : ℝ)
  | 1 => (78999 / 1000000000000 : ℝ)
  | 2 => (20203 / 250000000000 : ℝ)
  | 3 => (41329 / 500000000000 : ℝ)
  | 4 => (10567 / 125000000000 : ℝ)
  | 5 => (86447 / 1000000000000 : ℝ)
  | 6 => (11049 / 125000000000 : ℝ)
  | 7 => (90371 / 1000000000000 : ℝ)
  | 8 => (2887 / 31250000000 : ℝ)
  | 9 => (94431 / 1000000000000 : ℝ)
  | 10 => (48257 / 500000000000 : ℝ)
  | 11 => (12329 / 125000000000 : ℝ)
  | 12 => (50393 / 500000000000 : ℝ)
  | 13 => (102977 / 1000000000000 : ℝ)
  | 14 => (26301 / 250000000000 : ℝ)
  | 15 => (26867 / 250000000000 : ℝ)
  | 16 => (109769 / 1000000000000 : ℝ)
  | 17 => (112109 / 1000000000000 : ℝ)
  | 18 => (57243 / 500000000000 : ℝ)
  | 19 => (116903 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch012Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((240 : ℝ) + (j.val : ℝ)) / 1600)
      (((240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch012Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch012Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((240 : ℝ) + (j.val : ℝ)) / 1600)
    (((240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch012Neg45WeightLower j.val) (hpThetaShiftThreeBatch012Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch012Neg45WeightLower, hpThetaShiftThreeBatch012Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch012Neg45_integral_bounds :
    (165441 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (855223 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch012Lower hpThetaJensenCellsBatch012Upper
    hpThetaShiftThreeBatch012Neg45WeightLower hpThetaShiftThreeBatch012Neg45WeightUpper hpThetaJensenCellsBatch012_bounds hpThetaShiftThreeBatch012Neg45_weight_bounds
  have hl : (165441 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch012Lower j * hpThetaShiftThreeBatch012Neg45WeightLower j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftThreeBatch012Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftThreeBatch012Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch012Lower j * hpThetaShiftThreeBatch012Neg45WeightUpper j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftThreeBatch012Neg45WeightUpper j) / 1600) ≤ (855223 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftThreeBatch012Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (240 : ℝ) / 1600 = 12 / 80 by norm_num,
    show ((240 : ℝ) + 20) / 1600 = (12 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch012Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (41917 / 500000000000 : ℝ)
  | 1 => (4293 / 50000000000 : ℝ)
  | 2 => (43963 / 500000000000 : ℝ)
  | 3 => (90031 / 1000000000000 : ℝ)
  | 4 => (92177 / 1000000000000 : ℝ)
  | 5 => (23591 / 250000000000 : ℝ)
  | 6 => (96593 / 1000000000000 : ℝ)
  | 7 => (6179 / 62500000000 : ℝ)
  | 8 => (50589 / 500000000000 : ℝ)
  | 9 => (6471 / 62500000000 : ℝ)
  | 10 => (52969 / 500000000000 : ℝ)
  | 11 => (21677 / 200000000000 : ℝ)
  | 12 => (110877 / 1000000000000 : ℝ)
  | 13 => (22683 / 200000000000 : ℝ)
  | 14 => (115999 / 1000000000000 : ℝ)
  | 15 => (118631 / 1000000000000 : ℝ)
  | 16 => (121311 / 1000000000000 : ℝ)
  | 17 => (124039 / 1000000000000 : ℝ)
  | 18 => (126817 / 1000000000000 : ℝ)
  | 19 => (32411 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch012Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (85861 / 1000000000000 : ℝ)
  | 1 => (87927 / 1000000000000 : ℝ)
  | 2 => (5627 / 62500000000 : ℝ)
  | 3 => (46089 / 500000000000 : ℝ)
  | 4 => (18873 / 200000000000 : ℝ)
  | 5 => (48297 / 500000000000 : ℝ)
  | 6 => (19773 / 200000000000 : ℝ)
  | 7 => (101179 / 1000000000000 : ℝ)
  | 8 => (103537 / 1000000000000 : ℝ)
  | 9 => (105939 / 1000000000000 : ℝ)
  | 10 => (54193 / 500000000000 : ℝ)
  | 11 => (55439 / 500000000000 : ℝ)
  | 12 => (14177 / 125000000000 : ℝ)
  | 13 => (29 / 250000000 : ℝ)
  | 14 => (14829 / 125000000000 : ℝ)
  | 15 => (3791 / 31250000000 : ℝ)
  | 16 => (3101 / 25000000000 : ℝ)
  | 17 => (63409 / 500000000000 : ℝ)
  | 18 => (25929 / 200000000000 : ℝ)
  | 19 => (132523 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch012Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((240 : ℝ) + (j.val : ℝ)) / 1600)
      (((240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch012Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch012Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((240 : ℝ) + (j.val : ℝ)) / 1600)
    (((240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch012Neg25WeightLower j.val) (hpThetaShiftThreeBatch012Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch012Neg25WeightLower, hpThetaShiftThreeBatch012Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch012Neg25_integral_bounds :
    (928269 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (384273 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch012Lower hpThetaJensenCellsBatch012Upper
    hpThetaShiftThreeBatch012Neg25WeightLower hpThetaShiftThreeBatch012Neg25WeightUpper hpThetaJensenCellsBatch012_bounds hpThetaShiftThreeBatch012Neg25_weight_bounds
  have hl : (928269 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch012Lower j * hpThetaShiftThreeBatch012Neg25WeightLower j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftThreeBatch012Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftThreeBatch012Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch012Lower j * hpThetaShiftThreeBatch012Neg25WeightUpper j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftThreeBatch012Neg25WeightUpper j) / 1600) ≤ (384273 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftThreeBatch012Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (240 : ℝ) / 1600 = 12 / 80 by norm_num,
    show ((240 : ℝ) + 20) / 1600 = (12 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch012Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch012Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch012Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch012Neg25_integral_bounds
end HodgeProofHP
