/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch016

/-! Exact signed weight and batch integral certificates, batch 16 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch016Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (8581 / 50000000000 : ℝ)
  | 1 => (173129 / 1000000000000 : ℝ)
  | 2 => (1397 / 8000000000 : ℝ)
  | 3 => (176107 / 1000000000000 : ℝ)
  | 4 => (88787 / 500000000000 : ℝ)
  | 5 => (7161 / 40000000000 : ℝ)
  | 6 => (9023 / 50000000000 : ℝ)
  | 7 => (181879 / 1000000000000 : ℝ)
  | 8 => (183279 / 1000000000000 : ℝ)
  | 9 => (9233 / 50000000000 : ℝ)
  | 10 => (186021 / 1000000000000 : ℝ)
  | 11 => (93681 / 500000000000 : ℝ)
  | 12 => (94341 / 500000000000 : ℝ)
  | 13 => (189979 / 1000000000000 : ℝ)
  | 14 => (191253 / 1000000000000 : ℝ)
  | 15 => (192503 / 1000000000000 : ℝ)
  | 16 => (193727 / 1000000000000 : ℝ)
  | 17 => (97463 / 500000000000 : ℝ)
  | 18 => (196097 / 1000000000000 : ℝ)
  | 19 => (4931 / 25000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch016Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (17313 / 100000000000 : ℝ)
  | 1 => (87313 / 500000000000 : ℝ)
  | 2 => (44027 / 250000000000 : ℝ)
  | 3 => (7103 / 40000000000 : ℝ)
  | 4 => (89513 / 500000000000 : ℝ)
  | 5 => (180461 / 1000000000000 : ℝ)
  | 6 => (4547 / 25000000000 : ℝ)
  | 7 => (2291 / 12500000000 : ℝ)
  | 8 => (184661 / 1000000000000 : ℝ)
  | 9 => (93011 / 500000000000 : ℝ)
  | 10 => (187363 / 1000000000000 : ℝ)
  | 11 => (188683 / 1000000000000 : ℝ)
  | 12 => (9499 / 50000000000 : ℝ)
  | 13 => (95627 / 500000000000 : ℝ)
  | 14 => (24063 / 125000000000 : ℝ)
  | 15 => (3027 / 15625000000 : ℝ)
  | 16 => (194927 / 1000000000000 : ℝ)
  | 17 => (98049 / 500000000000 : ℝ)
  | 18 => (197241 / 1000000000000 : ℝ)
  | 19 => (39671 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch016Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((320 : ℝ) + (j.val : ℝ)) / 1600)
      (((320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch016Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch016Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((320 : ℝ) + (j.val : ℝ)) / 1600)
    (((320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch016Neg100WeightLower j.val) (hpThetaShiftThreeBatch016Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch016Neg100WeightLower, hpThetaShiftThreeBatch016Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch016Neg100_integral_bounds :
    (2730571 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (1391717 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch016Lower hpThetaJensenCellsBatch016Upper
    hpThetaShiftThreeBatch016Neg100WeightLower hpThetaShiftThreeBatch016Neg100WeightUpper hpThetaJensenCellsBatch016_bounds hpThetaShiftThreeBatch016Neg100_weight_bounds
  have hl : (2730571 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch016Lower j * hpThetaShiftThreeBatch016Neg100WeightLower j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftThreeBatch016Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftThreeBatch016Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch016Lower j * hpThetaShiftThreeBatch016Neg100WeightUpper j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftThreeBatch016Neg100WeightUpper j) / 1600) ≤ (1391717 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftThreeBatch016Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (320 : ℝ) / 1600 = 16 / 80 by norm_num,
    show ((320 : ℝ) + 20) / 1600 = (16 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch016Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (260999 / 1000000000000 : ℝ)
  | 1 => (132243 / 500000000000 : ℝ)
  | 2 => (66999 / 250000000000 : ℝ)
  | 3 => (271527 / 1000000000000 : ℝ)
  | 4 => (275079 / 1000000000000 : ℝ)
  | 5 => (69663 / 250000000000 : ℝ)
  | 6 => (141123 / 500000000000 : ℝ)
  | 7 => (14293 / 50000000000 : ℝ)
  | 8 => (289493 / 1000000000000 : ℝ)
  | 9 => (146573 / 500000000000 : ℝ)
  | 10 => (148409 / 500000000000 : ℝ)
  | 11 => (300509 / 1000000000000 : ℝ)
  | 12 => (304217 / 1000000000000 : ℝ)
  | 13 => (307943 / 1000000000000 : ℝ)
  | 14 => (155843 / 500000000000 : ℝ)
  | 15 => (157723 / 500000000000 : ℝ)
  | 16 => (159611 / 500000000000 : ℝ)
  | 17 => (323013 / 1000000000000 : ℝ)
  | 18 => (16341 / 50000000000 : ℝ)
  | 19 => (330641 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch016Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (264487 / 1000000000000 : ℝ)
  | 1 => (267997 / 1000000000000 : ℝ)
  | 2 => (33941 / 125000000000 : ℝ)
  | 3 => (6877 / 25000000000 : ℝ)
  | 4 => (278653 / 1000000000000 : ℝ)
  | 5 => (282247 / 1000000000000 : ℝ)
  | 6 => (285861 / 1000000000000 : ℝ)
  | 7 => (144747 / 500000000000 : ℝ)
  | 8 => (293147 / 1000000000000 : ℝ)
  | 9 => (296819 / 1000000000000 : ℝ)
  | 10 => (30051 / 100000000000 : ℝ)
  | 11 => (152109 / 500000000000 : ℝ)
  | 12 => (38493 / 125000000000 : ℝ)
  | 13 => (311687 / 1000000000000 : ℝ)
  | 14 => (315447 / 1000000000000 : ℝ)
  | 15 => (319223 / 1000000000000 : ℝ)
  | 16 => (161507 / 500000000000 : ℝ)
  | 17 => (326821 / 1000000000000 : ℝ)
  | 18 => (165321 / 500000000000 : ℝ)
  | 19 => (334477 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch016Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((320 : ℝ) + (j.val : ℝ)) / 1600)
      (((320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch016Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch016Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((320 : ℝ) + (j.val : ℝ)) / 1600)
    (((320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch016Neg70WeightLower j.val) (hpThetaShiftThreeBatch016Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch016Neg70WeightLower, hpThetaShiftThreeBatch016Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch016Neg70_integral_bounds :
    (34851 / 8000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (2231839 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch016Lower hpThetaJensenCellsBatch016Upper
    hpThetaShiftThreeBatch016Neg70WeightLower hpThetaShiftThreeBatch016Neg70WeightUpper hpThetaJensenCellsBatch016_bounds hpThetaShiftThreeBatch016Neg70_weight_bounds
  have hl : (34851 / 8000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch016Lower j * hpThetaShiftThreeBatch016Neg70WeightLower j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftThreeBatch016Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftThreeBatch016Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch016Lower j * hpThetaShiftThreeBatch016Neg70WeightUpper j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftThreeBatch016Neg70WeightUpper j) / 1600) ≤ (2231839 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftThreeBatch016Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (320 : ℝ) / 1600 = 16 / 80 by norm_num,
    show ((320 : ℝ) + 20) / 1600 = (16 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch016Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (347629 / 1000000000000 : ℝ)
  | 1 => (176569 / 500000000000 : ℝ)
  | 2 => (358709 / 1000000000000 : ℝ)
  | 3 => (182171 / 500000000000 : ℝ)
  | 4 => (92509 / 250000000000 : ℝ)
  | 5 => (375793 / 1000000000000 : ℝ)
  | 6 => (95403 / 250000000000 : ℝ)
  | 7 => (193747 / 500000000000 : ℝ)
  | 8 => (196719 / 500000000000 : ℝ)
  | 9 => (199723 / 500000000000 : ℝ)
  | 10 => (405517 / 1000000000000 : ℝ)
  | 11 => (102913 / 250000000000 : ℝ)
  | 12 => (8357 / 20000000000 : ℝ)
  | 13 => (26507 / 62500000000 : ℝ)
  | 14 => (430439 / 1000000000000 : ℝ)
  | 15 => (436829 / 1000000000000 : ℝ)
  | 16 => (88657 / 200000000000 : ℝ)
  | 17 => (89961 / 200000000000 : ℝ)
  | 18 => (456389 / 1000000000000 : ℝ)
  | 19 => (463039 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch016Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (353139 / 1000000000000 : ℝ)
  | 1 => (35871 / 100000000000 : ℝ)
  | 2 => (364343 / 1000000000000 : ℝ)
  | 3 => (370037 / 1000000000000 : ℝ)
  | 4 => (187897 / 500000000000 : ℝ)
  | 5 => (381613 / 1000000000000 : ℝ)
  | 6 => (77499 / 200000000000 : ℝ)
  | 7 => (393439 / 1000000000000 : ℝ)
  | 8 => (399447 / 1000000000000 : ℝ)
  | 9 => (202759 / 500000000000 : ℝ)
  | 10 => (411653 / 1000000000000 : ℝ)
  | 11 => (417851 / 1000000000000 : ℝ)
  | 12 => (424113 / 1000000000000 : ℝ)
  | 13 => (10761 / 25000000000 : ℝ)
  | 14 => (43683 / 100000000000 : ℝ)
  | 15 => (221643 / 500000000000 : ℝ)
  | 16 => (224903 / 500000000000 : ℝ)
  | 17 => (45639 / 100000000000 : ℝ)
  | 18 => (1447 / 3125000000 : ℝ)
  | 19 => (93951 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch016Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((320 : ℝ) + (j.val : ℝ)) / 1600)
      (((320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch016Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch016Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((320 : ℝ) + (j.val : ℝ)) / 1600)
    (((320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch016Neg45WeightLower j.val) (hpThetaShiftThreeBatch016Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch016Neg45WeightLower, hpThetaShiftThreeBatch016Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch016Neg45_integral_bounds :
    (2975933 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (6114663 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch016Lower hpThetaJensenCellsBatch016Upper
    hpThetaShiftThreeBatch016Neg45WeightLower hpThetaShiftThreeBatch016Neg45WeightUpper hpThetaJensenCellsBatch016_bounds hpThetaShiftThreeBatch016Neg45_weight_bounds
  have hl : (2975933 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch016Lower j * hpThetaShiftThreeBatch016Neg45WeightLower j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftThreeBatch016Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftThreeBatch016Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch016Lower j * hpThetaShiftThreeBatch016Neg45WeightUpper j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftThreeBatch016Neg45WeightUpper j) / 1600) ≤ (6114663 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftThreeBatch016Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (320 : ℝ) / 1600 = 16 / 80 by norm_num,
    show ((320 : ℝ) + 20) / 1600 = (16 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch016Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4253 / 10000000000 : ℝ)
  | 1 => (27043 / 62500000000 : ℝ)
  | 2 => (17607 / 40000000000 : ℝ)
  | 3 => (111941 / 250000000000 : ℝ)
  | 4 => (227727 / 500000000000 : ℝ)
  | 5 => (28953 / 62500000000 : ℝ)
  | 6 => (94229 / 200000000000 : ℝ)
  | 7 => (479147 / 1000000000000 : ℝ)
  | 8 => (97451 / 200000000000 : ℝ)
  | 9 => (495469 / 1000000000000 : ℝ)
  | 10 => (503791 / 1000000000000 : ℝ)
  | 11 => (256111 / 500000000000 : ℝ)
  | 12 => (520761 / 1000000000000 : ℝ)
  | 13 => (132353 / 250000000000 : ℝ)
  | 14 => (538173 / 1000000000000 : ℝ)
  | 15 => (547047 / 1000000000000 : ℝ)
  | 16 => (111207 / 200000000000 : ℝ)
  | 17 => (35321 / 62500000000 : ℝ)
  | 18 => (574353 / 1000000000000 : ℝ)
  | 19 => (116737 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch016Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (432689 / 1000000000000 : ℝ)
  | 1 => (27511 / 62500000000 : ℝ)
  | 2 => (89553 / 200000000000 : ℝ)
  | 3 => (91091 / 200000000000 : ℝ)
  | 4 => (463249 / 1000000000000 : ℝ)
  | 5 => (235573 / 500000000000 : ℝ)
  | 6 => (119787 / 250000000000 : ℝ)
  | 7 => (60907 / 125000000000 : ℝ)
  | 8 => (49547 / 100000000000 : ℝ)
  | 9 => (31487 / 62500000000 : ℝ)
  | 10 => (512223 / 1000000000000 : ℝ)
  | 11 => (260381 / 500000000000 : ℝ)
  | 12 => (529413 / 1000000000000 : ℝ)
  | 13 => (269087 / 500000000000 : ℝ)
  | 14 => (68381 / 125000000000 : ℝ)
  | 15 => (139009 / 250000000000 : ℝ)
  | 16 => (565137 / 1000000000000 : ℝ)
  | 17 => (287177 / 500000000000 : ℝ)
  | 18 => (291843 / 500000000000 : ℝ)
  | 19 => (37071 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch016Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((320 : ℝ) + (j.val : ℝ)) / 1600)
      (((320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch016Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch016Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((320 : ℝ) + (j.val : ℝ)) / 1600)
    (((320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch016Neg25WeightLower j.val) (hpThetaShiftThreeBatch016Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch016Neg25WeightLower, hpThetaShiftThreeBatch016Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch016Neg25_integral_bounds :
    (7394653 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (760891 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch016Lower hpThetaJensenCellsBatch016Upper
    hpThetaShiftThreeBatch016Neg25WeightLower hpThetaShiftThreeBatch016Neg25WeightUpper hpThetaJensenCellsBatch016_bounds hpThetaShiftThreeBatch016Neg25_weight_bounds
  have hl : (7394653 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch016Lower j * hpThetaShiftThreeBatch016Neg25WeightLower j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftThreeBatch016Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftThreeBatch016Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch016Lower j * hpThetaShiftThreeBatch016Neg25WeightUpper j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftThreeBatch016Neg25WeightUpper j) / 1600) ≤ (760891 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftThreeBatch016Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (320 : ℝ) / 1600 = 16 / 80 by norm_num,
    show ((320 : ℝ) + 20) / 1600 = (16 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch016Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch016Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch016Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch016Neg25_integral_bounds
end HodgeProofHP
