/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch055

/-! Exact signed weight and batch integral certificates, batch 55 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch055Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-141981157 / 100000000000 : ℝ)
  | 1 => (-362658887 / 250000000000 : ℝ)
  | 2 => (-59278009 / 40000000000 : ℝ)
  | 3 => (-1513761897 / 1000000000000 : ℝ)
  | 4 => (-1546076929 / 1000000000000 : ℝ)
  | 5 => (-315780351 / 200000000000 : ℝ)
  | 6 => (-806121437 / 500000000000 : ℝ)
  | 7 => (-823053429 / 500000000000 : ℝ)
  | 8 => (-1680500347 / 1000000000000 : ℝ)
  | 9 => (-1715430049 / 1000000000000 : ℝ)
  | 10 => (-1750902747 / 1000000000000 : ℝ)
  | 11 => (-1786925293 / 1000000000000 : ℝ)
  | 12 => (-1823504611 / 1000000000000 : ℝ)
  | 13 => (-18606477 / 10000000000 : ℝ)
  | 14 => (-189836163 / 100000000000 : ℝ)
  | 15 => (-968326773 / 500000000000 : ℝ)
  | 16 => (-1975530667 / 1000000000000 : ℝ)
  | 17 => (-201500029 / 100000000000 : ℝ)
  | 18 => (-1027534893 / 500000000000 : ℝ)
  | 19 => (-1047873301 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch055Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1389472057 / 1000000000000 : ℝ)
  | 1 => (-1419811569 / 1000000000000 : ℝ)
  | 2 => (-1450635547 / 1000000000000 : ℝ)
  | 3 => (-92621889 / 62500000000 : ℝ)
  | 4 => (-189220237 / 125000000000 : ℝ)
  | 5 => (-6039363 / 3906250000 : ℝ)
  | 6 => (-789450877 / 500000000000 : ℝ)
  | 7 => (-1612242873 / 1000000000000 : ℝ)
  | 8 => (-1646106857 / 1000000000000 : ℝ)
  | 9 => (-840250173 / 500000000000 : ℝ)
  | 10 => (-53607189 / 31250000000 : ℝ)
  | 11 => (-875451373 / 500000000000 : ℝ)
  | 12 => (-446731323 / 250000000000 : ℝ)
  | 13 => (-182350461 / 100000000000 : ℝ)
  | 14 => (-1860647699 / 1000000000000 : ℝ)
  | 15 => (-1898361629 / 1000000000000 : ℝ)
  | 16 => (-387330709 / 200000000000 : ℝ)
  | 17 => (-987765333 / 500000000000 : ℝ)
  | 18 => (-2015000289 / 1000000000000 : ℝ)
  | 19 => (-411013957 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch055Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1100 : ℝ) + (j.val : ℝ)) / 1600)
      (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch055Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch055Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1100 : ℝ) + (j.val : ℝ)) / 1600)
    (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch055Neg100WeightLower j.val) (hpThetaShiftThreeBatch055Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch055Neg100WeightLower, hpThetaShiftThreeBatch055Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch055Neg100_integral_bounds :
    (-23740389 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-113834397 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch055Lower hpThetaJensenCellsBatch055Upper
    hpThetaShiftThreeBatch055Neg100WeightLower hpThetaShiftThreeBatch055Neg100WeightUpper hpThetaJensenCellsBatch055_bounds hpThetaShiftThreeBatch055Neg100_weight_bounds
  have hl : (-23740389 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch055Lower j * hpThetaShiftThreeBatch055Neg100WeightLower j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftThreeBatch055Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftThreeBatch055Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch055Lower j * hpThetaShiftThreeBatch055Neg100WeightUpper j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftThreeBatch055Neg100WeightUpper j) / 1600) ≤ (-113834397 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftThreeBatch055Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1100 : ℝ) / 1600 = 55 / 80 by norm_num,
    show ((1100 : ℝ) + 20) / 1600 = (55 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch055Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (360016373 / 1000000000000 : ℝ)
  | 1 => (45119971 / 125000000000 : ℝ)
  | 2 => (90465267 / 250000000000 : ℝ)
  | 3 => (18135963 / 50000000000 : ℝ)
  | 4 => (363533313 / 1000000000000 : ℝ)
  | 5 => (72860437 / 200000000000 : ℝ)
  | 6 => (22814051 / 62500000000 : ℝ)
  | 7 => (182850067 / 500000000000 : ℝ)
  | 8 => (366327049 / 1000000000000 : ℝ)
  | 9 => (366904459 / 1000000000000 : ℝ)
  | 10 => (91857811 / 250000000000 : ℝ)
  | 11 => (36790627 / 100000000000 : ℝ)
  | 12 => (184164193 / 500000000000 : ℝ)
  | 13 => (92174107 / 250000000000 : ℝ)
  | 14 => (92252303 / 250000000000 : ℝ)
  | 15 => (369265541 / 1000000000000 : ℝ)
  | 16 => (1847321 / 5000000000 : ℝ)
  | 17 => (184801979 / 500000000000 : ℝ)
  | 18 => (23105223 / 62500000000 : ℝ)
  | 19 => (369657267 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch055Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (360959769 / 1000000000000 : ℝ)
  | 1 => (361861069 / 1000000000000 : ℝ)
  | 2 => (362719261 / 1000000000000 : ℝ)
  | 3 => (181766657 / 500000000000 : ℝ)
  | 4 => (182151093 / 500000000000 : ℝ)
  | 5 => (365024817 / 1000000000000 : ℝ)
  | 6 => (73140027 / 200000000000 : ℝ)
  | 7 => (7326541 / 20000000000 : ℝ)
  | 8 => (18345223 / 50000000000 : ℝ)
  | 9 => (73486249 / 200000000000 : ℝ)
  | 10 => (367906271 / 1000000000000 : ℝ)
  | 11 => (368328387 / 1000000000000 : ℝ)
  | 12 => (368696429 / 1000000000000 : ℝ)
  | 13 => (369009213 / 1000000000000 : ℝ)
  | 14 => (184632771 / 500000000000 : ℝ)
  | 15 => (369464201 / 1000000000000 : ℝ)
  | 16 => (369603959 / 1000000000000 : ℝ)
  | 17 => (369683569 / 1000000000000 : ℝ)
  | 18 => (46212947 / 125000000000 : ℝ)
  | 19 => (184850883 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch055Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1100 : ℝ) + (j.val : ℝ)) / 1600)
      (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch055Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch055Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1100 : ℝ) + (j.val : ℝ)) / 1600)
    (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch055Neg70WeightLower j.val) (hpThetaShiftThreeBatch055Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch055Neg70WeightLower, hpThetaShiftThreeBatch055Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch055Neg70_integral_bounds :
    (12314741 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (25195547 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch055Lower hpThetaJensenCellsBatch055Upper
    hpThetaShiftThreeBatch055Neg70WeightLower hpThetaShiftThreeBatch055Neg70WeightUpper hpThetaJensenCellsBatch055_bounds hpThetaShiftThreeBatch055Neg70_weight_bounds
  have hl : (12314741 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch055Lower j * hpThetaShiftThreeBatch055Neg70WeightLower j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftThreeBatch055Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftThreeBatch055Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch055Lower j * hpThetaShiftThreeBatch055Neg70WeightUpper j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftThreeBatch055Neg70WeightUpper j) / 1600) ≤ (25195547 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftThreeBatch055Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1100 : ℝ) / 1600 = 55 / 80 by norm_num,
    show ((1100 : ℝ) + 20) / 1600 = (55 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch055Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (81192601 / 1000000000000 : ℝ)
  | 1 => (83257139 / 1000000000000 : ℝ)
  | 2 => (42671941 / 500000000000 : ℝ)
  | 3 => (87452943 / 1000000000000 : ℝ)
  | 4 => (89584437 / 1000000000000 : ℝ)
  | 5 => (45869239 / 500000000000 : ℝ)
  | 6 => (4695759 / 50000000000 : ℝ)
  | 7 => (3003583 / 31250000000 : ℝ)
  | 8 => (98337019 / 1000000000000 : ℝ)
  | 9 => (5029119 / 50000000000 : ℝ)
  | 10 => (2057017 / 20000000000 : ℝ)
  | 11 => (105142541 / 1000000000000 : ℝ)
  | 12 => (107457561 / 1000000000000 : ℝ)
  | 13 => (54898011 / 500000000000 : ℝ)
  | 14 => (11215803 / 100000000000 : ℝ)
  | 15 => (57271847 / 500000000000 : ℝ)
  | 16 => (116953121 / 1000000000000 : ℝ)
  | 17 => (59693209 / 500000000000 : ℝ)
  | 18 => (121843691 / 1000000000000 : ℝ)
  | 19 => (124325043 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch055Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (4162857 / 50000000000 : ℝ)
  | 1 => (85343883 / 1000000000000 : ℝ)
  | 2 => (5465809 / 62500000000 : ℝ)
  | 3 => (44792219 / 500000000000 : ℝ)
  | 4 => (91738479 / 1000000000000 : ℝ)
  | 5 => (93915181 / 1000000000000 : ℝ)
  | 6 => (96114657 / 1000000000000 : ℝ)
  | 7 => (4916851 / 50000000000 : ℝ)
  | 8 => (100582381 / 1000000000000 : ℝ)
  | 9 => (102850851 / 1000000000000 : ℝ)
  | 10 => (52571271 / 500000000000 : ℝ)
  | 11 => (53728781 / 500000000000 : ℝ)
  | 12 => (109796023 / 1000000000000 : ℝ)
  | 13 => (112158031 / 1000000000000 : ℝ)
  | 14 => (22908739 / 200000000000 : ℝ)
  | 15 => (58476561 / 500000000000 : ℝ)
  | 16 => (119386419 / 1000000000000 : ℝ)
  | 17 => (30460923 / 250000000000 : ℝ)
  | 18 => (31081261 / 250000000000 : ℝ)
  | 19 => (6341529 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch055Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1100 : ℝ) + (j.val : ℝ)) / 1600)
      (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch055Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch055Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1100 : ℝ) + (j.val : ℝ)) / 1600)
    (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch055Neg45WeightLower j.val) (hpThetaShiftThreeBatch055Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch055Neg45WeightLower, hpThetaShiftThreeBatch055Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch055Neg45_integral_bounds :
    (850513 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (3553543 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch055Lower hpThetaJensenCellsBatch055Upper
    hpThetaShiftThreeBatch055Neg45WeightLower hpThetaShiftThreeBatch055Neg45WeightUpper hpThetaJensenCellsBatch055_bounds hpThetaShiftThreeBatch055Neg45_weight_bounds
  have hl : (850513 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch055Lower j * hpThetaShiftThreeBatch055Neg45WeightLower j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftThreeBatch055Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftThreeBatch055Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch055Lower j * hpThetaShiftThreeBatch055Neg45WeightUpper j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftThreeBatch055Neg45WeightUpper j) / 1600) ≤ (3553543 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftThreeBatch055Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1100 : ℝ) / 1600 = 55 / 80 by norm_num,
    show ((1100 : ℝ) + 20) / 1600 = (55 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch055Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-29663273 / 200000000000 : ℝ)
  | 1 => (-5971293 / 40000000000 : ℝ)
  | 2 => (-150249263 / 1000000000000 : ℝ)
  | 3 => (-151217129 / 1000000000000 : ℝ)
  | 4 => (-9511617 / 62500000000 : ℝ)
  | 5 => (-76577721 / 500000000000 : ℝ)
  | 6 => (-77062893 / 500000000000 : ℝ)
  | 7 => (-77548427 / 500000000000 : ℝ)
  | 8 => (-9754287 / 62500000000 : ℝ)
  | 9 => (-78520473 / 500000000000 : ℝ)
  | 10 => (-158013863 / 1000000000000 : ℝ)
  | 11 => (-158987289 / 1000000000000 : ℝ)
  | 12 => (-159961167 / 1000000000000 : ℝ)
  | 13 => (-160935443 / 1000000000000 : ℝ)
  | 14 => (-8095503 / 50000000000 : ℝ)
  | 15 => (-162884961 / 1000000000000 : ℝ)
  | 16 => (-20482511 / 125000000000 : ℝ)
  | 17 => (-20604423 / 125000000000 : ℝ)
  | 18 => (-41452697 / 250000000000 : ℝ)
  | 19 => (-166786243 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch055Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-147351431 / 1000000000000 : ℝ)
  | 1 => (-37079091 / 250000000000 : ℝ)
  | 2 => (-37320581 / 250000000000 : ℝ)
  | 3 => (-75124631 / 500000000000 : ℝ)
  | 4 => (-18902141 / 125000000000 : ℝ)
  | 5 => (-152185871 / 1000000000000 : ℝ)
  | 6 => (-153155441 / 1000000000000 : ℝ)
  | 7 => (-30825157 / 200000000000 : ℝ)
  | 8 => (-155096853 / 1000000000000 : ℝ)
  | 9 => (-156068591 / 1000000000000 : ℝ)
  | 10 => (-31408189 / 200000000000 : ℝ)
  | 11 => (-79006931 / 500000000000 : ℝ)
  | 12 => (-19873411 / 125000000000 : ℝ)
  | 13 => (-79980583 / 500000000000 : ℝ)
  | 14 => (-80467721 / 500000000000 : ℝ)
  | 15 => (-161910059 / 1000000000000 : ℝ)
  | 16 => (-1018031 / 6250000000 : ℝ)
  | 17 => (-163860087 / 1000000000000 : ℝ)
  | 18 => (-164835383 / 1000000000000 : ℝ)
  | 19 => (-165810787 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch055Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1100 : ℝ) + (j.val : ℝ)) / 1600)
      (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch055Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch055Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1100 : ℝ) + (j.val : ℝ)) / 1600)
    (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch055Neg25WeightLower j.val) (hpThetaShiftThreeBatch055Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch055Neg25WeightLower, hpThetaShiftThreeBatch055Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch055Neg25_integral_bounds :
    (-5399291 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-10505227 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch055Lower hpThetaJensenCellsBatch055Upper
    hpThetaShiftThreeBatch055Neg25WeightLower hpThetaShiftThreeBatch055Neg25WeightUpper hpThetaJensenCellsBatch055_bounds hpThetaShiftThreeBatch055Neg25_weight_bounds
  have hl : (-5399291 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch055Lower j * hpThetaShiftThreeBatch055Neg25WeightLower j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftThreeBatch055Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftThreeBatch055Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch055Lower j * hpThetaShiftThreeBatch055Neg25WeightUpper j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftThreeBatch055Neg25WeightUpper j) / 1600) ≤ (-10505227 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftThreeBatch055Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1100 : ℝ) / 1600 = 55 / 80 by norm_num,
    show ((1100 : ℝ) + 20) / 1600 = (55 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch055Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch055Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch055Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch055Neg25_integral_bounds
end HodgeProofHP
