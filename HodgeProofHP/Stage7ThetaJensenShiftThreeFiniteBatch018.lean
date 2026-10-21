/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch018

/-! Exact signed weight and batch integral certificates, batch 18 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch018Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (26609 / 125000000000 : ℝ)
  | 1 => (333 / 1562500000 : ℝ)
  | 2 => (106657 / 500000000000 : ℝ)
  | 3 => (53363 / 250000000000 : ℝ)
  | 4 => (213533 / 1000000000000 : ℝ)
  | 5 => (106759 / 500000000000 : ℝ)
  | 6 => (213419 / 1000000000000 : ℝ)
  | 7 => (106629 / 500000000000 : ℝ)
  | 8 => (213033 / 1000000000000 : ℝ)
  | 9 => (212743 / 1000000000000 : ℝ)
  | 10 => (42477 / 200000000000 : ℝ)
  | 11 => (5299 / 25000000000 : ℝ)
  | 12 => (42293 / 200000000000 : ℝ)
  | 13 => (210899 / 1000000000000 : ℝ)
  | 14 => (10513 / 50000000000 : ℝ)
  | 15 => (209547 / 1000000000000 : ℝ)
  | 16 => (208759 / 1000000000000 : ℝ)
  | 17 => (103947 / 500000000000 : ℝ)
  | 18 => (4139 / 20000000000 : ℝ)
  | 19 => (102963 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch018Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (213121 / 1000000000000 : ℝ)
  | 1 => (42663 / 200000000000 : ℝ)
  | 2 => (213453 / 1000000000000 : ℝ)
  | 3 => (106767 / 500000000000 : ℝ)
  | 4 => (213557 / 1000000000000 : ℝ)
  | 5 => (213557 / 1000000000000 : ℝ)
  | 6 => (213519 / 1000000000000 : ℝ)
  | 7 => (10671 / 50000000000 : ℝ)
  | 8 => (213259 / 1000000000000 : ℝ)
  | 9 => (106517 / 500000000000 : ℝ)
  | 10 => (26593 / 125000000000 : ℝ)
  | 11 => (106193 / 500000000000 : ℝ)
  | 12 => (211961 / 1000000000000 : ℝ)
  | 13 => (105733 / 500000000000 : ℝ)
  | 14 => (2109 / 10000000000 : ℝ)
  | 15 => (210261 / 1000000000000 : ℝ)
  | 16 => (52387 / 250000000000 : ℝ)
  | 17 => (5219 / 25000000000 : ℝ)
  | 18 => (41579 / 200000000000 : ℝ)
  | 19 => (206951 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch018Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((360 : ℝ) + (j.val : ℝ)) / 1600)
      (((360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch018Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch018Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((360 : ℝ) + (j.val : ℝ)) / 1600)
    (((360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch018Neg100WeightLower j.val) (hpThetaShiftThreeBatch018Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch018Neg100WeightLower, hpThetaShiftThreeBatch018Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch018Neg100_integral_bounds :
    (700331 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (568257 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch018Lower hpThetaJensenCellsBatch018Upper
    hpThetaShiftThreeBatch018Neg100WeightLower hpThetaShiftThreeBatch018Neg100WeightUpper hpThetaJensenCellsBatch018_bounds hpThetaShiftThreeBatch018Neg100_weight_bounds
  have hl : (700331 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch018Lower j * hpThetaShiftThreeBatch018Neg100WeightLower j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftThreeBatch018Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftThreeBatch018Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch018Lower j * hpThetaShiftThreeBatch018Neg100WeightUpper j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftThreeBatch018Neg100WeightUpper j) / 1600) ≤ (568257 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftThreeBatch018Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (360 : ℝ) / 1600 = 18 / 80 by norm_num,
    show ((360 : ℝ) + 20) / 1600 = (18 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch018Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (413133 / 1000000000000 : ℝ)
  | 1 => (104277 / 250000000000 : ℝ)
  | 2 => (421081 / 1000000000000 : ℝ)
  | 3 => (425051 / 1000000000000 : ℝ)
  | 4 => (429017 / 1000000000000 : ℝ)
  | 5 => (432979 / 1000000000000 : ℝ)
  | 6 => (218467 / 500000000000 : ℝ)
  | 7 => (440883 / 1000000000000 : ℝ)
  | 8 => (17793 / 40000000000 : ℝ)
  | 9 => (224379 / 500000000000 : ℝ)
  | 10 => (452681 / 1000000000000 : ℝ)
  | 11 => (456593 / 1000000000000 : ℝ)
  | 12 => (460493 / 1000000000000 : ℝ)
  | 13 => (464381 / 1000000000000 : ℝ)
  | 14 => (234127 / 500000000000 : ℝ)
  | 15 => (472113 / 1000000000000 : ℝ)
  | 16 => (95191 / 200000000000 : ℝ)
  | 17 => (23989 / 50000000000 : ℝ)
  | 18 => (241793 / 500000000000 : ℝ)
  | 19 => (121843 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch018Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (417109 / 1000000000000 : ℝ)
  | 1 => (210541 / 500000000000 : ℝ)
  | 2 => (106263 / 250000000000 : ℝ)
  | 3 => (214509 / 500000000000 : ℝ)
  | 4 => (21649 / 50000000000 : ℝ)
  | 5 => (87387 / 200000000000 : ℝ)
  | 6 => (110221 / 250000000000 : ℝ)
  | 7 => (222413 / 500000000000 : ℝ)
  | 8 => (448759 / 1000000000000 : ℝ)
  | 9 => (226341 / 500000000000 : ℝ)
  | 10 => (228297 / 500000000000 : ℝ)
  | 11 => (230247 / 500000000000 : ℝ)
  | 12 => (232191 / 500000000000 : ℝ)
  | 13 => (93651 / 200000000000 : ℝ)
  | 14 => (236057 / 500000000000 : ℝ)
  | 15 => (118989 / 250000000000 : ℝ)
  | 16 => (479781 / 1000000000000 : ℝ)
  | 17 => (483587 / 1000000000000 : ℝ)
  | 18 => (487373 / 1000000000000 : ℝ)
  | 19 => (491139 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch018Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((360 : ℝ) + (j.val : ℝ)) / 1600)
      (((360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch018Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch018Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((360 : ℝ) + (j.val : ℝ)) / 1600)
    (((360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch018Neg70WeightLower j.val) (hpThetaShiftThreeBatch018Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch018Neg70WeightLower, hpThetaShiftThreeBatch018Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch018Neg70_integral_bounds :
    (149099 / 25000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (3044811 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch018Lower hpThetaJensenCellsBatch018Upper
    hpThetaShiftThreeBatch018Neg70WeightLower hpThetaShiftThreeBatch018Neg70WeightUpper hpThetaJensenCellsBatch018_bounds hpThetaShiftThreeBatch018Neg70_weight_bounds
  have hl : (149099 / 25000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch018Lower j * hpThetaShiftThreeBatch018Neg70WeightLower j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftThreeBatch018Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftThreeBatch018Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch018Lower j * hpThetaShiftThreeBatch018Neg70WeightUpper j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftThreeBatch018Neg70WeightUpper j) / 1600) ≤ (3044811 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftThreeBatch018Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (360 : ℝ) / 1600 = 18 / 80 by norm_num,
    show ((360 : ℝ) + 20) / 1600 = (18 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch018Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (617897 / 1000000000000 : ℝ)
  | 1 => (313 / 500000000 : ℝ)
  | 2 => (634169 / 1000000000000 : ℝ)
  | 3 => (160601 / 250000000000 : ℝ)
  | 4 => (130141 / 200000000000 : ℝ)
  | 5 => (5149 / 7812500000 : ℝ)
  | 6 => (133501 / 200000000000 : ℝ)
  | 7 => (169001 / 250000000000 : ℝ)
  | 8 => (85571 / 125000000000 : ℝ)
  | 9 => (346599 / 500000000000 : ℝ)
  | 10 => (701893 / 1000000000000 : ℝ)
  | 11 => (710653 / 1000000000000 : ℝ)
  | 12 => (719479 / 1000000000000 : ℝ)
  | 13 => (45523 / 62500000000 : ℝ)
  | 14 => (737323 / 1000000000000 : ℝ)
  | 15 => (373171 / 500000000000 : ℝ)
  | 16 => (23607 / 31250000000 : ℝ)
  | 17 => (764571 / 1000000000000 : ℝ)
  | 18 => (773781 / 1000000000000 : ℝ)
  | 19 => (156611 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch018Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (626001 / 1000000000000 : ℝ)
  | 1 => (63417 / 100000000000 : ℝ)
  | 2 => (128481 / 200000000000 : ℝ)
  | 3 => (325353 / 500000000000 : ℝ)
  | 4 => (659073 / 1000000000000 : ℝ)
  | 5 => (333753 / 500000000000 : ℝ)
  | 6 => (135201 / 200000000000 : ℝ)
  | 7 => (684569 / 1000000000000 : ℝ)
  | 8 => (693199 / 1000000000000 : ℝ)
  | 9 => (350947 / 500000000000 : ℝ)
  | 10 => (355327 / 500000000000 : ℝ)
  | 11 => (17987 / 25000000000 : ℝ)
  | 12 => (728369 / 1000000000000 : ℝ)
  | 13 => (184331 / 250000000000 : ℝ)
  | 14 => (746343 / 1000000000000 : ℝ)
  | 15 => (30217 / 40000000000 : ℝ)
  | 16 => (191143 / 250000000000 : ℝ)
  | 17 => (386891 / 500000000000 : ℝ)
  | 18 => (48941 / 62500000000 : ℝ)
  | 19 => (99049 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch018Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((360 : ℝ) + (j.val : ℝ)) / 1600)
      (((360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch018Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch018Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((360 : ℝ) + (j.val : ℝ)) / 1600)
    (((360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch018Neg45WeightLower j.val) (hpThetaShiftThreeBatch018Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch018Neg45WeightLower, hpThetaShiftThreeBatch018Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch018Neg45_integral_bounds :
    (9244367 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (2368743 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch018Lower hpThetaJensenCellsBatch018Upper
    hpThetaShiftThreeBatch018Neg45WeightLower hpThetaShiftThreeBatch018Neg45WeightUpper hpThetaJensenCellsBatch018_bounds hpThetaShiftThreeBatch018Neg45_weight_bounds
  have hl : (9244367 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch018Lower j * hpThetaShiftThreeBatch018Neg45WeightLower j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftThreeBatch018Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftThreeBatch018Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch018Lower j * hpThetaShiftThreeBatch018Neg45WeightUpper j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftThreeBatch018Neg45WeightUpper j) / 1600) ≤ (2368743 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftThreeBatch018Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (360 : ℝ) / 1600 = 18 / 80 by norm_num,
    show ((360 : ℝ) + 20) / 1600 = (18 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch018Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (808209 / 1000000000000 : ℝ)
  | 1 => (410171 / 500000000000 : ℝ)
  | 2 => (208153 / 250000000000 : ℝ)
  | 3 => (845023 / 1000000000000 : ℝ)
  | 4 => (428787 / 500000000000 : ℝ)
  | 5 => (435133 / 500000000000 : ℝ)
  | 6 => (883101 / 1000000000000 : ℝ)
  | 7 => (448039 / 500000000000 : ℝ)
  | 8 => (909201 / 1000000000000 : ℝ)
  | 9 => (230617 / 250000000000 : ℝ)
  | 10 => (467941 / 500000000000 : ℝ)
  | 11 => (949443 / 1000000000000 : ℝ)
  | 12 => (60197 / 62500000000 : ℝ)
  | 13 => (977011 / 1000000000000 : ℝ)
  | 14 => (991019 / 1000000000000 : ℝ)
  | 15 => (1005179 / 1000000000000 : ℝ)
  | 16 => (101949 / 100000000000 : ℝ)
  | 17 => (206791 / 200000000000 : ℝ)
  | 18 => (1048573 / 1000000000000 : ℝ)
  | 19 => (1063347 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch018Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (820343 / 1000000000000 : ℝ)
  | 1 => (832613 / 1000000000000 : ℝ)
  | 2 => (26407 / 31250000000 : ℝ)
  | 3 => (34303 / 40000000000 : ℝ)
  | 4 => (870267 / 1000000000000 : ℝ)
  | 5 => (441551 / 500000000000 : ℝ)
  | 6 => (896079 / 1000000000000 : ℝ)
  | 7 => (454601 / 500000000000 : ℝ)
  | 8 => (922469 / 1000000000000 : ℝ)
  | 9 => (935883 / 1000000000000 : ℝ)
  | 10 => (237361 / 250000000000 : ℝ)
  | 11 => (963153 / 1000000000000 : ℝ)
  | 12 => (244253 / 250000000000 : ℝ)
  | 13 => (49551 / 50000000000 : ℝ)
  | 14 => (50259 / 50000000000 : ℝ)
  | 15 => (1019491 / 1000000000000 : ℝ)
  | 16 => (258489 / 250000000000 : ℝ)
  | 17 => (524287 / 500000000000 : ℝ)
  | 18 => (265837 / 250000000000 : ℝ)
  | 19 => (1078277 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch018Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((360 : ℝ) + (j.val : ℝ)) / 1600)
      (((360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch018Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch018Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((360 : ℝ) + (j.val : ℝ)) / 1600)
    (((360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch018Neg25WeightLower j.val) (hpThetaShiftThreeBatch018Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch018Neg25WeightLower, hpThetaShiftThreeBatch018Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch018Neg25_integral_bounds :
    (3081211 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (6328657 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch018Lower hpThetaJensenCellsBatch018Upper
    hpThetaShiftThreeBatch018Neg25WeightLower hpThetaShiftThreeBatch018Neg25WeightUpper hpThetaJensenCellsBatch018_bounds hpThetaShiftThreeBatch018Neg25_weight_bounds
  have hl : (3081211 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch018Lower j * hpThetaShiftThreeBatch018Neg25WeightLower j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftThreeBatch018Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftThreeBatch018Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch018Lower j * hpThetaShiftThreeBatch018Neg25WeightUpper j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftThreeBatch018Neg25WeightUpper j) / 1600) ≤ (6328657 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftThreeBatch018Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (360 : ℝ) / 1600 = 18 / 80 by norm_num,
    show ((360 : ℝ) + 20) / 1600 = (18 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch018Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch018Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch018Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch018Neg25_integral_bounds
end HodgeProofHP
