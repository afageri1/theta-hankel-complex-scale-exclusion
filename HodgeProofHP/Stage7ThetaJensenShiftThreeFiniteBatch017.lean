/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch017

/-! Exact signed weight and batch integral certificates, batch 17 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch017Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (99177 / 500000000000 : ℝ)
  | 1 => (199439 / 1000000000000 : ℝ)
  | 2 => (50123 / 250000000000 : ℝ)
  | 3 => (25189 / 125000000000 : ℝ)
  | 4 => (81 / 400000000 : ℝ)
  | 5 => (203453 / 1000000000000 : ℝ)
  | 6 => (204371 / 1000000000000 : ℝ)
  | 7 => (205253 / 1000000000000 : ℝ)
  | 8 => (206097 / 1000000000000 : ℝ)
  | 9 => (103451 / 500000000000 : ℝ)
  | 10 => (51917 / 250000000000 : ℝ)
  | 11 => (26049 / 125000000000 : ℝ)
  | 12 => (104537 / 500000000000 : ℝ)
  | 13 => (209713 / 1000000000000 : ℝ)
  | 14 => (52577 / 250000000000 : ℝ)
  | 15 => (210857 / 1000000000000 : ℝ)
  | 16 => (105679 / 500000000000 : ℝ)
  | 17 => (52953 / 250000000000 : ℝ)
  | 18 => (26527 / 125000000000 : ℝ)
  | 19 => (21257 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch017Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2493 / 12500000000 : ℝ)
  | 1 => (200493 / 1000000000000 : ℝ)
  | 2 => (201513 / 1000000000000 : ℝ)
  | 3 => (202501 / 1000000000000 : ℝ)
  | 4 => (101727 / 500000000000 : ℝ)
  | 5 => (51093 / 250000000000 : ℝ)
  | 6 => (102627 / 500000000000 : ℝ)
  | 7 => (103049 / 500000000000 : ℝ)
  | 8 => (206903 / 1000000000000 : ℝ)
  | 9 => (207669 / 1000000000000 : ℝ)
  | 10 => (208393 / 1000000000000 : ℝ)
  | 11 => (8363 / 40000000000 : ℝ)
  | 12 => (104857 / 500000000000 : ℝ)
  | 13 => (210309 / 1000000000000 : ℝ)
  | 14 => (105429 / 500000000000 : ℝ)
  | 15 => (211359 / 1000000000000 : ℝ)
  | 16 => (211813 / 1000000000000 : ℝ)
  | 17 => (212217 / 1000000000000 : ℝ)
  | 18 => (212571 / 1000000000000 : ℝ)
  | 19 => (212873 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch017Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((340 : ℝ) + (j.val : ℝ)) / 1600)
      (((340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch017Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch017Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((340 : ℝ) + (j.val : ℝ)) / 1600)
    (((340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch017Neg100WeightLower j.val) (hpThetaShiftThreeBatch017Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch017Neg100WeightLower, hpThetaShiftThreeBatch017Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch017Neg100_integral_bounds :
    (2894113 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (2939661 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch017Lower hpThetaJensenCellsBatch017Upper
    hpThetaShiftThreeBatch017Neg100WeightLower hpThetaShiftThreeBatch017Neg100WeightUpper hpThetaJensenCellsBatch017_bounds hpThetaShiftThreeBatch017Neg100_weight_bounds
  have hl : (2894113 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch017Lower j * hpThetaShiftThreeBatch017Neg100WeightLower j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftThreeBatch017Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftThreeBatch017Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch017Lower j * hpThetaShiftThreeBatch017Neg100WeightUpper j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftThreeBatch017Neg100WeightUpper j) / 1600) ≤ (2939661 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftThreeBatch017Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (340 : ℝ) / 1600 = 17 / 80 by norm_num,
    show ((340 : ℝ) + 20) / 1600 = (17 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch017Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (83619 / 250000000000 : ℝ)
  | 1 => (84581 / 250000000000 : ℝ)
  | 2 => (171093 / 500000000000 : ℝ)
  | 3 => (346059 / 1000000000000 : ℝ)
  | 4 => (69989 / 200000000000 : ℝ)
  | 5 => (353841 / 1000000000000 : ℝ)
  | 6 => (357747 / 1000000000000 : ℝ)
  | 7 => (5651 / 15625000000 : ℝ)
  | 8 => (365589 / 1000000000000 : ℝ)
  | 9 => (369523 / 1000000000000 : ℝ)
  | 10 => (46683 / 125000000000 : ℝ)
  | 11 => (94353 / 250000000000 : ℝ)
  | 12 => (381367 / 1000000000000 : ℝ)
  | 13 => (385327 / 1000000000000 : ℝ)
  | 14 => (389291 / 1000000000000 : ℝ)
  | 15 => (19663 / 50000000000 : ℝ)
  | 16 => (24827 / 62500000000 : ℝ)
  | 17 => (200603 / 500000000000 : ℝ)
  | 18 => (405181 / 1000000000000 : ℝ)
  | 19 => (409157 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch017Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (13533 / 40000000000 : ℝ)
  | 1 => (342187 / 1000000000000 : ℝ)
  | 2 => (17303 / 50000000000 : ℝ)
  | 3 => (174973 / 500000000000 : ℝ)
  | 4 => (176921 / 500000000000 : ℝ)
  | 5 => (89437 / 250000000000 : ℝ)
  | 6 => (72333 / 200000000000 : ℝ)
  | 7 => (36559 / 100000000000 : ℝ)
  | 8 => (92381 / 250000000000 : ℝ)
  | 9 => (74693 / 200000000000 : ℝ)
  | 10 => (377413 / 1000000000000 : ℝ)
  | 11 => (47671 / 125000000000 : ℝ)
  | 12 => (24083 / 62500000000 : ℝ)
  | 13 => (97323 / 250000000000 : ℝ)
  | 14 => (393261 / 1000000000000 : ℝ)
  | 15 => (397233 / 1000000000000 : ℝ)
  | 16 => (401207 / 1000000000000 : ℝ)
  | 17 => (202591 / 500000000000 : ℝ)
  | 18 => (204579 / 500000000000 : ℝ)
  | 19 => (206567 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch017Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((340 : ℝ) + (j.val : ℝ)) / 1600)
      (((340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch017Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch017Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((340 : ℝ) + (j.val : ℝ)) / 1600)
    (((340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch017Neg70WeightLower j.val) (hpThetaShiftThreeBatch017Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch017Neg70WeightLower, hpThetaShiftThreeBatch017Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch017Neg70_integral_bounds :
    (1040393 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (5321001 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch017Lower hpThetaJensenCellsBatch017Upper
    hpThetaShiftThreeBatch017Neg70WeightLower hpThetaShiftThreeBatch017Neg70WeightUpper hpThetaJensenCellsBatch017_bounds hpThetaShiftThreeBatch017Neg70_weight_bounds
  have hl : (1040393 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch017Lower j * hpThetaShiftThreeBatch017Neg70WeightLower j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftThreeBatch017Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftThreeBatch017Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch017Lower j * hpThetaShiftThreeBatch017Neg70WeightUpper j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftThreeBatch017Neg70WeightUpper j) / 1600) ≤ (5321001 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftThreeBatch017Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (340 : ℝ) / 1600 = 17 / 80 by norm_num,
    show ((340 : ℝ) + 20) / 1600 = (17 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch017Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (234877 / 500000000000 : ℝ)
  | 1 => (95307 / 200000000000 : ℝ)
  | 2 => (24169 / 50000000000 : ℝ)
  | 3 => (122573 / 250000000000 : ℝ)
  | 4 => (497269 / 1000000000000 : ℝ)
  | 5 => (63039 / 125000000000 : ℝ)
  | 6 => (25571 / 50000000000 : ℝ)
  | 7 => (103719 / 200000000000 : ℝ)
  | 8 => (131459 / 250000000000 : ℝ)
  | 9 => (533143 / 1000000000000 : ℝ)
  | 10 => (135129 / 250000000000 : ℝ)
  | 11 => (136989 / 250000000000 : ℝ)
  | 12 => (555461 / 1000000000000 : ℝ)
  | 13 => (281517 / 500000000000 : ℝ)
  | 14 => (35667 / 62500000000 : ℝ)
  | 15 => (578377 / 1000000000000 : ℝ)
  | 16 => (146537 / 250000000000 : ℝ)
  | 17 => (296993 / 500000000000 : ℝ)
  | 18 => (60189 / 100000000000 : ℝ)
  | 19 => (30493 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch017Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (59567 / 125000000000 : ℝ)
  | 1 => (483381 / 1000000000000 : ℝ)
  | 2 => (490293 / 1000000000000 : ℝ)
  | 3 => (49727 / 100000000000 : ℝ)
  | 4 => (504313 / 1000000000000 : ℝ)
  | 5 => (511421 / 1000000000000 : ℝ)
  | 6 => (129649 / 250000000000 : ℝ)
  | 7 => (525837 / 1000000000000 : ℝ)
  | 8 => (66643 / 125000000000 : ℝ)
  | 9 => (540517 / 1000000000000 : ℝ)
  | 10 => (547957 / 1000000000000 : ℝ)
  | 11 => (277731 / 500000000000 : ℝ)
  | 12 => (112607 / 200000000000 : ℝ)
  | 13 => (570673 / 1000000000000 : ℝ)
  | 14 => (289189 / 500000000000 : ℝ)
  | 15 => (586149 / 1000000000000 : ℝ)
  | 16 => (593987 / 1000000000000 : ℝ)
  | 17 => (601891 / 1000000000000 : ℝ)
  | 18 => (609861 / 1000000000000 : ℝ)
  | 19 => (308949 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch017Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((340 : ℝ) + (j.val : ℝ)) / 1600)
      (((340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch017Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch017Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((340 : ℝ) + (j.val : ℝ)) / 1600)
    (((340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch017Neg45WeightLower j.val) (hpThetaShiftThreeBatch017Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch017Neg45WeightLower, hpThetaShiftThreeBatch017Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch017Neg45_integral_bounds :
    (7527897 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (7724417 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch017Lower hpThetaJensenCellsBatch017Upper
    hpThetaShiftThreeBatch017Neg45WeightLower hpThetaShiftThreeBatch017Neg45WeightUpper hpThetaJensenCellsBatch017_bounds hpThetaShiftThreeBatch017Neg45_weight_bounds
  have hl : (7527897 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch017Lower j * hpThetaShiftThreeBatch017Neg45WeightLower j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftThreeBatch017Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftThreeBatch017Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch017Lower j * hpThetaShiftThreeBatch017Neg45WeightUpper j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftThreeBatch017Neg45WeightUpper j) / 1600) ≤ (7724417 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftThreeBatch017Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (340 : ℝ) / 1600 = 17 / 80 by norm_num,
    show ((340 : ℝ) + 20) / 1600 = (17 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch017Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (118627 / 200000000000 : ℝ)
  | 1 => (602703 / 1000000000000 : ℝ)
  | 2 => (61239 / 100000000000 : ℝ)
  | 3 => (622197 / 1000000000000 : ℝ)
  | 4 => (158031 / 250000000000 : ℝ)
  | 5 => (321087 / 500000000000 : ℝ)
  | 6 => (652347 / 1000000000000 : ℝ)
  | 7 => (662643 / 1000000000000 : ℝ)
  | 8 => (84133 / 125000000000 : ℝ)
  | 9 => (683611 / 1000000000000 : ℝ)
  | 10 => (138857 / 200000000000 : ℝ)
  | 11 => (705087 / 1000000000000 : ℝ)
  | 12 => (716017 / 1000000000000 : ℝ)
  | 13 => (727077 / 1000000000000 : ℝ)
  | 14 => (738267 / 1000000000000 : ℝ)
  | 15 => (749589 / 1000000000000 : ℝ)
  | 16 => (190261 / 250000000000 : ℝ)
  | 17 => (772633 / 1000000000000 : ℝ)
  | 18 => (196089 / 250000000000 : ℝ)
  | 19 => (398107 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch017Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (37669 / 62500000000 : ℝ)
  | 1 => (612391 / 1000000000000 : ℝ)
  | 2 => (311099 / 500000000000 : ℝ)
  | 3 => (5057 / 8000000000 : ℝ)
  | 4 => (25687 / 40000000000 : ℝ)
  | 5 => (163087 / 250000000000 : ℝ)
  | 6 => (165661 / 250000000000 : ℝ)
  | 7 => (134613 / 200000000000 : ℝ)
  | 8 => (170903 / 250000000000 : ℝ)
  | 9 => (347143 / 500000000000 : ℝ)
  | 10 => (11017 / 15625000000 : ℝ)
  | 11 => (358009 / 500000000000 : ℝ)
  | 12 => (363539 / 500000000000 : ℝ)
  | 13 => (184567 / 250000000000 : ℝ)
  | 14 => (74959 / 100000000000 : ℝ)
  | 15 => (152209 / 200000000000 : ℝ)
  | 16 => (386317 / 500000000000 : ℝ)
  | 17 => (784357 / 1000000000000 : ℝ)
  | 18 => (159243 / 200000000000 : ℝ)
  | 19 => (80821 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch017Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((340 : ℝ) + (j.val : ℝ)) / 1600)
      (((340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch017Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch017Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((340 : ℝ) + (j.val : ℝ)) / 1600)
    (((340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch017Neg25WeightLower j.val) (hpThetaShiftThreeBatch017Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch017Neg25WeightLower, hpThetaShiftThreeBatch017Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch017Neg25_integral_bounds :
    (4834637 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (496961 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch017Lower hpThetaJensenCellsBatch017Upper
    hpThetaShiftThreeBatch017Neg25WeightLower hpThetaShiftThreeBatch017Neg25WeightUpper hpThetaJensenCellsBatch017_bounds hpThetaShiftThreeBatch017Neg25_weight_bounds
  have hl : (4834637 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch017Lower j * hpThetaShiftThreeBatch017Neg25WeightLower j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftThreeBatch017Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftThreeBatch017Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch017Lower j * hpThetaShiftThreeBatch017Neg25WeightUpper j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftThreeBatch017Neg25WeightUpper j) / 1600) ≤ (496961 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftThreeBatch017Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (340 : ℝ) / 1600 = 17 / 80 by norm_num,
    show ((340 : ℝ) + 20) / 1600 = (17 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch017Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch017Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch017Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch017Neg25_integral_bounds
end HodgeProofHP
