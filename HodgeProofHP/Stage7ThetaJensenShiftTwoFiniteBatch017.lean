/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch017

/-! Exact signed weight and batch integral certificates, batch 17 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch017Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (7264851 / 1000000000000 : ℝ)
  | 1 => (52731 / 7812500000 : ℝ)
  | 2 => (1244633 / 200000000000 : ℝ)
  | 3 => (88837 / 15625000000 : ℝ)
  | 4 => (2568351 / 500000000000 : ℝ)
  | 5 => (2288247 / 500000000000 : ℝ)
  | 6 => (4004873 / 1000000000000 : ℝ)
  | 7 => (3421769 / 1000000000000 : ℝ)
  | 8 => (2827113 / 1000000000000 : ℝ)
  | 9 => (555209 / 250000000000 : ℝ)
  | 10 => (801437 / 500000000000 : ℝ)
  | 11 => (973161 / 1000000000000 : ℝ)
  | 12 => (165817 / 500000000000 : ℝ)
  | 13 => (-321769 / 1000000000000 : ℝ)
  | 14 => (-246777 / 250000000000 : ℝ)
  | 15 => (-832221 / 500000000000 : ℝ)
  | 16 => (-2353827 / 1000000000000 : ℝ)
  | 17 => (-76383 / 25000000000 : ℝ)
  | 18 => (-3768973 / 1000000000000 : ℝ)
  | 19 => (-4494839 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch017Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (7769091 / 1000000000000 : ℝ)
  | 1 => (1816213 / 250000000000 : ℝ)
  | 2 => (6749569 / 1000000000000 : ℝ)
  | 3 => (3111583 / 500000000000 : ℝ)
  | 4 => (5685569 / 1000000000000 : ℝ)
  | 5 => (5136703 / 1000000000000 : ℝ)
  | 6 => (915299 / 200000000000 : ℝ)
  | 7 => (2002437 / 500000000000 : ℝ)
  | 8 => (342177 / 100000000000 : ℝ)
  | 9 => (1413557 / 500000000000 : ℝ)
  | 10 => (2220837 / 1000000000000 : ℝ)
  | 11 => (12823 / 8000000000 : ℝ)
  | 12 => (486581 / 500000000000 : ℝ)
  | 13 => (66327 / 200000000000 : ℝ)
  | 14 => (-40221 / 125000000000 : ℝ)
  | 15 => (-987107 / 1000000000000 : ℝ)
  | 16 => (-1664441 / 1000000000000 : ℝ)
  | 17 => (-1176913 / 500000000000 : ℝ)
  | 18 => (-3055319 / 1000000000000 : ℝ)
  | 19 => (-942243 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch017Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((340 : ℝ) + (j.val : ℝ)) / 1600)
      (((340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch017Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch017Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((340 : ℝ) + (j.val : ℝ)) / 1600)
    (((340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch017Neg100WeightLower j.val) (hpThetaShiftTwoBatch017Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch017Neg100WeightLower, hpThetaShiftTwoBatch017Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch017Neg100_integral_bounds :
    (24724093 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (8486767 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch017Lower hpThetaJensenCellsBatch017Upper
    hpThetaShiftTwoBatch017Neg100WeightLower hpThetaShiftTwoBatch017Neg100WeightUpper hpThetaJensenCellsBatch017_bounds hpThetaShiftTwoBatch017Neg100_weight_bounds
  have hl : (24724093 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch017Lower j * hpThetaShiftTwoBatch017Neg100WeightLower j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftTwoBatch017Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftTwoBatch017Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch017Lower j * hpThetaShiftTwoBatch017Neg100WeightUpper j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftTwoBatch017Neg100WeightUpper j) / 1600) ≤ (8486767 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftTwoBatch017Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (340 : ℝ) / 1600 = 17 / 80 by norm_num,
    show ((340 : ℝ) + 20) / 1600 = (17 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch017Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (6245317 / 125000000000 : ℝ)
  | 1 => (25002731 / 500000000000 : ℝ)
  | 2 => (1000819 / 20000000000 : ℝ)
  | 3 => (50068883 / 1000000000000 : ℝ)
  | 4 => (50089143 / 1000000000000 : ℝ)
  | 5 => (50101613 / 1000000000000 : ℝ)
  | 6 => (50102711 / 1000000000000 : ℝ)
  | 7 => (25045551 / 500000000000 : ℝ)
  | 8 => (50071229 / 1000000000000 : ℝ)
  | 9 => (50042973 / 1000000000000 : ℝ)
  | 10 => (25003107 / 500000000000 : ℝ)
  | 11 => (390319 / 7812500000 : ℝ)
  | 12 => (12476677 / 250000000000 : ℝ)
  | 13 => (49843719 / 1000000000000 : ℝ)
  | 14 => (49771747 / 1000000000000 : ℝ)
  | 15 => (49690669 / 1000000000000 : ℝ)
  | 16 => (9920073 / 200000000000 : ℝ)
  | 17 => (49500713 / 1000000000000 : ℝ)
  | 18 => (49391591 / 1000000000000 : ℝ)
  | 19 => (24636439 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch017Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (50005463 / 1000000000000 : ℝ)
  | 1 => (50040951 / 1000000000000 : ℝ)
  | 2 => (12517221 / 250000000000 : ℝ)
  | 3 => (6261143 / 125000000000 : ℝ)
  | 4 => (25050807 / 500000000000 : ℝ)
  | 5 => (782909 / 15625000000 : ℝ)
  | 6 => (50106233 / 1000000000000 : ℝ)
  | 7 => (6262839 / 125000000000 : ℝ)
  | 8 => (50091103 / 1000000000000 : ℝ)
  | 9 => (5007123 / 100000000000 : ℝ)
  | 10 => (25021487 / 500000000000 : ℝ)
  | 11 => (10001243 / 200000000000 : ℝ)
  | 12 => (49960833 / 1000000000000 : ℝ)
  | 13 => (49906709 / 1000000000000 : ℝ)
  | 14 => (1246093 / 25000000000 : ℝ)
  | 15 => (12442937 / 250000000000 : ℝ)
  | 16 => (4969067 / 100000000000 : ℝ)
  | 17 => (24800183 / 500000000000 : ℝ)
  | 18 => (24750357 / 500000000000 : ℝ)
  | 19 => (6173949 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch017Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((340 : ℝ) + (j.val : ℝ)) / 1600)
      (((340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch017Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch017Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((340 : ℝ) + (j.val : ℝ)) / 1600)
    (((340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch017Neg65WeightLower j.val) (hpThetaShiftTwoBatch017Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch017Neg65WeightLower, hpThetaShiftTwoBatch017Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch017Neg65_integral_bounds :
    (87362181 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (70808023 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch017Lower hpThetaJensenCellsBatch017Upper
    hpThetaShiftTwoBatch017Neg65WeightLower hpThetaShiftTwoBatch017Neg65WeightUpper hpThetaJensenCellsBatch017_bounds hpThetaShiftTwoBatch017Neg65_weight_bounds
  have hl : (87362181 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch017Lower j * hpThetaShiftTwoBatch017Neg65WeightLower j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftTwoBatch017Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftTwoBatch017Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch017Lower j * hpThetaShiftTwoBatch017Neg65WeightUpper j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftTwoBatch017Neg65WeightUpper j) / 1600) ≤ (70808023 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftTwoBatch017Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (340 : ℝ) / 1600 = 17 / 80 by norm_num,
    show ((340 : ℝ) + 20) / 1600 = (17 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch017Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (80806099 / 1000000000000 : ℝ)
  | 1 => (40656553 / 500000000000 : ℝ)
  | 2 => (81817619 / 1000000000000 : ℝ)
  | 3 => (82319541 / 1000000000000 : ℝ)
  | 4 => (3312751 / 40000000000 : ℝ)
  | 5 => (41657613 / 500000000000 : ℝ)
  | 6 => (41904397 / 500000000000 : ℝ)
  | 7 => (42149691 / 500000000000 : ℝ)
  | 8 => (84786889 / 1000000000000 : ℝ)
  | 9 => (17054243 / 200000000000 : ℝ)
  | 10 => (85752259 / 1000000000000 : ℝ)
  | 11 => (538937 / 6250000000 : ℝ)
  | 12 => (43352047 / 500000000000 : ℝ)
  | 13 => (43587339 / 500000000000 : ℝ)
  | 14 => (2738799 / 31250000000 : ℝ)
  | 15 => (44052329 / 500000000000 : ℝ)
  | 16 => (88563843 / 1000000000000 : ℝ)
  | 17 => (89019017 / 1000000000000 : ℝ)
  | 18 => (11183759 / 125000000000 : ℝ)
  | 19 => (899169 / 10000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch017Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (81313107 / 1000000000000 : ℝ)
  | 1 => (4090881 / 50000000000 : ℝ)
  | 2 => (41159771 / 500000000000 : ℝ)
  | 3 => (10352347 / 125000000000 : ℝ)
  | 4 => (83315227 / 1000000000000 : ℝ)
  | 5 => (16761759 / 200000000000 : ℝ)
  | 6 => (84299383 / 1000000000000 : ℝ)
  | 7 => (8478689 / 100000000000 : ℝ)
  | 8 => (5329451 / 62500000000 : ℝ)
  | 9 => (4287613 / 50000000000 : ℝ)
  | 10 => (86229921 / 1000000000000 : ℝ)
  | 11 => (17340819 / 200000000000 : ℝ)
  | 12 => (87174679 / 1000000000000 : ℝ)
  | 13 => (87641569 / 1000000000000 : ℝ)
  | 14 => (88104659 / 1000000000000 : ℝ)
  | 15 => (22140961 / 250000000000 : ℝ)
  | 16 => (44509509 / 500000000000 : ℝ)
  | 17 => (89470073 / 1000000000000 : ℝ)
  | 18 => (89916901 / 1000000000000 : ℝ)
  | 19 => (2823731 / 31250000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch017Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((340 : ℝ) + (j.val : ℝ)) / 1600)
      (((340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch017Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch017Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((340 : ℝ) + (j.val : ℝ)) / 1600)
    (((340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch017Neg45WeightLower j.val) (hpThetaShiftTwoBatch017Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch017Neg45WeightLower, hpThetaShiftTwoBatch017Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch017Neg45_integral_bounds :
    (1196790537 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (304530047 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch017Lower hpThetaJensenCellsBatch017Upper
    hpThetaShiftTwoBatch017Neg45WeightLower hpThetaShiftTwoBatch017Neg45WeightUpper hpThetaJensenCellsBatch017_bounds hpThetaShiftTwoBatch017Neg45_weight_bounds
  have hl : (1196790537 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch017Lower j * hpThetaShiftTwoBatch017Neg45WeightLower j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftTwoBatch017Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftTwoBatch017Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch017Lower j * hpThetaShiftTwoBatch017Neg45WeightUpper j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftTwoBatch017Neg45WeightUpper j) / 1600) ≤ (304530047 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftTwoBatch017Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (340 : ℝ) / 1600 = 17 / 80 by norm_num,
    show ((340 : ℝ) + 20) / 1600 = (17 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch017Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (116918933 / 1000000000000 : ℝ)
  | 1 => (23602249 / 200000000000 : ℝ)
  | 2 => (119108399 / 1000000000000 : ℝ)
  | 3 => (3005259 / 25000000000 : ℝ)
  | 4 => (30329273 / 250000000000 : ℝ)
  | 5 => (1530357 / 12500000000 : ℝ)
  | 6 => (4941789 / 40000000000 : ℝ)
  | 7 => (124665551 / 1000000000000 : ℝ)
  | 8 => (125790997 / 1000000000000 : ℝ)
  | 9 => (5076841 / 40000000000 : ℝ)
  | 10 => (32013899 / 250000000000 : ℝ)
  | 11 => (129194667 / 1000000000000 : ℝ)
  | 12 => (130338197 / 1000000000000 : ℝ)
  | 13 => (26297229 / 200000000000 : ℝ)
  | 14 => (132638467 / 1000000000000 : ℝ)
  | 15 => (133795119 / 1000000000000 : ℝ)
  | 16 => (134956057 / 1000000000000 : ℝ)
  | 17 => (34030309 / 250000000000 : ℝ)
  | 18 => (13729061 / 100000000000 : ℝ)
  | 19 => (34616033 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch017Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (59005623 / 500000000000 : ℝ)
  | 1 => (297771 / 2500000000 : ℝ)
  | 2 => (120210361 / 1000000000000 : ℝ)
  | 3 => (121317093 / 1000000000000 : ℝ)
  | 4 => (122428561 / 1000000000000 : ℝ)
  | 5 => (61772363 / 500000000000 : ℝ)
  | 6 => (7791597 / 62500000000 : ℝ)
  | 7 => (62895499 / 500000000000 : ℝ)
  | 8 => (63460513 / 500000000000 : ℝ)
  | 9 => (128055597 / 1000000000000 : ℝ)
  | 10 => (32298667 / 250000000000 : ℝ)
  | 11 => (65169099 / 500000000000 : ℝ)
  | 12 => (65743073 / 500000000000 : ℝ)
  | 13 => (33159617 / 250000000000 : ℝ)
  | 14 => (1672439 / 12500000000 : ℝ)
  | 15 => (67478029 / 500000000000 : ℝ)
  | 16 => (136121237 / 1000000000000 : ℝ)
  | 17 => (137290611 / 1000000000000 : ℝ)
  | 18 => (138464133 / 1000000000000 : ℝ)
  | 19 => (27928351 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch017Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((340 : ℝ) + (j.val : ℝ)) / 1600)
      (((340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch017Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch017Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((340 : ℝ) + (j.val : ℝ)) / 1600)
    (((340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch017Neg25WeightLower j.val) (hpThetaShiftTwoBatch017Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch017Neg25WeightLower, hpThetaShiftTwoBatch017Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch017Neg25_integral_bounds :
    (111621511 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (911883387 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch017Lower hpThetaJensenCellsBatch017Upper
    hpThetaShiftTwoBatch017Neg25WeightLower hpThetaShiftTwoBatch017Neg25WeightUpper hpThetaJensenCellsBatch017_bounds hpThetaShiftTwoBatch017Neg25_weight_bounds
  have hl : (111621511 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch017Lower j * hpThetaShiftTwoBatch017Neg25WeightLower j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftTwoBatch017Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftTwoBatch017Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch017Lower j * hpThetaShiftTwoBatch017Neg25WeightUpper j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftTwoBatch017Neg25WeightUpper j) / 1600) ≤ (911883387 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftTwoBatch017Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (340 : ℝ) / 1600 = 17 / 80 by norm_num,
    show ((340 : ℝ) + 20) / 1600 = (17 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch017Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch017Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch017Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch017Neg25_integral_bounds
end HodgeProofHP
