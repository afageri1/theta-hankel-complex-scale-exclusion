/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch007

/-! Exact signed weight and batch integral certificates, batch 7 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch007Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3823347 / 1000000000000 : ℝ)
  | 1 => (783799 / 200000000000 : ℝ)
  | 2 => (4016089 / 1000000000000 : ℝ)
  | 3 => (4114629 / 1000000000000 : ℝ)
  | 4 => (4214613 / 1000000000000 : ℝ)
  | 5 => (2158021 / 500000000000 : ℝ)
  | 6 => (2209457 / 500000000000 : ℝ)
  | 7 => (1130807 / 250000000000 : ℝ)
  | 8 => (231449 / 50000000000 : ℝ)
  | 9 => (592021 / 125000000000 : ℝ)
  | 10 => (1211197 / 250000000000 : ℝ)
  | 11 => (4954837 / 1000000000000 : ℝ)
  | 12 => (506631 / 100000000000 : ℝ)
  | 13 => (5179201 / 1000000000000 : ℝ)
  | 14 => (1058701 / 200000000000 : ℝ)
  | 15 => (1081843 / 200000000000 : ℝ)
  | 16 => (221053 / 40000000000 : ℝ)
  | 17 => (2822413 / 500000000000 : ℝ)
  | 18 => (5764711 / 1000000000000 : ℝ)
  | 19 => (1471493 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch007Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (979749 / 250000000000 : ℝ)
  | 1 => (401609 / 100000000000 : ℝ)
  | 2 => (411463 / 100000000000 : ℝ)
  | 3 => (2107307 / 500000000000 : ℝ)
  | 4 => (4316043 / 1000000000000 : ℝ)
  | 5 => (883783 / 200000000000 : ℝ)
  | 6 => (4523229 / 1000000000000 : ℝ)
  | 7 => (4628981 / 1000000000000 : ℝ)
  | 8 => (4736169 / 1000000000000 : ℝ)
  | 9 => (4844789 / 1000000000000 : ℝ)
  | 10 => (2477419 / 500000000000 : ℝ)
  | 11 => (5066311 / 1000000000000 : ℝ)
  | 12 => (2589601 / 500000000000 : ℝ)
  | 13 => (2646753 / 500000000000 : ℝ)
  | 14 => (84519 / 15625000000 : ℝ)
  | 15 => (2763163 / 500000000000 : ℝ)
  | 16 => (5644827 / 1000000000000 : ℝ)
  | 17 => (720589 / 125000000000 : ℝ)
  | 18 => (5885973 / 1000000000000 : ℝ)
  | 19 => (3004299 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch007Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((140 : ℝ) + (j.val : ℝ)) / 1600)
      (((140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch007Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch007Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((140 : ℝ) + (j.val : ℝ)) / 1600)
    (((140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch007Neg100WeightLower j.val) (hpThetaShiftTwoBatch007Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch007Neg100WeightLower, hpThetaShiftTwoBatch007Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch007Neg100_integral_bounds :
    (98448087 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (101797337 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch007Lower hpThetaJensenCellsBatch007Upper
    hpThetaShiftTwoBatch007Neg100WeightLower hpThetaShiftTwoBatch007Neg100WeightUpper hpThetaJensenCellsBatch007_bounds hpThetaShiftTwoBatch007Neg100_weight_bounds
  have hl : (98448087 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch007Lower j * hpThetaShiftTwoBatch007Neg100WeightLower j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftTwoBatch007Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftTwoBatch007Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch007Lower j * hpThetaShiftTwoBatch007Neg100WeightUpper j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftTwoBatch007Neg100WeightUpper j) / 1600) ≤ (101797337 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftTwoBatch007Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (140 : ℝ) / 1600 = 7 / 80 by norm_num,
    show ((140 : ℝ) + 20) / 1600 = (7 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch007Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4181239 / 1000000000000 : ℝ)
  | 1 => (4291991 / 1000000000000 : ℝ)
  | 2 => (137647 / 31250000000 : ℝ)
  | 3 => (141231 / 31250000000 : ℝ)
  | 4 => (1159017 / 250000000000 : ℝ)
  | 5 => (950949 / 200000000000 : ℝ)
  | 6 => (1218859 / 250000000000 : ℝ)
  | 7 => (624769 / 125000000000 : ℝ)
  | 8 => (5122907 / 1000000000000 : ℝ)
  | 9 => (328107 / 62500000000 : ℝ)
  | 10 => (5378577 / 1000000000000 : ℝ)
  | 11 => (1101903 / 200000000000 : ℝ)
  | 12 => (705317 / 125000000000 : ℝ)
  | 13 => (5777651 / 1000000000000 : ℝ)
  | 14 => (5914869 / 1000000000000 : ℝ)
  | 15 => (30271 / 5000000000 : ℝ)
  | 16 => (3097827 / 500000000000 : ℝ)
  | 17 => (158481 / 25000000000 : ℝ)
  | 18 => (3242483 / 500000000000 : ℝ)
  | 19 => (165821 / 25000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch007Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (536499 / 125000000000 : ℝ)
  | 1 => (880941 / 200000000000 : ℝ)
  | 2 => (4519393 / 1000000000000 : ℝ)
  | 3 => (4636069 / 1000000000000 : ℝ)
  | 4 => (2377373 / 500000000000 : ℝ)
  | 5 => (4875437 / 1000000000000 : ℝ)
  | 6 => (4998153 / 1000000000000 : ℝ)
  | 7 => (1280727 / 250000000000 : ℝ)
  | 8 => (5249713 / 1000000000000 : ℝ)
  | 9 => (2689289 / 500000000000 : ℝ)
  | 10 => (1377379 / 250000000000 : ℝ)
  | 11 => (5642537 / 1000000000000 : ℝ)
  | 12 => (1444413 / 250000000000 : ℝ)
  | 13 => (591487 / 100000000000 : ℝ)
  | 14 => (6054201 / 1000000000000 : ℝ)
  | 15 => (1239131 / 200000000000 : ℝ)
  | 16 => (6339241 / 1000000000000 : ℝ)
  | 17 => (6484967 / 1000000000000 : ℝ)
  | 18 => (6632841 / 1000000000000 : ℝ)
  | 19 => (847859 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch007Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((140 : ℝ) + (j.val : ℝ)) / 1600)
      (((140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch007Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch007Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((140 : ℝ) + (j.val : ℝ)) / 1600)
    (((140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch007Neg65WeightLower j.val) (hpThetaShiftTwoBatch007Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch007Neg65WeightLower, hpThetaShiftTwoBatch007Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch007Neg65_integral_bounds :
    (21873197 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (113266391 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch007Lower hpThetaJensenCellsBatch007Upper
    hpThetaShiftTwoBatch007Neg65WeightLower hpThetaShiftTwoBatch007Neg65WeightUpper hpThetaJensenCellsBatch007_bounds hpThetaShiftTwoBatch007Neg65_weight_bounds
  have hl : (21873197 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch007Lower j * hpThetaShiftTwoBatch007Neg65WeightLower j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftTwoBatch007Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftTwoBatch007Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch007Lower j * hpThetaShiftTwoBatch007Neg65WeightUpper j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftTwoBatch007Neg65WeightUpper j) / 1600) ≤ (113266391 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftTwoBatch007Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (140 : ℝ) / 1600 = 7 / 80 by norm_num,
    show ((140 : ℝ) + 20) / 1600 = (7 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch007Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2196149 / 500000000000 : ℝ)
  | 1 => (4512061 / 1000000000000 : ℝ)
  | 2 => (4634099 / 1000000000000 : ℝ)
  | 3 => (951687 / 200000000000 : ℝ)
  | 4 => (4885089 / 1000000000000 : ℝ)
  | 5 => (1253521 / 250000000000 : ℝ)
  | 6 => (2572721 / 500000000000 : ℝ)
  | 7 => (5279183 / 1000000000000 : ℝ)
  | 8 => (5415329 / 1000000000000 : ℝ)
  | 9 => (5553901 / 1000000000000 : ℝ)
  | 10 => (142373 / 25000000000 : ℝ)
  | 11 => (5838407 / 1000000000000 : ℝ)
  | 12 => (5984383 / 1000000000000 : ℝ)
  | 13 => (6132867 / 1000000000000 : ℝ)
  | 14 => (6283881 / 1000000000000 : ℝ)
  | 15 => (1609361 / 250000000000 : ℝ)
  | 16 => (6593577 / 1000000000000 : ℝ)
  | 17 => (6752299 / 1000000000000 : ℝ)
  | 18 => (6913629 / 1000000000000 : ℝ)
  | 19 => (7077587 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch007Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2256031 / 500000000000 : ℝ)
  | 1 => (46341 / 10000000000 : ℝ)
  | 2 => (1189609 / 250000000000 : ℝ)
  | 3 => (488509 / 100000000000 : ℝ)
  | 4 => (1002817 / 200000000000 : ℝ)
  | 5 => (5145443 / 1000000000000 : ℝ)
  | 6 => (329949 / 62500000000 : ℝ)
  | 7 => (541533 / 100000000000 : ℝ)
  | 8 => (2776951 / 500000000000 : ℝ)
  | 9 => (5694921 / 1000000000000 : ℝ)
  | 10 => (729801 / 125000000000 : ℝ)
  | 11 => (46753 / 7812500000 : ℝ)
  | 12 => (1533217 / 250000000000 : ℝ)
  | 13 => (3141941 / 500000000000 : ℝ)
  | 14 => (1287489 / 200000000000 : ℝ)
  | 15 => (3296789 / 500000000000 : ℝ)
  | 16 => (67523 / 10000000000 : ℝ)
  | 17 => (691363 / 100000000000 : ℝ)
  | 18 => (1769397 / 250000000000 : ℝ)
  | 19 => (7244193 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch007Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((140 : ℝ) + (j.val : ℝ)) / 1600)
      (((140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch007Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch007Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((140 : ℝ) + (j.val : ℝ)) / 1600)
    (((140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch007Neg45WeightLower j.val) (hpThetaShiftTwoBatch007Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch007Neg45WeightLower, hpThetaShiftTwoBatch007Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch007Neg45_integral_bounds :
    (115839247 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (12006993 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch007Lower hpThetaJensenCellsBatch007Upper
    hpThetaShiftTwoBatch007Neg45WeightLower hpThetaShiftTwoBatch007Neg45WeightUpper hpThetaJensenCellsBatch007_bounds hpThetaShiftTwoBatch007Neg45_weight_bounds
  have hl : (115839247 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch007Lower j * hpThetaShiftTwoBatch007Neg45WeightLower j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftTwoBatch007Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftTwoBatch007Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch007Lower j * hpThetaShiftTwoBatch007Neg45WeightUpper j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftTwoBatch007Neg45WeightUpper j) / 1600) ≤ (12006993 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftTwoBatch007Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (140 : ℝ) / 1600 = 7 / 80 by norm_num,
    show ((140 : ℝ) + 20) / 1600 = (7 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch007Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4608171 / 1000000000000 : ℝ)
  | 1 => (2368613 / 500000000000 : ℝ)
  | 2 => (1217221 / 250000000000 : ℝ)
  | 3 => (5003177 / 1000000000000 : ℝ)
  | 4 => (1028027 / 200000000000 : ℝ)
  | 5 => (527979 / 100000000000 : ℝ)
  | 6 => (1355543 / 250000000000 : ℝ)
  | 7 => (347957 / 62500000000 : ℝ)
  | 8 => (5715243 / 1000000000000 : ℝ)
  | 9 => (1173199 / 200000000000 : ℝ)
  | 10 => (15049 / 2500000000 : ℝ)
  | 11 => (6176089 / 1000000000000 : ℝ)
  | 12 => (1583873 / 250000000000 : ℝ)
  | 13 => (6497843 / 1000000000000 : ℝ)
  | 14 => (1665793 / 250000000000 : ℝ)
  | 15 => (683151 / 100000000000 : ℝ)
  | 16 => (7002889 / 1000000000000 : ℝ)
  | 17 => (358867 / 50000000000 : ℝ)
  | 18 => (1470979 / 200000000000 : ℝ)
  | 19 => (1507117 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch007Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (4737227 / 1000000000000 : ℝ)
  | 1 => (973777 / 200000000000 : ℝ)
  | 2 => (2501589 / 500000000000 : ℝ)
  | 3 => (642517 / 125000000000 : ℝ)
  | 4 => (5279791 / 1000000000000 : ℝ)
  | 5 => (5422173 / 1000000000000 : ℝ)
  | 6 => (5567313 / 1000000000000 : ℝ)
  | 7 => (1428811 / 250000000000 : ℝ)
  | 8 => (1466499 / 250000000000 : ℝ)
  | 9 => (6019601 / 1000000000000 : ℝ)
  | 10 => (617609 / 100000000000 : ℝ)
  | 11 => (6335493 / 1000000000000 : ℝ)
  | 12 => (1624461 / 250000000000 : ℝ)
  | 13 => (6663173 / 1000000000000 : ℝ)
  | 14 => (6831511 / 1000000000000 : ℝ)
  | 15 => (700289 / 100000000000 : ℝ)
  | 16 => (7177341 / 1000000000000 : ℝ)
  | 17 => (459681 / 62500000000 : ℝ)
  | 18 => (3767793 / 500000000000 : ℝ)
  | 19 => (7719443 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch007Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((140 : ℝ) + (j.val : ℝ)) / 1600)
      (((140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch007Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch007Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((140 : ℝ) + (j.val : ℝ)) / 1600)
    (((140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch007Neg25WeightLower j.val) (hpThetaShiftTwoBatch007Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch007Neg25WeightLower, hpThetaShiftTwoBatch007Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch007Neg25_integral_bounds :
    (122485211 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (63528749 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch007Lower hpThetaJensenCellsBatch007Upper
    hpThetaShiftTwoBatch007Neg25WeightLower hpThetaShiftTwoBatch007Neg25WeightUpper hpThetaJensenCellsBatch007_bounds hpThetaShiftTwoBatch007Neg25_weight_bounds
  have hl : (122485211 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch007Lower j * hpThetaShiftTwoBatch007Neg25WeightLower j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftTwoBatch007Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftTwoBatch007Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch007Lower j * hpThetaShiftTwoBatch007Neg25WeightUpper j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftTwoBatch007Neg25WeightUpper j) / 1600) ≤ (63528749 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftTwoBatch007Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (140 : ℝ) / 1600 = 7 / 80 by norm_num,
    show ((140 : ℝ) + 20) / 1600 = (7 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch007Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch007Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch007Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch007Neg25_integral_bounds
end HodgeProofHP
