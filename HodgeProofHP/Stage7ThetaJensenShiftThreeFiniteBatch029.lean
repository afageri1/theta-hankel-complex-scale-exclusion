/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch029

/-! Exact signed weight and batch integral certificates, batch 29 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch029Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-808263 / 250000000000 : ℝ)
  | 1 => (-6523 / 2000000000 : ℝ)
  | 2 => (-164487 / 50000000000 : ℝ)
  | 3 => (-1658881 / 500000000000 : ℝ)
  | 4 => (-209097 / 62500000000 : ℝ)
  | 5 => (-3373099 / 1000000000000 : ℝ)
  | 6 => (-425049 / 125000000000 : ℝ)
  | 7 => (-3427417 / 1000000000000 : ℝ)
  | 8 => (-3454163 / 1000000000000 : ℝ)
  | 9 => (-435077 / 125000000000 : ℝ)
  | 10 => (-876691 / 250000000000 : ℝ)
  | 11 => (-1766297 / 500000000000 : ℝ)
  | 12 => (-889523 / 250000000000 : ℝ)
  | 13 => (-1791623 / 500000000000 : ℝ)
  | 14 => (-90201 / 25000000000 : ℝ)
  | 15 => (-1816231 / 500000000000 : ℝ)
  | 16 => (-3656497 / 1000000000000 : ℝ)
  | 17 => (-920033 / 250000000000 : ℝ)
  | 18 => (-74067 / 20000000000 : ℝ)
  | 19 => (-1863069 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch029Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1602203 / 500000000000 : ℝ)
  | 1 => (-3233051 / 1000000000000 : ℝ)
  | 2 => (-3261499 / 1000000000000 : ℝ)
  | 3 => (-3289739 / 1000000000000 : ℝ)
  | 4 => (-3317761 / 1000000000000 : ℝ)
  | 5 => (-3345551 / 1000000000000 : ℝ)
  | 6 => (-1686549 / 500000000000 : ℝ)
  | 7 => (-3400391 / 1000000000000 : ℝ)
  | 8 => (-428427 / 125000000000 : ℝ)
  | 9 => (-1727081 / 500000000000 : ℝ)
  | 10 => (-696123 / 200000000000 : ℝ)
  | 11 => (-3506763 / 1000000000000 : ℝ)
  | 12 => (-3532593 / 1000000000000 : ℝ)
  | 13 => (-3558091 / 1000000000000 : ℝ)
  | 14 => (-716649 / 200000000000 : ℝ)
  | 15 => (-3608039 / 1000000000000 : ℝ)
  | 16 => (-3632461 / 1000000000000 : ℝ)
  | 17 => (-228531 / 62500000000 : ℝ)
  | 18 => (-3680131 / 1000000000000 : ℝ)
  | 19 => (-3703349 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch029Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((580 : ℝ) + (j.val : ℝ)) / 1600)
      (((580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch029Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch029Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((580 : ℝ) + (j.val : ℝ)) / 1600)
    (((580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch029Neg100WeightLower j.val) (hpThetaShiftThreeBatch029Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch029Neg100WeightLower, hpThetaShiftThreeBatch029Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch029Neg100_integral_bounds :
    (-9877563 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-19333821 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch029Lower hpThetaJensenCellsBatch029Upper
    hpThetaShiftThreeBatch029Neg100WeightLower hpThetaShiftThreeBatch029Neg100WeightUpper hpThetaJensenCellsBatch029_bounds hpThetaShiftThreeBatch029Neg100_weight_bounds
  have hl : (-9877563 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch029Lower j * hpThetaShiftThreeBatch029Neg100WeightLower j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftThreeBatch029Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftThreeBatch029Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch029Lower j * hpThetaShiftThreeBatch029Neg100WeightUpper j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftThreeBatch029Neg100WeightUpper j) / 1600) ≤ (-19333821 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftThreeBatch029Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (580 : ℝ) / 1600 = 29 / 80 by norm_num,
    show ((580 : ℝ) + 20) / 1600 = (29 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch029Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1007789 / 500000000000 : ℝ)
  | 1 => (-515321 / 250000000000 : ℝ)
  | 2 => (-1053727 / 500000000000 : ℝ)
  | 3 => (-2154089 / 1000000000000 : ℝ)
  | 4 => (-2201189 / 1000000000000 : ℝ)
  | 5 => (-140547 / 62500000000 : ℝ)
  | 6 => (-114839 / 50000000000 : ℝ)
  | 7 => (-2345271 / 1000000000000 : ℝ)
  | 8 => (-1197113 / 500000000000 : ℝ)
  | 9 => (-610911 / 250000000000 : ℝ)
  | 10 => (-623381 / 250000000000 : ℝ)
  | 11 => (-1271933 / 500000000000 : ℝ)
  | 12 => (-648667 / 250000000000 : ℝ)
  | 13 => (-2645931 / 1000000000000 : ℝ)
  | 14 => (-2697653 / 1000000000000 : ℝ)
  | 15 => (-1374917 / 500000000000 : ℝ)
  | 16 => (-2802471 / 1000000000000 : ℝ)
  | 17 => (-713891 / 250000000000 : ℝ)
  | 18 => (-363639 / 125000000000 : ℝ)
  | 19 => (-2963113 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch029Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-394067 / 200000000000 : ℝ)
  | 1 => (-2015577 / 1000000000000 : ℝ)
  | 2 => (-2061283 / 1000000000000 : ℝ)
  | 3 => (-2107453 / 1000000000000 : ℝ)
  | 4 => (-269261 / 125000000000 : ℝ)
  | 5 => (-550297 / 250000000000 : ℝ)
  | 6 => (-2248751 / 1000000000000 : ℝ)
  | 7 => (-2296779 / 1000000000000 : ℝ)
  | 8 => (-234527 / 100000000000 : ℝ)
  | 9 => (-95769 / 40000000000 : ℝ)
  | 10 => (-2443643 / 1000000000000 : ℝ)
  | 11 => (-2493523 / 1000000000000 : ℝ)
  | 12 => (-508773 / 200000000000 : ℝ)
  | 13 => (-2594667 / 1000000000000 : ℝ)
  | 14 => (-264593 / 100000000000 : ℝ)
  | 15 => (-674413 / 250000000000 : ℝ)
  | 16 => (-2749833 / 1000000000000 : ℝ)
  | 17 => (-280247 / 100000000000 : ℝ)
  | 18 => (-2855563 / 1000000000000 : ℝ)
  | 19 => (-2909111 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch029Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((580 : ℝ) + (j.val : ℝ)) / 1600)
      (((580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch029Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch029Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((580 : ℝ) + (j.val : ℝ)) / 1600)
    (((580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch029Neg70WeightLower j.val) (hpThetaShiftThreeBatch029Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch029Neg70WeightLower, hpThetaShiftThreeBatch029Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch029Neg70_integral_bounds :
    (-54659 / 3906250000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-3380161 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch029Lower hpThetaJensenCellsBatch029Upper
    hpThetaShiftThreeBatch029Neg70WeightLower hpThetaShiftThreeBatch029Neg70WeightUpper hpThetaJensenCellsBatch029_bounds hpThetaShiftThreeBatch029Neg70_weight_bounds
  have hl : (-54659 / 3906250000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch029Lower j * hpThetaShiftThreeBatch029Neg70WeightLower j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftThreeBatch029Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftThreeBatch029Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch029Lower j * hpThetaShiftThreeBatch029Neg70WeightUpper j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftThreeBatch029Neg70WeightUpper j) / 1600) ≤ (-3380161 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftThreeBatch029Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (580 : ℝ) / 1600 = 29 / 80 by norm_num,
    show ((580 : ℝ) + 20) / 1600 = (29 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch029Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1050437 / 500000000000 : ℝ)
  | 1 => (521601 / 250000000000 : ℝ)
  | 2 => (41429 / 20000000000 : ℝ)
  | 3 => (2056007 / 1000000000000 : ℝ)
  | 4 => (2040069 / 1000000000000 : ℝ)
  | 5 => (2023631 / 1000000000000 : ℝ)
  | 6 => (2006687 / 1000000000000 : ℝ)
  | 7 => (124327 / 62500000000 : ℝ)
  | 8 => (1971261 / 1000000000000 : ℝ)
  | 9 => (1952767 / 1000000000000 : ℝ)
  | 10 => (966873 / 500000000000 : ℝ)
  | 11 => (1914191 / 1000000000000 : ℝ)
  | 12 => (947049 / 500000000000 : ℝ)
  | 13 => (1873461 / 1000000000000 : ℝ)
  | 14 => (926137 / 500000000000 : ℝ)
  | 15 => (1830531 / 1000000000000 : ℝ)
  | 16 => (1808227 / 1000000000000 : ℝ)
  | 17 => (1785357 / 1000000000000 : ℝ)
  | 18 => (880957 / 500000000000 : ℝ)
  | 19 => (868947 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch029Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1057433 / 500000000000 : ℝ)
  | 1 => (16807 / 8000000000 : ℝ)
  | 2 => (417281 / 200000000000 : ℝ)
  | 3 => (2071451 / 1000000000000 : ℝ)
  | 4 => (257001 / 125000000000 : ℝ)
  | 5 => (204007 / 100000000000 : ℝ)
  | 6 => (126477 / 62500000000 : ℝ)
  | 7 => (62709 / 31250000000 : ℝ)
  | 8 => (1989233 / 1000000000000 : ℝ)
  | 9 => (985631 / 500000000000 : ℝ)
  | 10 => (1907 / 976562500 : ℝ)
  | 11 => (1933747 / 1000000000000 : ℝ)
  | 12 => (119637 / 62500000000 : ℝ)
  | 13 => (1894099 / 1000000000000 : ℝ)
  | 14 => (936731 / 500000000000 : ℝ)
  | 15 => (74091 / 40000000000 : ℝ)
  | 16 => (457633 / 250000000000 : ℝ)
  | 17 => (452057 / 250000000000 : ℝ)
  | 18 => (892679 / 500000000000 : ℝ)
  | 19 => (352383 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch029Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((580 : ℝ) + (j.val : ℝ)) / 1600)
      (((580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch029Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch029Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((580 : ℝ) + (j.val : ℝ)) / 1600)
    (((580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch029Neg45WeightLower j.val) (hpThetaShiftThreeBatch029Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch029Neg45WeightLower, hpThetaShiftThreeBatch029Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch029Neg45_integral_bounds :
    (10833603 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (2773237 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch029Lower hpThetaJensenCellsBatch029Upper
    hpThetaShiftThreeBatch029Neg45WeightLower hpThetaShiftThreeBatch029Neg45WeightUpper hpThetaJensenCellsBatch029_bounds hpThetaShiftThreeBatch029Neg45_weight_bounds
  have hl : (10833603 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch029Lower j * hpThetaShiftThreeBatch029Neg45WeightLower j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftThreeBatch029Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftThreeBatch029Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch029Lower j * hpThetaShiftThreeBatch029Neg45WeightUpper j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftThreeBatch029Neg45WeightUpper j) / 1600) ≤ (2773237 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftThreeBatch029Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (580 : ℝ) / 1600 = 29 / 80 by norm_num,
    show ((580 : ℝ) + 20) / 1600 = (29 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch029Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3953119 / 500000000000 : ℝ)
  | 1 => (3978833 / 500000000000 : ℝ)
  | 2 => (8009163 / 1000000000000 : ℝ)
  | 3 => (8060727 / 1000000000000 : ℝ)
  | 4 => (4056177 / 500000000000 : ℝ)
  | 5 => (8164041 / 1000000000000 : ℝ)
  | 6 => (1643157 / 200000000000 : ℝ)
  | 7 => (4133791 / 500000000000 : ℝ)
  | 8 => (8319429 / 1000000000000 : ℝ)
  | 9 => (4185661 / 500000000000 : ℝ)
  | 10 => (4211629 / 500000000000 : ℝ)
  | 11 => (4237617 / 500000000000 : ℝ)
  | 12 => (1705449 / 200000000000 : ℝ)
  | 13 => (1072411 / 125000000000 : ℝ)
  | 14 => (8631359 / 1000000000000 : ℝ)
  | 15 => (135679 / 15625000000 : ℝ)
  | 16 => (8735573 / 1000000000000 : ℝ)
  | 17 => (8787707 / 1000000000000 : ℝ)
  | 18 => (4419927 / 500000000000 : ℝ)
  | 19 => (8892011 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch029Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (7957667 / 1000000000000 : ℝ)
  | 1 => (2002291 / 250000000000 : ℝ)
  | 2 => (1007591 / 125000000000 : ℝ)
  | 3 => (1622471 / 200000000000 : ℝ)
  | 4 => (4082021 / 500000000000 : ℝ)
  | 5 => (4107893 / 500000000000 : ℝ)
  | 6 => (8267583 / 1000000000000 : ℝ)
  | 7 => (831943 / 100000000000 : ℝ)
  | 8 => (8371323 / 1000000000000 : ℝ)
  | 9 => (8423259 / 1000000000000 : ℝ)
  | 10 => (1695047 / 200000000000 : ℝ)
  | 11 => (4263623 / 500000000000 : ℝ)
  | 12 => (8579289 / 1000000000000 : ℝ)
  | 13 => (26973 / 3125000000 : ℝ)
  | 14 => (8683457 / 1000000000000 : ℝ)
  | 15 => (4367787 / 500000000000 : ℝ)
  | 16 => (2196927 / 250000000000 : ℝ)
  | 17 => (1767971 / 200000000000 : ℝ)
  | 18 => (2223003 / 250000000000 : ℝ)
  | 19 => (4472087 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch029Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((580 : ℝ) + (j.val : ℝ)) / 1600)
      (((580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch029Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch029Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((580 : ℝ) + (j.val : ℝ)) / 1600)
    (((580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch029Neg25WeightLower j.val) (hpThetaShiftThreeBatch029Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch029Neg25WeightLower, hpThetaShiftThreeBatch029Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch029Neg25_integral_bounds :
    (46904311 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (47861053 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch029Lower hpThetaJensenCellsBatch029Upper
    hpThetaShiftThreeBatch029Neg25WeightLower hpThetaShiftThreeBatch029Neg25WeightUpper hpThetaJensenCellsBatch029_bounds hpThetaShiftThreeBatch029Neg25_weight_bounds
  have hl : (46904311 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch029Lower j * hpThetaShiftThreeBatch029Neg25WeightLower j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftThreeBatch029Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftThreeBatch029Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch029Lower j * hpThetaShiftThreeBatch029Neg25WeightUpper j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftThreeBatch029Neg25WeightUpper j) / 1600) ≤ (47861053 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftThreeBatch029Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (580 : ℝ) / 1600 = 29 / 80 by norm_num,
    show ((580 : ℝ) + 20) / 1600 = (29 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch029Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch029Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch029Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch029Neg25_integral_bounds
end HodgeProofHP
