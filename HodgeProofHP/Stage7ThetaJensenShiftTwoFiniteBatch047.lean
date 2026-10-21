/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch047

/-! Exact signed weight and batch integral certificates, batch 47 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch047Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1606469559 / 1000000000000 : ℝ)
  | 1 => (-1792533789 / 1000000000000 : ℝ)
  | 2 => (-4956243 / 2500000000 : ℝ)
  | 3 => (-2176413639 / 1000000000000 : ℝ)
  | 4 => (-2374337517 / 1000000000000 : ℝ)
  | 5 => (-2576323809 / 1000000000000 : ℝ)
  | 6 => (-2782428059 / 1000000000000 : ℝ)
  | 7 => (-2992706389 / 1000000000000 : ℝ)
  | 8 => (-400901937 / 125000000000 : ℝ)
  | 9 => (-685202533 / 200000000000 : ℝ)
  | 10 => (-456144471 / 125000000000 : ℝ)
  | 11 => (-3876703269 / 1000000000000 : ℝ)
  | 12 => (-4108714233 / 1000000000000 : ℝ)
  | 13 => (-4345248327 / 1000000000000 : ℝ)
  | 14 => (-183454633 / 40000000000 : ℝ)
  | 15 => (-4832127613 / 1000000000000 : ℝ)
  | 16 => (-2541297599 / 500000000000 : ℝ)
  | 17 => (-2668915353 / 500000000000 : ℝ)
  | 18 => (-1399474223 / 250000000000 : ℝ)
  | 19 => (-5862857143 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch047Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1424251217 / 1000000000000 : ℝ)
  | 1 => (-803234779 / 500000000000 : ℝ)
  | 2 => (-448133447 / 250000000000 : ℝ)
  | 3 => (-1982497199 / 1000000000000 : ℝ)
  | 4 => (-1088206819 / 500000000000 : ℝ)
  | 5 => (-593584379 / 250000000000 : ℝ)
  | 6 => (-80510119 / 31250000000 : ℝ)
  | 7 => (-1391214029 / 500000000000 : ℝ)
  | 8 => (-748176597 / 250000000000 : ℝ)
  | 9 => (-641443099 / 200000000000 : ℝ)
  | 10 => (-428251583 / 125000000000 : ℝ)
  | 11 => (-3649155767 / 1000000000000 : ℝ)
  | 12 => (-969175817 / 250000000000 : ℝ)
  | 13 => (-513589279 / 125000000000 : ℝ)
  | 14 => (-2172624163 / 500000000000 : ℝ)
  | 15 => (-35830983 / 7812500000 : ℝ)
  | 16 => (-1208031903 / 250000000000 : ℝ)
  | 17 => (-5082595197 / 1000000000000 : ℝ)
  | 18 => (-1067566141 / 200000000000 : ℝ)
  | 19 => (-5597896891 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch047Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((940 : ℝ) + (j.val : ℝ)) / 1600)
      (((940 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch047Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch047Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((940 : ℝ) + (j.val : ℝ)) / 1600)
    (((940 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch047Neg100WeightLower j.val) (hpThetaShiftTwoBatch047Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch047Neg100WeightLower, hpThetaShiftTwoBatch047Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch047Neg100_integral_bounds :
    (-1467215679 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-1350432409 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (940 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch047Lower hpThetaJensenCellsBatch047Upper
    hpThetaShiftTwoBatch047Neg100WeightLower hpThetaShiftTwoBatch047Neg100WeightUpper hpThetaJensenCellsBatch047_bounds hpThetaShiftTwoBatch047Neg100_weight_bounds
  have hl : (-1467215679 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch047Lower j * hpThetaShiftTwoBatch047Neg100WeightLower j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftTwoBatch047Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftTwoBatch047Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch047Lower j * hpThetaShiftTwoBatch047Neg100WeightUpper j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftTwoBatch047Neg100WeightUpper j) / 1600) ≤ (-1350432409 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftTwoBatch047Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (940 : ℝ) / 1600 = 47 / 80 by norm_num,
    show ((940 : ℝ) + 20) / 1600 = (47 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch047Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (142489759 / 25000000000 : ℝ)
  | 1 => (5753425899 / 1000000000000 : ℝ)
  | 2 => (145184449 / 25000000000 : ℝ)
  | 3 => (5861441797 / 1000000000000 : ℝ)
  | 4 => (236624503 / 40000000000 : ℝ)
  | 5 => (5969885367 / 1000000000000 : ℝ)
  | 6 => (6024255157 / 1000000000000 : ℝ)
  | 7 => (6078716837 / 1000000000000 : ℝ)
  | 8 => (1226653041 / 200000000000 : ℝ)
  | 9 => (1237578993 / 200000000000 : ℝ)
  | 10 => (780325091 / 125000000000 : ℝ)
  | 11 => (6297377007 / 1000000000000 : ℝ)
  | 12 => (317610911 / 50000000000 : ℝ)
  | 13 => (3203559343 / 500000000000 : ℝ)
  | 14 => (51696581 / 8000000000 : ℝ)
  | 15 => (6517074159 / 1000000000000 : ℝ)
  | 16 => (6572117307 / 1000000000000 : ℝ)
  | 17 => (1656798997 / 250000000000 : ℝ)
  | 18 => (417644001 / 62500000000 : ℝ)
  | 19 => (6737435103 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch047Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (57534259 / 10000000000 : ℝ)
  | 1 => (5807377961 / 1000000000000 : ℝ)
  | 2 => (2930720899 / 500000000000 : ℝ)
  | 3 => (184862893 / 31250000000 : ℝ)
  | 4 => (746235671 / 125000000000 : ℝ)
  | 5 => (3012127579 / 500000000000 : ℝ)
  | 6 => (3039358419 / 500000000000 : ℝ)
  | 7 => (3066632603 / 500000000000 : ℝ)
  | 8 => (3093947483 / 500000000000 : ℝ)
  | 9 => (6242600729 / 1000000000000 : ℝ)
  | 10 => (393586063 / 62500000000 : ℝ)
  | 11 => (6352218221 / 1000000000000 : ℝ)
  | 12 => (6407118687 / 1000000000000 : ℝ)
  | 13 => (3231036313 / 500000000000 : ℝ)
  | 14 => (81463427 / 12500000000 : ℝ)
  | 15 => (1643029327 / 250000000000 : ℝ)
  | 16 => (6627195989 / 1000000000000 : ℝ)
  | 17 => (6682304017 / 1000000000000 : ℝ)
  | 18 => (210544847 / 31250000000 : ℝ)
  | 19 => (3396291429 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch047Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((940 : ℝ) + (j.val : ℝ)) / 1600)
      (((940 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch047Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch047Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((940 : ℝ) + (j.val : ℝ)) / 1600)
    (((940 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch047Neg65WeightLower j.val) (hpThetaShiftTwoBatch047Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch047Neg65WeightLower, hpThetaShiftTwoBatch047Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch047Neg65_integral_bounds :
    (2524252159 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (2594138603 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (940 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch047Lower hpThetaJensenCellsBatch047Upper
    hpThetaShiftTwoBatch047Neg65WeightLower hpThetaShiftTwoBatch047Neg65WeightUpper hpThetaJensenCellsBatch047_bounds hpThetaShiftTwoBatch047Neg65_weight_bounds
  have hl : (2524252159 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch047Lower j * hpThetaShiftTwoBatch047Neg65WeightLower j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftTwoBatch047Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftTwoBatch047Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch047Lower j * hpThetaShiftTwoBatch047Neg65WeightUpper j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftTwoBatch047Neg65WeightUpper j) / 1600) ≤ (2594138603 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftTwoBatch047Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (940 : ℝ) / 1600 = 47 / 80 by norm_num,
    show ((940 : ℝ) + 20) / 1600 = (47 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch047Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (57075449 / 250000000000 : ℝ)
  | 1 => (255172469 / 1000000000000 : ℝ)
  | 2 => (8823687 / 31250000000 : ℝ)
  | 3 => (309859903 / 1000000000000 : ℝ)
  | 4 => (168839889 / 500000000000 : ℝ)
  | 5 => (73163831 / 200000000000 : ℝ)
  | 6 => (15771183 / 40000000000 : ℝ)
  | 7 => (105765643 / 250000000000 : ℝ)
  | 8 => (452169671 / 1000000000000 : ℝ)
  | 9 => (481602393 / 1000000000000 : ℝ)
  | 10 => (511362247 / 1000000000000 : ℝ)
  | 11 => (541450739 / 1000000000000 : ℝ)
  | 12 => (114373873 / 200000000000 : ℝ)
  | 13 => (602619613 / 1000000000000 : ℝ)
  | 14 => (633702963 / 1000000000000 : ℝ)
  | 15 => (332560443 / 500000000000 : ℝ)
  | 16 => (348437423 / 500000000000 : ℝ)
  | 17 => (728966297 / 1000000000000 : ℝ)
  | 18 => (190349171 / 250000000000 : ℝ)
  | 19 => (794167443 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch047Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (25517247 / 100000000000 : ℝ)
  | 1 => (56471597 / 200000000000 : ℝ)
  | 2 => (4841561 / 15625000000 : ℝ)
  | 3 => (337679779 / 1000000000000 : ℝ)
  | 4 => (91454789 / 250000000000 : ℝ)
  | 5 => (49284947 / 125000000000 : ℝ)
  | 6 => (423062573 / 1000000000000 : ℝ)
  | 7 => (56521209 / 125000000000 : ℝ)
  | 8 => (240801197 / 500000000000 : ℝ)
  | 9 => (63920281 / 125000000000 : ℝ)
  | 10 => (27072537 / 50000000000 : ℝ)
  | 11 => (285934683 / 500000000000 : ℝ)
  | 12 => (301309807 / 500000000000 : ℝ)
  | 13 => (158425741 / 250000000000 : ℝ)
  | 14 => (665120887 / 1000000000000 : ℝ)
  | 15 => (696874847 / 1000000000000 : ℝ)
  | 16 => (364483149 / 500000000000 : ℝ)
  | 17 => (152279337 / 200000000000 : ℝ)
  | 18 => (198541861 / 250000000000 : ℝ)
  | 19 => (10341 / 12500000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch047Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((940 : ℝ) + (j.val : ℝ)) / 1600)
      (((940 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch047Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch047Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((940 : ℝ) + (j.val : ℝ)) / 1600)
    (((940 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch047Neg45WeightLower j.val) (hpThetaShiftTwoBatch047Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch047Neg45WeightLower, hpThetaShiftTwoBatch047Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch047Neg45_integral_bounds :
    (25052233 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (108276297 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (940 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch047Lower hpThetaJensenCellsBatch047Upper
    hpThetaShiftTwoBatch047Neg45WeightLower hpThetaShiftTwoBatch047Neg45WeightUpper hpThetaJensenCellsBatch047_bounds hpThetaShiftTwoBatch047Neg45_weight_bounds
  have hl : (25052233 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch047Lower j * hpThetaShiftTwoBatch047Neg45WeightLower j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftTwoBatch047Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftTwoBatch047Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch047Lower j * hpThetaShiftTwoBatch047Neg45WeightUpper j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftTwoBatch047Neg45WeightUpper j) / 1600) ≤ (108276297 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftTwoBatch047Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (940 : ℝ) / 1600 = 47 / 80 by norm_num,
    show ((940 : ℝ) + 20) / 1600 = (47 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch047Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2476977137 / 1000000000000 : ℝ)
  | 1 => (-2490876959 / 1000000000000 : ℝ)
  | 2 => (-2504766841 / 1000000000000 : ℝ)
  | 3 => (-2518645979 / 1000000000000 : ℝ)
  | 4 => (-1266256783 / 500000000000 : ℝ)
  | 5 => (-159148049 / 62500000000 : ℝ)
  | 6 => (-640052703 / 250000000000 : ℝ)
  | 7 => (-1287019411 / 500000000000 : ℝ)
  | 8 => (-129392599 / 50000000000 : ℝ)
  | 9 => (-650412361 / 250000000000 : ℝ)
  | 10 => (-81732199 / 31250000000 : ℝ)
  | 11 => (-2629193897 / 1000000000000 : ℝ)
  | 12 => (-2642939173 / 1000000000000 : ℝ)
  | 13 => (-2656665329 / 1000000000000 : ℝ)
  | 14 => (-667592873 / 250000000000 : ℝ)
  | 15 => (-167753549 / 62500000000 : ℝ)
  | 16 => (-2697720319 / 1000000000000 : ℝ)
  | 17 => (-677840301 / 250000000000 : ℝ)
  | 18 => (-2724978543 / 1000000000000 : ℝ)
  | 19 => (-2738571429 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch047Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2463068171 / 1000000000000 : ℝ)
  | 1 => (-154811071 / 62500000000 : ℝ)
  | 2 => (-1245438479 / 500000000000 : ℝ)
  | 3 => (-62619171 / 25000000000 : ℝ)
  | 4 => (-1259322989 / 500000000000 : ℝ)
  | 5 => (-506502713 / 200000000000 : ℝ)
  | 6 => (-2546368783 / 1000000000000 : ℝ)
  | 7 => (-2560210811 / 1000000000000 : ℝ)
  | 8 => (-2574038821 / 1000000000000 : ℝ)
  | 9 => (-2587851979 / 1000000000000 : ℝ)
  | 10 => (-2601649443 / 1000000000000 : ℝ)
  | 11 => (-2615430367 / 1000000000000 : ℝ)
  | 12 => (-328649237 / 125000000000 : ℝ)
  | 13 => (-660734793 / 250000000000 : ℝ)
  | 14 => (-166041583 / 62500000000 : ℝ)
  | 15 => (-2670371491 / 1000000000000 : ℝ)
  | 16 => (-2684056783 / 1000000000000 : ℝ)
  | 17 => (-1348860159 / 500000000000 : ℝ)
  | 18 => (-2711361203 / 1000000000000 : ℝ)
  | 19 => (-1362489271 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch047Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((940 : ℝ) + (j.val : ℝ)) / 1600)
      (((940 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch047Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch047Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((940 : ℝ) + (j.val : ℝ)) / 1600)
    (((940 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch047Neg25WeightLower j.val) (hpThetaShiftTwoBatch047Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch047Neg25WeightLower, hpThetaShiftTwoBatch047Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch047Neg25_integral_bounds :
    (-540083163 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-1054719381 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (940 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch047Lower hpThetaJensenCellsBatch047Upper
    hpThetaShiftTwoBatch047Neg25WeightLower hpThetaShiftTwoBatch047Neg25WeightUpper hpThetaJensenCellsBatch047_bounds hpThetaShiftTwoBatch047Neg25_weight_bounds
  have hl : (-540083163 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch047Lower j * hpThetaShiftTwoBatch047Neg25WeightLower j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftTwoBatch047Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftTwoBatch047Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch047Lower j * hpThetaShiftTwoBatch047Neg25WeightUpper j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftTwoBatch047Neg25WeightUpper j) / 1600) ≤ (-1054719381 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftTwoBatch047Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (940 : ℝ) / 1600 = 47 / 80 by norm_num,
    show ((940 : ℝ) + 20) / 1600 = (47 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch047Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch047Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch047Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch047Neg25_integral_bounds
end HodgeProofHP
