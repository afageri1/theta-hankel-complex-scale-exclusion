/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch006

/-! Exact signed weight and batch integral certificates, batch 6 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch006Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2065383093 / 1000000000000 : ℝ)
  | 1 => (1043992743 / 500000000000 : ℝ)
  | 2 => (2110401681 / 1000000000000 : ℝ)
  | 3 => (1066311819 / 500000000000 : ℝ)
  | 4 => (2154643301 / 1000000000000 : ℝ)
  | 5 => (2176452597 / 1000000000000 : ℝ)
  | 6 => (2198043441 / 1000000000000 : ℝ)
  | 7 => (2219407731 / 1000000000000 : ℝ)
  | 8 => (560134339 / 250000000000 : ℝ)
  | 9 => (2261424191 / 1000000000000 : ℝ)
  | 10 => (285257513 / 125000000000 : ℝ)
  | 11 => (287804619 / 125000000000 : ℝ)
  | 12 => (1161273293 / 500000000000 : ℝ)
  | 13 => (2342380849 / 1000000000000 : ℝ)
  | 14 => (2361931581 / 1000000000000 : ℝ)
  | 15 => (297648827 / 125000000000 : ℝ)
  | 16 => (1200074893 / 500000000000 : ℝ)
  | 17 => (1209400461 / 500000000000 : ℝ)
  | 18 => (487427171 / 200000000000 : ℝ)
  | 19 => (491029283 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch006Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2087985487 / 1000000000000 : ℝ)
  | 1 => (1055200841 / 500000000000 : ℝ)
  | 2 => (2132623639 / 1000000000000 : ℝ)
  | 3 => (1077321651 / 500000000000 : ℝ)
  | 4 => (1088226299 / 500000000000 : ℝ)
  | 5 => (1099021721 / 500000000000 : ℝ)
  | 6 => (554851933 / 250000000000 : ℝ)
  | 7 => (2240537357 / 1000000000000 : ℝ)
  | 8 => (35334753 / 15625000000 : ℝ)
  | 9 => (456412021 / 200000000000 : ℝ)
  | 10 => (2302436953 / 1000000000000 : ℝ)
  | 11 => (2322546587 / 1000000000000 : ℝ)
  | 12 => (46847617 / 20000000000 : ℝ)
  | 13 => (1180965791 / 500000000000 : ℝ)
  | 14 => (2381190617 / 1000000000000 : ℝ)
  | 15 => (2400149787 / 1000000000000 : ℝ)
  | 16 => (2418800923 / 1000000000000 : ℝ)
  | 17 => (152320991 / 62500000000 : ℝ)
  | 18 => (153446651 / 62500000000 : ℝ)
  | 19 => (2472824437 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch006Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((120 : ℝ) + (j.val : ℝ)) / 1600)
      (((120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch006Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch006Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((120 : ℝ) + (j.val : ℝ)) / 1600)
    (((120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch006Neg100WeightLower j.val) (hpThetaShiftOneBatch006Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch006Neg100WeightLower, hpThetaShiftOneBatch006Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch006Neg100_integral_bounds :
    (740056731 / 15625000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (2415707677 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch006Lower hpThetaJensenCellsBatch006Upper
    hpThetaShiftOneBatch006Neg100WeightLower hpThetaShiftOneBatch006Neg100WeightUpper hpThetaJensenCellsBatch006_bounds hpThetaShiftOneBatch006Neg100_weight_bounds
  have hl : (740056731 / 15625000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch006Lower j * hpThetaShiftOneBatch006Neg100WeightLower j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftOneBatch006Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftOneBatch006Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch006Lower j * hpThetaShiftOneBatch006Neg100WeightUpper j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftOneBatch006Neg100WeightUpper j) / 1600) ≤ (2415707677 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftOneBatch006Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (120 : ℝ) / 1600 = 6 / 80 by norm_num,
    show ((120 : ℝ) + 20) / 1600 = (6 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch006Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (579243793 / 250000000000 : ℝ)
  | 1 => (2347639903 / 1000000000000 : ℝ)
  | 2 => (2378299437 / 1000000000000 : ℝ)
  | 3 => (301118483 / 125000000000 : ℝ)
  | 4 => (152473703 / 62500000000 : ℝ)
  | 5 => (2470187627 / 1000000000000 : ℝ)
  | 6 => (250076701 / 100000000000 : ℝ)
  | 7 => (2531311383 / 1000000000000 : ℝ)
  | 8 => (2561814707 / 1000000000000 : ℝ)
  | 9 => (648067729 / 250000000000 : ℝ)
  | 10 => (1311336961 / 500000000000 : ℝ)
  | 11 => (2653017613 / 1000000000000 : ℝ)
  | 12 => (1341647927 / 500000000000 : ℝ)
  | 13 => (1356751243 / 500000000000 : ℝ)
  | 14 => (274363133 / 100000000000 : ℝ)
  | 15 => (346709523 / 125000000000 : ℝ)
  | 16 => (700907707 / 250000000000 : ℝ)
  | 17 => (1416744509 / 500000000000 : ℝ)
  | 18 => (2863244493 / 1000000000000 : ℝ)
  | 19 => (289289097 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch006Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (73363747 / 31250000000 : ℝ)
  | 1 => (1189149719 / 500000000000 : ℝ)
  | 2 => (481789573 / 200000000000 : ℝ)
  | 3 => (2439579249 / 1000000000000 : ℝ)
  | 4 => (617546907 / 250000000000 : ℝ)
  | 5 => (2500767011 / 1000000000000 : ℝ)
  | 6 => (316413923 / 125000000000 : ℝ)
  | 7 => (640453677 / 250000000000 : ℝ)
  | 8 => (2592270917 / 1000000000000 : ℝ)
  | 9 => (2622673923 / 1000000000000 : ℝ)
  | 10 => (1326508807 / 500000000000 : ℝ)
  | 11 => (536659171 / 200000000000 : ℝ)
  | 12 => (2713502487 / 1000000000000 : ℝ)
  | 13 => (2743631331 / 1000000000000 : ℝ)
  | 14 => (554735237 / 200000000000 : ℝ)
  | 15 => (2803630829 / 1000000000000 : ℝ)
  | 16 => (2833489019 / 1000000000000 : ℝ)
  | 17 => (1431622247 / 500000000000 : ℝ)
  | 18 => (2892890971 / 1000000000000 : ℝ)
  | 19 => (365302769 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch006Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((120 : ℝ) + (j.val : ℝ)) / 1600)
      (((120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch006Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch006Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((120 : ℝ) + (j.val : ℝ)) / 1600)
    (((120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch006Neg65WeightLower j.val) (hpThetaShiftOneBatch006Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch006Neg65WeightLower, hpThetaShiftOneBatch006Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch006Neg65_integral_bounds :
    (54440277089 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (27838753917 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch006Lower hpThetaJensenCellsBatch006Upper
    hpThetaShiftOneBatch006Neg65WeightLower hpThetaShiftOneBatch006Neg65WeightUpper hpThetaJensenCellsBatch006_bounds hpThetaShiftOneBatch006Neg65_weight_bounds
  have hl : (54440277089 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch006Lower j * hpThetaShiftOneBatch006Neg65WeightLower j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftOneBatch006Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftOneBatch006Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch006Lower j * hpThetaShiftOneBatch006Neg65WeightUpper j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftOneBatch006Neg65WeightUpper j) / 1600) ≤ (27838753917 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftOneBatch006Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (120 : ℝ) / 1600 = 6 / 80 by norm_num,
    show ((120 : ℝ) + 20) / 1600 = (6 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch006Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (78224211 / 31250000000 : ℝ)
  | 1 => (2539926457 / 1000000000000 : ℝ)
  | 2 => (2576815877 / 1000000000000 : ℝ)
  | 3 => (2613839067 / 1000000000000 : ℝ)
  | 4 => (132549603 / 50000000000 : ℝ)
  | 5 => (2688270861 / 1000000000000 : ℝ)
  | 6 => (2725671457 / 1000000000000 : ℝ)
  | 7 => (1381594903 / 500000000000 : ℝ)
  | 8 => (1400410923 / 500000000000 : ℝ)
  | 9 => (2838563491 / 1000000000000 : ℝ)
  | 10 => (2876410631 / 1000000000000 : ℝ)
  | 11 => (582871827 / 200000000000 : ℝ)
  | 12 => (184525303 / 62500000000 : ℝ)
  | 13 => (2990543593 / 1000000000000 : ℝ)
  | 14 => (757192793 / 250000000000 : ℝ)
  | 15 => (3067083363 / 1000000000000 : ℝ)
  | 16 => (776368981 / 250000000000 : ℝ)
  | 17 => (196496537 / 62500000000 : ℝ)
  | 18 => (79562127 / 25000000000 : ℝ)
  | 19 => (3221093083 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch006Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1269963229 / 500000000000 : ℝ)
  | 1 => (1288407939 / 500000000000 : ℝ)
  | 2 => (653459767 / 250000000000 : ℝ)
  | 3 => (2650992061 / 1000000000000 : ℝ)
  | 4 => (1344135431 / 500000000000 : ℝ)
  | 5 => (1362835729 / 500000000000 : ℝ)
  | 6 => (2763189807 / 1000000000000 : ℝ)
  | 7 => (2800821847 / 1000000000000 : ℝ)
  | 8 => (709640873 / 250000000000 : ℝ)
  | 9 => (359551329 / 125000000000 : ℝ)
  | 10 => (91073723 / 31250000000 : ℝ)
  | 11 => (2952404849 / 1000000000000 : ℝ)
  | 12 => (1495271797 / 500000000000 : ℝ)
  | 13 => (3028771173 / 1000000000000 : ℝ)
  | 14 => (766770841 / 250000000000 : ℝ)
  | 15 => (124219037 / 40000000000 : ℝ)
  | 16 => (3143944593 / 1000000000000 : ℝ)
  | 17 => (3182485081 / 1000000000000 : ℝ)
  | 18 => (805273271 / 250000000000 : ℝ)
  | 19 => (1629882137 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch006Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((120 : ℝ) + (j.val : ℝ)) / 1600)
      (((120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch006Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch006Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((120 : ℝ) + (j.val : ℝ)) / 1600)
    (((120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch006Neg40WeightLower j.val) (hpThetaShiftOneBatch006Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch006Neg40WeightLower, hpThetaShiftOneBatch006Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch006Neg40_integral_bounds :
    (11942822407 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (61168783817 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch006Lower hpThetaJensenCellsBatch006Upper
    hpThetaShiftOneBatch006Neg40WeightLower hpThetaShiftOneBatch006Neg40WeightUpper hpThetaJensenCellsBatch006_bounds hpThetaShiftOneBatch006Neg40_weight_bounds
  have hl : (11942822407 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch006Lower j * hpThetaShiftOneBatch006Neg40WeightLower j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftOneBatch006Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftOneBatch006Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch006Lower j * hpThetaShiftOneBatch006Neg40WeightUpper j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftOneBatch006Neg40WeightUpper j) / 1600) ≤ (61168783817 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftOneBatch006Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (120 : ℝ) / 1600 = 6 / 80 by norm_num,
    show ((120 : ℝ) + 20) / 1600 = (6 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch006Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (664017973 / 250000000000 : ℝ)
  | 1 => (2697893019 / 1000000000000 : ℝ)
  | 2 => (2739974541 / 1000000000000 : ℝ)
  | 3 => (69557859 / 25000000000 : ℝ)
  | 4 => (706227591 / 250000000000 : ℝ)
  | 5 => (114710417 / 40000000000 : ℝ)
  | 6 => (2910862401 / 1000000000000 : ℝ)
  | 7 => (1477107067 / 500000000000 : ℝ)
  | 8 => (59956269 / 20000000000 : ℝ)
  | 9 => (3041658163 / 1000000000000 : ℝ)
  | 10 => (3085746071 / 1000000000000 : ℝ)
  | 11 => (1565037477 / 500000000000 : ℝ)
  | 12 => (3174642583 / 1000000000000 : ℝ)
  | 13 => (321944671 / 100000000000 : ℝ)
  | 14 => (1632242537 / 500000000000 : ℝ)
  | 15 => (1654877699 / 500000000000 : ℝ)
  | 16 => (1677627697 / 500000000000 : ℝ)
  | 17 => (680196551 / 200000000000 : ℝ)
  | 18 => (3446935163 / 1000000000000 : ℝ)
  | 19 => (873277571 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch006Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (134894651 / 50000000000 : ℝ)
  | 1 => (1369987271 / 500000000000 : ℝ)
  | 2 => (2782314361 / 1000000000000 : ℝ)
  | 3 => (564982073 / 200000000000 : ℝ)
  | 4 => (1433880213 / 500000000000 : ℝ)
  | 5 => (1455431201 / 500000000000 : ℝ)
  | 6 => (590842827 / 200000000000 : ℝ)
  | 7 => (2997813451 / 1000000000000 : ℝ)
  | 8 => (760414541 / 250000000000 : ℝ)
  | 9 => (385718259 / 125000000000 : ℝ)
  | 10 => (626014991 / 200000000000 : ℝ)
  | 11 => (396830323 / 125000000000 : ℝ)
  | 12 => (3219446711 / 1000000000000 : ℝ)
  | 13 => (130579403 / 40000000000 : ℝ)
  | 14 => (3309755399 / 1000000000000 : ℝ)
  | 15 => (671051079 / 200000000000 : ℝ)
  | 16 => (850245689 / 250000000000 : ℝ)
  | 17 => (861733791 / 250000000000 : ℝ)
  | 18 => (698622057 / 200000000000 : ℝ)
  | 19 => (3539505771 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch006Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((120 : ℝ) + (j.val : ℝ)) / 1600)
      (((120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch006Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch006Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((120 : ℝ) + (j.val : ℝ)) / 1600)
    (((120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch006Neg20WeightLower j.val) (hpThetaShiftOneBatch006Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch006Neg20WeightLower, hpThetaShiftOneBatch006Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch006Neg20_integral_bounds :
    (32033185323 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (6 / 80 : ℝ) ((6 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (32851357077 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch006Lower hpThetaJensenCellsBatch006Upper
    hpThetaShiftOneBatch006Neg20WeightLower hpThetaShiftOneBatch006Neg20WeightUpper hpThetaJensenCellsBatch006_bounds hpThetaShiftOneBatch006Neg20_weight_bounds
  have hl : (32033185323 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch006Lower j * hpThetaShiftOneBatch006Neg20WeightLower j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftOneBatch006Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftOneBatch006Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch006Lower j * hpThetaShiftOneBatch006Neg20WeightUpper j)
        (hpThetaJensenCellsBatch006Upper j * hpThetaShiftOneBatch006Neg20WeightUpper j) / 1600) ≤ (32851357077 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch006Lower, hpThetaJensenCellsBatch006Upper,
      hpThetaShiftOneBatch006Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (120 : ℝ) / 1600 = 6 / 80 by norm_num,
    show ((120 : ℝ) + 20) / 1600 = (6 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch006Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch006Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch006Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch006Neg20_integral_bounds
end HodgeProofHP
