/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch061

/-! Exact signed weight and batch integral certificates, batch 61 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch061Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5538034197 / 500000000000 : ℝ)
  | 1 => (-11235534331 / 1000000000000 : ℝ)
  | 2 => (-11396938583 / 1000000000000 : ℝ)
  | 3 => (-2312060267 / 200000000000 : ℝ)
  | 4 => (-11725642953 / 1000000000000 : ℝ)
  | 5 => (-5946491993 / 500000000000 : ℝ)
  | 6 => (-2412469033 / 200000000000 : ℝ)
  | 7 => (-764609213 / 62500000000 : ℝ)
  | 8 => (-6203605909 / 500000000000 : ℝ)
  | 9 => (-6291379843 / 500000000000 : ℝ)
  | 10 => (-3190103123 / 250000000000 : ℝ)
  | 11 => (-12940191907 / 1000000000000 : ℝ)
  | 12 => (-13122119793 / 1000000000000 : ℝ)
  | 13 => (-13306218207 / 1000000000000 : ℝ)
  | 14 => (-67462547 / 5000000000 : ℝ)
  | 15 => (-684050791 / 50000000000 : ℝ)
  | 16 => (-13871760113 / 1000000000000 : ℝ)
  | 17 => (-3516191281 / 250000000000 : ℝ)
  | 18 => (-7130026949 / 500000000000 : ℝ)
  | 19 => (-7228824843 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch061Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-10918520763 / 1000000000000 : ℝ)
  | 1 => (-11076068393 / 1000000000000 : ℝ)
  | 2 => (-1123553433 / 100000000000 : ℝ)
  | 3 => (-5698469291 / 500000000000 : ℝ)
  | 4 => (-5780150667 / 500000000000 : ℝ)
  | 5 => (-1465705369 / 125000000000 : ℝ)
  | 6 => (-2378596797 / 200000000000 : ℝ)
  | 7 => (-3015586291 / 250000000000 : ℝ)
  | 8 => (-12233747407 / 1000000000000 : ℝ)
  | 9 => (-12407211817 / 1000000000000 : ℝ)
  | 10 => (-2516551937 / 200000000000 : ℝ)
  | 11 => (-12760412491 / 1000000000000 : ℝ)
  | 12 => (-6470095953 / 500000000000 : ℝ)
  | 13 => (-820132487 / 62500000000 : ℝ)
  | 14 => (-6653109103 / 500000000000 : ℝ)
  | 15 => (-13492509399 / 1000000000000 : ℝ)
  | 16 => (-13681015819 / 1000000000000 : ℝ)
  | 17 => (-866985007 / 62500000000 : ℝ)
  | 18 => (-14064765123 / 1000000000000 : ℝ)
  | 19 => (-14260053897 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch061Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1220 : ℝ) + (j.val : ℝ)) / 1600)
      (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch061Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch061Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1220 : ℝ) + (j.val : ℝ)) / 1600)
    (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch061Neg100WeightLower j.val) (hpThetaShiftThreeBatch061Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch061Neg100WeightLower, hpThetaShiftThreeBatch061Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch061Neg100_integral_bounds :
    (-80998259 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-155971439 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch061Lower hpThetaJensenCellsBatch061Upper
    hpThetaShiftThreeBatch061Neg100WeightLower hpThetaShiftThreeBatch061Neg100WeightUpper hpThetaJensenCellsBatch061_bounds hpThetaShiftThreeBatch061Neg100_weight_bounds
  have hl : (-80998259 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch061Lower j * hpThetaShiftThreeBatch061Neg100WeightLower j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftThreeBatch061Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftThreeBatch061Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch061Lower j * hpThetaShiftThreeBatch061Neg100WeightUpper j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftThreeBatch061Neg100WeightUpper j) / 1600) ≤ (-155971439 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftThreeBatch061Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1220 : ℝ) / 1600 = 61 / 80 by norm_num,
    show ((1220 : ℝ) + 20) / 1600 = (61 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch061Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-281973823 / 1000000000000 : ℝ)
  | 1 => (-59845789 / 200000000000 : ℝ)
  | 2 => (-31681029 / 100000000000 : ℝ)
  | 3 => (-2615017 / 7812500000 : ℝ)
  | 4 => (-70593793 / 200000000000 : ℝ)
  | 5 => (-46444383 / 125000000000 : ℝ)
  | 6 => (-195242463 / 500000000000 : ℝ)
  | 7 => (-8195261 / 20000000000 : ℝ)
  | 8 => (-429393983 / 1000000000000 : ℝ)
  | 9 => (-449382317 / 1000000000000 : ℝ)
  | 10 => (-117433173 / 250000000000 : ℝ)
  | 11 => (-122612449 / 250000000000 : ℝ)
  | 12 => (-255769183 / 500000000000 : ℝ)
  | 13 => (-106600637 / 200000000000 : ℝ)
  | 14 => (-554849089 / 1000000000000 : ℝ)
  | 15 => (-577080959 / 1000000000000 : ℝ)
  | 16 => (-37481483 / 62500000000 : ℝ)
  | 17 => (-31136119 / 50000000000 : ℝ)
  | 18 => (-646141949 / 1000000000000 : ℝ)
  | 19 => (-334983759 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch061Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-265040653 / 1000000000000 : ℝ)
  | 1 => (-140986911 / 500000000000 : ℝ)
  | 2 => (-18701809 / 62500000000 : ℝ)
  | 3 => (-316810289 / 1000000000000 : ℝ)
  | 4 => (-13388887 / 40000000000 : ℝ)
  | 5 => (-88242241 / 250000000000 : ℝ)
  | 6 => (-371555063 / 1000000000000 : ℝ)
  | 7 => (-15619397 / 40000000000 : ℝ)
  | 8 => (-409763049 / 1000000000000 : ℝ)
  | 9 => (-214696991 / 500000000000 : ℝ)
  | 10 => (-112345579 / 250000000000 : ℝ)
  | 11 => (-469732691 / 1000000000000 : ℝ)
  | 12 => (-98089959 / 200000000000 : ℝ)
  | 13 => (-102307673 / 200000000000 : ℝ)
  | 14 => (-33312699 / 62500000000 : ℝ)
  | 15 => (-8669517 / 15625000000 : ℝ)
  | 16 => (-288540479 / 500000000000 : ℝ)
  | 17 => (-599703727 / 1000000000000 : ℝ)
  | 18 => (-622722379 / 1000000000000 : ℝ)
  | 19 => (-161535487 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch061Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1220 : ℝ) + (j.val : ℝ)) / 1600)
      (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch061Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch061Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1220 : ℝ) + (j.val : ℝ)) / 1600)
    (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch061Neg70WeightLower j.val) (hpThetaShiftThreeBatch061Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch061Neg70WeightLower, hpThetaShiftThreeBatch061Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch061Neg70_integral_bounds :
    (-1169057 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-5455789 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch061Lower hpThetaJensenCellsBatch061Upper
    hpThetaShiftThreeBatch061Neg70WeightLower hpThetaShiftThreeBatch061Neg70WeightUpper hpThetaJensenCellsBatch061_bounds hpThetaShiftThreeBatch061Neg70_weight_bounds
  have hl : (-1169057 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch061Lower j * hpThetaShiftThreeBatch061Neg70WeightLower j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftThreeBatch061Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftThreeBatch061Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch061Lower j * hpThetaShiftThreeBatch061Neg70WeightUpper j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftThreeBatch061Neg70WeightUpper j) / 1600) ≤ (-5455789 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftThreeBatch061Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1220 : ℝ) / 1600 = 61 / 80 by norm_num,
    show ((1220 : ℝ) + 20) / 1600 = (61 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch061Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (102269881 / 200000000000 : ℝ)
  | 1 => (516563073 / 1000000000000 : ℝ)
  | 2 => (521801949 / 1000000000000 : ℝ)
  | 3 => (13176647 / 25000000000 : ℝ)
  | 4 => (532354709 / 1000000000000 : ℝ)
  | 5 => (268834137 / 500000000000 : ℝ)
  | 6 => (543006411 / 1000000000000 : ℝ)
  | 7 => (109673789 / 200000000000 : ℝ)
  | 8 => (276877851 / 500000000000 : ℝ)
  | 9 => (279583249 / 500000000000 : ℝ)
  | 10 => (141150287 / 250000000000 : ℝ)
  | 11 => (285029729 / 500000000000 : ℝ)
  | 12 => (575541231 / 1000000000000 : ℝ)
  | 13 => (116209253 / 200000000000 : ℝ)
  | 14 => (11731487 / 20000000000 : ℝ)
  | 15 => (592125273 / 1000000000000 : ℝ)
  | 16 => (119539763 / 200000000000 : ℝ)
  | 17 => (603294749 / 1000000000000 : ℝ)
  | 18 => (304456423 / 500000000000 : ℝ)
  | 19 => (153638217 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch061Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (258281537 / 500000000000 : ℝ)
  | 1 => (10436039 / 20000000000 : ℝ)
  | 2 => (527065881 / 1000000000000 : ℝ)
  | 3 => (53235471 / 100000000000 : ℝ)
  | 4 => (21506731 / 40000000000 : ℝ)
  | 5 => (135751603 / 250000000000 : ℝ)
  | 6 => (274184473 / 500000000000 : ℝ)
  | 7 => (553755703 / 1000000000000 : ℝ)
  | 8 => (559166499 / 1000000000000 : ℝ)
  | 9 => (564601149 / 1000000000000 : ℝ)
  | 10 => (570059459 / 1000000000000 : ℝ)
  | 11 => (35971327 / 62500000000 : ℝ)
  | 12 => (290523133 / 500000000000 : ℝ)
  | 13 => (586574351 / 1000000000000 : ℝ)
  | 14 => (296062637 / 500000000000 : ℝ)
  | 15 => (2334761 / 3906250000 : ℝ)
  | 16 => (2413179 / 4000000000 : ℝ)
  | 17 => (608912847 / 1000000000000 : ℝ)
  | 18 => (614552869 / 1000000000000 : ℝ)
  | 19 => (310107287 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch061Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1220 : ℝ) + (j.val : ℝ)) / 1600)
      (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch061Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch061Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1220 : ℝ) + (j.val : ℝ)) / 1600)
    (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch061Neg45WeightLower j.val) (hpThetaShiftThreeBatch061Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch061Neg45WeightLower, hpThetaShiftThreeBatch061Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch061Neg45_integral_bounds :
    (3507489 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (3627051 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch061Lower hpThetaJensenCellsBatch061Upper
    hpThetaShiftThreeBatch061Neg45WeightLower hpThetaShiftThreeBatch061Neg45WeightUpper hpThetaJensenCellsBatch061_bounds hpThetaShiftThreeBatch061Neg45_weight_bounds
  have hl : (3507489 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch061Lower j * hpThetaShiftThreeBatch061Neg45WeightLower j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftThreeBatch061Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftThreeBatch061Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch061Lower j * hpThetaShiftThreeBatch061Neg45WeightUpper j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftThreeBatch061Neg45WeightUpper j) / 1600) ≤ (3627051 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftThreeBatch061Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1220 : ℝ) / 1600 = 61 / 80 by norm_num,
    show ((1220 : ℝ) + 20) / 1600 = (61 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch061Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-62968663 / 250000000000 : ℝ)
  | 1 => (-50482871 / 200000000000 : ℝ)
  | 2 => (-25294407 / 100000000000 : ℝ)
  | 3 => (-31682957 / 125000000000 : ℝ)
  | 4 => (-253972973 / 1000000000000 : ℝ)
  | 5 => (-254471877 / 1000000000000 : ℝ)
  | 6 => (-127480113 / 500000000000 : ℝ)
  | 7 => (-63859469 / 250000000000 : ℝ)
  | 8 => (-127952341 / 500000000000 : ℝ)
  | 9 => (-256360497 / 1000000000000 : ℝ)
  | 10 => (-10272207 / 40000000000 : ℝ)
  | 11 => (-32154821 / 125000000000 : ℝ)
  | 12 => (-257660527 / 1000000000000 : ℝ)
  | 13 => (-258070903 / 1000000000000 : ℝ)
  | 14 => (-51693909 / 200000000000 : ℝ)
  | 15 => (-129428151 / 500000000000 : ℝ)
  | 16 => (-259231021 / 1000000000000 : ℝ)
  | 17 => (-259593549 / 1000000000000 : ℝ)
  | 18 => (-259943731 / 1000000000000 : ℝ)
  | 19 => (-260281413 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch061Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2513251 / 10000000000 : ℝ)
  | 1 => (-251874651 / 1000000000000 : ℝ)
  | 2 => (-126207177 / 500000000000 : ℝ)
  | 3 => (-252944069 / 1000000000000 : ℝ)
  | 4 => (-50692731 / 200000000000 : ℝ)
  | 5 => (-63493243 / 250000000000 : ℝ)
  | 6 => (-63617969 / 250000000000 : ℝ)
  | 7 => (-10198409 / 40000000000 : ℝ)
  | 8 => (-2043503 / 8000000000 : ℝ)
  | 9 => (-255904681 / 1000000000000 : ℝ)
  | 10 => (-16022531 / 62500000000 : ℝ)
  | 11 => (-128402587 / 500000000000 : ℝ)
  | 12 => (-257238567 / 1000000000000 : ℝ)
  | 13 => (-128830263 / 500000000000 : ℝ)
  | 14 => (-129035451 / 500000000000 : ℝ)
  | 15 => (-32308693 / 125000000000 : ℝ)
  | 16 => (-258856301 / 1000000000000 : ℝ)
  | 17 => (-12961551 / 50000000000 : ℝ)
  | 18 => (-64898387 / 250000000000 : ℝ)
  | 19 => (-25994373 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch061Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1220 : ℝ) + (j.val : ℝ)) / 1600)
      (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch061Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch061Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1220 : ℝ) + (j.val : ℝ)) / 1600)
    (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch061Neg25WeightLower j.val) (hpThetaShiftThreeBatch061Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch061Neg25WeightLower, hpThetaShiftThreeBatch061Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch061Neg25_integral_bounds :
    (-3289327 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-3206107 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch061Lower hpThetaJensenCellsBatch061Upper
    hpThetaShiftThreeBatch061Neg25WeightLower hpThetaShiftThreeBatch061Neg25WeightUpper hpThetaJensenCellsBatch061_bounds hpThetaShiftThreeBatch061Neg25_weight_bounds
  have hl : (-3289327 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch061Lower j * hpThetaShiftThreeBatch061Neg25WeightLower j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftThreeBatch061Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftThreeBatch061Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch061Lower j * hpThetaShiftThreeBatch061Neg25WeightUpper j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftThreeBatch061Neg25WeightUpper j) / 1600) ≤ (-3206107 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftThreeBatch061Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1220 : ℝ) / 1600 = 61 / 80 by norm_num,
    show ((1220 : ℝ) + 20) / 1600 = (61 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch061Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch061Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch061Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch061Neg25_integral_bounds
end HodgeProofHP
