/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch040

/-! Exact signed weight and batch integral certificates, batch 40 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch040Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (690029 / 20000000000 : ℝ)
  | 1 => (3511091 / 100000000000 : ℝ)
  | 2 => (17862989 / 500000000000 : ℝ)
  | 3 => (36346639 / 1000000000000 : ℝ)
  | 4 => (462161 / 12500000000 : ℝ)
  | 5 => (9401171 / 250000000000 : ℝ)
  | 6 => (38242033 / 1000000000000 : ℝ)
  | 7 => (38884907 / 1000000000000 : ℝ)
  | 8 => (39533287 / 1000000000000 : ℝ)
  | 9 => (40187147 / 1000000000000 : ℝ)
  | 10 => (8169293 / 200000000000 : ℝ)
  | 11 => (41511213 / 1000000000000 : ℝ)
  | 12 => (42181363 / 1000000000000 : ℝ)
  | 13 => (21428443 / 500000000000 : ℝ)
  | 14 => (43537749 / 1000000000000 : ℝ)
  | 15 => (44223919 / 1000000000000 : ℝ)
  | 16 => (280721 / 6250000000 : ℝ)
  | 17 => (22806017 / 500000000000 : ℝ)
  | 18 => (46313901 / 1000000000000 : ℝ)
  | 19 => (47020919 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch040Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (35110911 / 1000000000000 : ℝ)
  | 1 => (35725979 / 1000000000000 : ℝ)
  | 2 => (454333 / 12500000000 : ℝ)
  | 3 => (36972881 / 1000000000000 : ℝ)
  | 4 => (7520937 / 200000000000 : ℝ)
  | 5 => (19121017 / 500000000000 : ℝ)
  | 6 => (9721227 / 250000000000 : ℝ)
  | 7 => (4941661 / 125000000000 : ℝ)
  | 8 => (10046787 / 250000000000 : ℝ)
  | 9 => (20423233 / 500000000000 : ℝ)
  | 10 => (20755607 / 500000000000 : ℝ)
  | 11 => (10545341 / 250000000000 : ℝ)
  | 12 => (42856887 / 1000000000000 : ℝ)
  | 13 => (174151 / 4000000000 : ℝ)
  | 14 => (552799 / 12500000000 : ℝ)
  | 15 => (44915361 / 1000000000000 : ℝ)
  | 16 => (9122407 / 200000000000 : ℝ)
  | 17 => (23156951 / 500000000000 : ℝ)
  | 18 => (1175523 / 25000000000 : ℝ)
  | 19 => (47733047 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch040Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((800 : ℝ) + (j.val : ℝ)) / 1600)
      (((800 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch040Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch040Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((800 : ℝ) + (j.val : ℝ)) / 1600)
    (((800 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch040Neg100WeightLower j.val) (hpThetaShiftThreeBatch040Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch040Neg100WeightLower, hpThetaShiftThreeBatch040Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch040Neg100_integral_bounds :
    (14046293 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (3628357 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (800 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch040Lower hpThetaJensenCellsBatch040Upper
    hpThetaShiftThreeBatch040Neg100WeightLower hpThetaShiftThreeBatch040Neg100WeightUpper hpThetaJensenCellsBatch040_bounds hpThetaShiftThreeBatch040Neg100_weight_bounds
  have hl : (14046293 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch040Lower j * hpThetaShiftThreeBatch040Neg100WeightLower j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftThreeBatch040Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftThreeBatch040Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch040Lower j * hpThetaShiftThreeBatch040Neg100WeightUpper j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftThreeBatch040Neg100WeightUpper j) / 1600) ≤ (3628357 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftThreeBatch040Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (800 : ℝ) / 1600 = 40 / 80 by norm_num,
    show ((800 : ℝ) + 20) / 1600 = (40 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch040Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-9227201 / 1000000000000 : ℝ)
  | 1 => (-9085463 / 1000000000000 : ℝ)
  | 2 => (-4469749 / 500000000000 : ℝ)
  | 3 => (-35157 / 4000000000 : ℝ)
  | 4 => (-8634667 / 1000000000000 : ℝ)
  | 5 => (-4237847 / 500000000000 : ℝ)
  | 6 => (-2078069 / 250000000000 : ℝ)
  | 7 => (-8144359 / 1000000000000 : ℝ)
  | 8 => (-498243 / 62500000000 : ℝ)
  | 9 => (-7794807 / 1000000000000 : ℝ)
  | 10 => (-7613061 / 1000000000000 : ℝ)
  | 11 => (-3713297 / 500000000000 : ℝ)
  | 12 => (-144707 / 20000000000 : ℝ)
  | 13 => (-879909 / 125000000000 : ℝ)
  | 14 => (-213697 / 31250000000 : ℝ)
  | 15 => (-1658097 / 250000000000 : ℝ)
  | 16 => (-1605367 / 250000000000 : ℝ)
  | 17 => (-3102743 / 500000000000 : ℝ)
  | 18 => (-46753 / 7812500000 : ℝ)
  | 19 => (-719763 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch040Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4542731 / 500000000000 : ℝ)
  | 1 => (-8939497 / 1000000000000 : ℝ)
  | 2 => (-8789249 / 1000000000000 : ℝ)
  | 3 => (-4317333 / 500000000000 : ℝ)
  | 4 => (-8475693 / 1000000000000 : ℝ)
  | 5 => (-332491 / 40000000000 : ℝ)
  | 6 => (-4072179 / 500000000000 : ℝ)
  | 7 => (-7971887 / 1000000000000 : ℝ)
  | 8 => (-3897403 / 500000000000 : ℝ)
  | 9 => (-380653 / 50000000000 : ℝ)
  | 10 => (-7426593 / 1000000000000 : ℝ)
  | 11 => (-7235349 / 1000000000000 : ℝ)
  | 12 => (-7039271 / 1000000000000 : ℝ)
  | 13 => (-6838303 / 1000000000000 : ℝ)
  | 14 => (-6632387 / 1000000000000 : ℝ)
  | 15 => (-6421467 / 1000000000000 : ℝ)
  | 16 => (-1241097 / 200000000000 : ℝ)
  | 17 => (-5984383 / 1000000000000 : ℝ)
  | 18 => (-5758103 / 1000000000000 : ℝ)
  | 19 => (-5526587 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch040Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((800 : ℝ) + (j.val : ℝ)) / 1600)
      (((800 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch040Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch040Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((800 : ℝ) + (j.val : ℝ)) / 1600)
    (((800 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch040Neg70WeightLower j.val) (hpThetaShiftThreeBatch040Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch040Neg70WeightLower, hpThetaShiftThreeBatch040Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch040Neg70_integral_bounds :
    (-10839111 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-2081257 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (800 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch040Lower hpThetaJensenCellsBatch040Upper
    hpThetaShiftThreeBatch040Neg70WeightLower hpThetaShiftThreeBatch040Neg70WeightUpper hpThetaJensenCellsBatch040_bounds hpThetaShiftThreeBatch040Neg70_weight_bounds
  have hl : (-10839111 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch040Lower j * hpThetaShiftThreeBatch040Neg70WeightLower j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftThreeBatch040Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftThreeBatch040Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch040Lower j * hpThetaShiftThreeBatch040Neg70WeightUpper j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftThreeBatch040Neg70WeightUpper j) / 1600) ≤ (-2081257 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftThreeBatch040Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (800 : ℝ) / 1600 = 40 / 80 by norm_num,
    show ((800 : ℝ) + 20) / 1600 = (40 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch040Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-10577439 / 500000000000 : ℝ)
  | 1 => (-10683779 / 500000000000 : ℝ)
  | 2 => (-21580881 / 1000000000000 : ℝ)
  | 3 => (-21794831 / 1000000000000 : ℝ)
  | 4 => (-22009393 / 1000000000000 : ℝ)
  | 5 => (-22224551 / 1000000000000 : ℝ)
  | 6 => (-2244029 / 100000000000 : ℝ)
  | 7 => (-11328297 / 500000000000 : ℝ)
  | 8 => (-22873447 / 1000000000000 : ℝ)
  | 9 => (-23090831 / 1000000000000 : ℝ)
  | 10 => (-23308731 / 1000000000000 : ℝ)
  | 11 => (-2940891 / 125000000000 : ℝ)
  | 12 => (-11873003 / 500000000000 : ℝ)
  | 13 => (-23965347 / 1000000000000 : ℝ)
  | 14 => (-6046283 / 250000000000 : ℝ)
  | 15 => (-762667 / 31250000000 : ℝ)
  | 16 => (-24625963 / 1000000000000 : ℝ)
  | 17 => (-2484697 / 100000000000 : ℝ)
  | 18 => (-6267087 / 250000000000 : ℝ)
  | 19 => (-12645037 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch040Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-20942853 / 1000000000000 : ℝ)
  | 1 => (-21154877 / 1000000000000 : ℝ)
  | 2 => (-21367557 / 1000000000000 : ℝ)
  | 3 => (-269761 / 12500000000 : ℝ)
  | 4 => (-2179483 / 100000000000 : ℝ)
  | 5 => (-1375587 / 62500000000 : ℝ)
  | 6 => (-444491 / 20000000000 : ℝ)
  | 7 => (-22440289 / 1000000000000 : ℝ)
  | 8 => (-22656593 / 1000000000000 : ℝ)
  | 9 => (-11436723 / 500000000000 : ℝ)
  | 10 => (-2309083 / 100000000000 : ℝ)
  | 11 => (-2330873 / 100000000000 : ℝ)
  | 12 => (-23527127 / 1000000000000 : ℝ)
  | 13 => (-4749201 / 200000000000 : ℝ)
  | 14 => (-11982673 / 500000000000 : ℝ)
  | 15 => (-24185131 / 1000000000000 : ℝ)
  | 16 => (-24405343 / 1000000000000 : ℝ)
  | 17 => (-12312981 / 500000000000 : ℝ)
  | 18 => (-24846969 / 1000000000000 : ℝ)
  | 19 => (-25068347 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch040Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((800 : ℝ) + (j.val : ℝ)) / 1600)
      (((800 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch040Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch040Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((800 : ℝ) + (j.val : ℝ)) / 1600)
    (((800 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch040Neg45WeightLower j.val) (hpThetaShiftThreeBatch040Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch040Neg45WeightLower, hpThetaShiftThreeBatch040Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch040Neg45_integral_bounds :
    (-32704471 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-15933427 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (800 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch040Lower hpThetaJensenCellsBatch040Upper
    hpThetaShiftThreeBatch040Neg45WeightLower hpThetaShiftThreeBatch040Neg45WeightUpper hpThetaJensenCellsBatch040_bounds hpThetaShiftThreeBatch040Neg45_weight_bounds
  have hl : (-32704471 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch040Lower j * hpThetaShiftThreeBatch040Neg45WeightLower j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftThreeBatch040Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftThreeBatch040Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch040Lower j * hpThetaShiftThreeBatch040Neg45WeightUpper j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftThreeBatch040Neg45WeightUpper j) / 1600) ≤ (-15933427 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftThreeBatch040Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (800 : ℝ) / 1600 = 40 / 80 by norm_num,
    show ((800 : ℝ) + 20) / 1600 = (40 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch040Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2635403 / 250000000000 : ℝ)
  | 1 => (10442437 / 1000000000000 : ℝ)
  | 2 => (2585353 / 250000000000 : ℝ)
  | 3 => (2559631 / 250000000000 : ℝ)
  | 4 => (5066879 / 500000000000 : ℝ)
  | 5 => (10027101 / 1000000000000 : ℝ)
  | 6 => (495927 / 50000000000 : ℝ)
  | 7 => (490403 / 50000000000 : ℝ)
  | 8 => (302989 / 31250000000 : ℝ)
  | 9 => (9581291 / 1000000000000 : ℝ)
  | 10 => (4732487 / 500000000000 : ℝ)
  | 11 => (9346683 / 1000000000000 : ℝ)
  | 12 => (4613203 / 500000000000 : ℝ)
  | 13 => (9104127 / 1000000000000 : ℝ)
  | 14 => (4489917 / 500000000000 : ℝ)
  | 15 => (8853513 / 1000000000000 : ℝ)
  | 16 => (174503 / 20000000000 : ℝ)
  | 17 => (859473 / 100000000000 : ℝ)
  | 18 => (52889 / 6250000000 : ℝ)
  | 19 => (8327667 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch040Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (10638951 / 1000000000000 : ℝ)
  | 1 => (10541613 / 1000000000000 : ℝ)
  | 2 => (5221219 / 500000000000 : ℝ)
  | 3 => (10341413 / 1000000000000 : ℝ)
  | 4 => (409541 / 40000000000 : ℝ)
  | 5 => (10133759 / 1000000000000 : ℝ)
  | 6 => (5013551 / 500000000000 : ℝ)
  | 7 => (9918541 / 1000000000000 : ℝ)
  | 8 => (9808061 / 1000000000000 : ℝ)
  | 9 => (9695649 / 1000000000000 : ℝ)
  | 10 => (2395323 / 250000000000 : ℝ)
  | 11 => (378599 / 40000000000 : ℝ)
  | 12 => (2336671 / 250000000000 : ℝ)
  | 13 => (9226407 / 1000000000000 : ℝ)
  | 14 => (35563 / 3906250000 : ℝ)
  | 15 => (1795967 / 200000000000 : ℝ)
  | 16 => (4426757 / 500000000000 : ℝ)
  | 17 => (8725151 / 1000000000000 : ℝ)
  | 18 => (8594731 / 1000000000000 : ℝ)
  | 19 => (8462241 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch040Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((800 : ℝ) + (j.val : ℝ)) / 1600)
      (((800 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch040Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch040Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((800 : ℝ) + (j.val : ℝ)) / 1600)
    (((800 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch040Neg25WeightLower j.val) (hpThetaShiftThreeBatch040Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch040Neg25WeightLower, hpThetaShiftThreeBatch040Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch040Neg25_integral_bounds :
    (13228419 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (6805577 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (800 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch040Lower hpThetaJensenCellsBatch040Upper
    hpThetaShiftThreeBatch040Neg25WeightLower hpThetaShiftThreeBatch040Neg25WeightUpper hpThetaJensenCellsBatch040_bounds hpThetaShiftThreeBatch040Neg25_weight_bounds
  have hl : (13228419 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch040Lower j * hpThetaShiftThreeBatch040Neg25WeightLower j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftThreeBatch040Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftThreeBatch040Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch040Lower j * hpThetaShiftThreeBatch040Neg25WeightUpper j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftThreeBatch040Neg25WeightUpper j) / 1600) ≤ (6805577 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftThreeBatch040Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (800 : ℝ) / 1600 = 40 / 80 by norm_num,
    show ((800 : ℝ) + 20) / 1600 = (40 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch040Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch040Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch040Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch040Neg25_integral_bounds
end HodgeProofHP
