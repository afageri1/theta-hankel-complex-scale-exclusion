/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch065

/-! Exact signed weight and batch integral certificates, batch 65 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch065Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-31938876021 / 1000000000000 : ℝ)
  | 1 => (-16167232683 / 500000000000 : ℝ)
  | 2 => (-6546861659 / 200000000000 : ℝ)
  | 3 => (-8284611163 / 250000000000 : ℝ)
  | 4 => (-2096682163 / 62500000000 : ℝ)
  | 5 => (-33959758657 / 1000000000000 : ℝ)
  | 6 => (-17188508813 / 500000000000 : ℝ)
  | 7 => (-34798732671 / 1000000000000 : ℝ)
  | 8 => (-35224945281 / 1000000000000 : ℝ)
  | 9 => (-8913924321 / 250000000000 : ℝ)
  | 10 => (-18045515421 / 500000000000 : ℝ)
  | 11 => (-36530988461 / 1000000000000 : ℝ)
  | 12 => (-36975612989 / 1000000000000 : ℝ)
  | 13 => (-1871247381 / 50000000000 : ℝ)
  | 14 => (-18939517947 / 500000000000 : ℝ)
  | 15 => (-4792240213 / 125000000000 : ℝ)
  | 16 => (-19400824647 / 500000000000 : ℝ)
  | 17 => (-19635131631 / 500000000000 : ℝ)
  | 18 => (-19871904283 / 500000000000 : ℝ)
  | 19 => (-40222330523 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch065Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-492929699 / 15625000000 : ℝ)
  | 1 => (-1596943801 / 50000000000 : ℝ)
  | 2 => (-6466893073 / 200000000000 : ℝ)
  | 3 => (-16367154147 / 500000000000 : ℝ)
  | 4 => (-33138444651 / 1000000000000 : ℝ)
  | 5 => (-33546914607 / 1000000000000 : ℝ)
  | 6 => (-530621229 / 15625000000 : ℝ)
  | 7 => (-275016141 / 8000000000 : ℝ)
  | 8 => (-3479873267 / 100000000000 : ℝ)
  | 9 => (-55038977 / 1562500000 : ℝ)
  | 10 => (-35655697283 / 1000000000000 : ℝ)
  | 11 => (-36091030841 / 1000000000000 : ℝ)
  | 12 => (-1826549423 / 50000000000 : ℝ)
  | 13 => (-9243903247 / 250000000000 : ℝ)
  | 14 => (-37424947619 / 1000000000000 : ℝ)
  | 15 => (-37879035893 / 1000000000000 : ℝ)
  | 16 => (-38337921703 / 1000000000000 : ℝ)
  | 17 => (-38801649293 / 1000000000000 : ℝ)
  | 18 => (-39270263261 / 1000000000000 : ℝ)
  | 19 => (-7948761713 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch065Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1300 : ℝ) + (j.val : ℝ)) / 1600)
      (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch065Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch065Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1300 : ℝ) + (j.val : ℝ)) / 1600)
    (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch065Neg100WeightLower j.val) (hpThetaShiftThreeBatch065Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch065Neg100WeightLower, hpThetaShiftThreeBatch065Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch065Neg100_integral_bounds :
    (-124983281 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-24066617 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch065Lower hpThetaJensenCellsBatch065Upper
    hpThetaShiftThreeBatch065Neg100WeightLower hpThetaShiftThreeBatch065Neg100WeightUpper hpThetaJensenCellsBatch065_bounds hpThetaShiftThreeBatch065Neg100_weight_bounds
  have hl : (-124983281 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch065Lower j * hpThetaShiftThreeBatch065Neg100WeightLower j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftThreeBatch065Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftThreeBatch065Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch065Lower j * hpThetaShiftThreeBatch065Neg100WeightUpper j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftThreeBatch065Neg100WeightUpper j) / 1600) ≤ (-24066617 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftThreeBatch065Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1300 : ℝ) / 1600 = 65 / 80 by norm_num,
    show ((1300 : ℝ) + 20) / 1600 = (65 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch065Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3129203427 / 1000000000000 : ℝ)
  | 1 => (-25524579 / 8000000000 : ℝ)
  | 2 => (-1626395647 / 500000000000 : ℝ)
  | 3 => (-3315869561 / 1000000000000 : ℝ)
  | 4 => (-1689908319 / 500000000000 : ℝ)
  | 5 => (-430580259 / 125000000000 : ℝ)
  | 6 => (-3510355499 / 1000000000000 : ℝ)
  | 7 => (-1788483321 / 500000000000 : ℝ)
  | 8 => (-3644485311 / 1000000000000 : ℝ)
  | 9 => (-1856460703 / 500000000000 : ℝ)
  | 10 => (-945571229 / 250000000000 : ℝ)
  | 11 => (-3852585921 / 1000000000000 : ℝ)
  | 12 => (-392383459 / 100000000000 : ℝ)
  | 13 => (-1998020593 / 500000000000 : ℝ)
  | 14 => (-2034608031 / 500000000000 : ℝ)
  | 15 => (-2071684833 / 500000000000 : ℝ)
  | 16 => (-4218512539 / 1000000000000 : ℝ)
  | 17 => (-858931063 / 200000000000 : ℝ)
  | 18 => (-174872349 / 40000000000 : ℝ)
  | 19 => (-2224991797 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch065Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1534337579 / 500000000000 : ℝ)
  | 1 => (-1564601713 / 500000000000 : ℝ)
  | 2 => (-1595286187 / 500000000000 : ℝ)
  | 3 => (-3252791293 / 1000000000000 : ℝ)
  | 4 => (-82896739 / 25000000000 : ℝ)
  | 5 => (-3379816637 / 1000000000000 : ℝ)
  | 6 => (-3444642071 / 1000000000000 : ℝ)
  | 7 => (-1755177749 / 500000000000 : ℝ)
  | 8 => (-3576966641 / 1000000000000 : ℝ)
  | 9 => (-364448531 / 100000000000 : ℝ)
  | 10 => (-742584281 / 200000000000 : ℝ)
  | 11 => (-756456983 / 200000000000 : ℝ)
  | 12 => (-12039331 / 3125000000 : ℝ)
  | 13 => (-3923834589 / 1000000000000 : ℝ)
  | 14 => (-799208237 / 200000000000 : ℝ)
  | 15 => (-4069216061 / 1000000000000 : ℝ)
  | 16 => (-828673933 / 200000000000 : ℝ)
  | 17 => (-2109256269 / 500000000000 : ℝ)
  | 18 => (-2147327657 / 500000000000 : ℝ)
  | 19 => (-1092952181 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch065Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1300 : ℝ) + (j.val : ℝ)) / 1600)
      (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch065Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch065Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1300 : ℝ) + (j.val : ℝ)) / 1600)
    (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch065Neg70WeightLower j.val) (hpThetaShiftThreeBatch065Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch065Neg70WeightLower, hpThetaShiftThreeBatch065Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch065Neg70_integral_bounds :
    (-13034959 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-6234741 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch065Lower hpThetaJensenCellsBatch065Upper
    hpThetaShiftThreeBatch065Neg70WeightLower hpThetaShiftThreeBatch065Neg70WeightUpper hpThetaJensenCellsBatch065_bounds hpThetaShiftThreeBatch065Neg70_weight_bounds
  have hl : (-13034959 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch065Lower j * hpThetaShiftThreeBatch065Neg70WeightLower j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftThreeBatch065Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftThreeBatch065Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch065Lower j * hpThetaShiftThreeBatch065Neg70WeightUpper j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftThreeBatch065Neg70WeightUpper j) / 1600) ≤ (-6234741 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftThreeBatch065Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1300 : ℝ) / 1600 = 65 / 80 by norm_num,
    show ((1300 : ℝ) + 20) / 1600 = (65 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch065Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (986362519 / 1000000000000 : ℝ)
  | 1 => (49630353 / 50000000000 : ℝ)
  | 2 => (249710883 / 250000000000 : ℝ)
  | 3 => (502535579 / 500000000000 : ℝ)
  | 4 => (252822287 / 250000000000 : ℝ)
  | 5 => (1017496703 / 1000000000000 : ℝ)
  | 6 => (1023693009 / 1000000000000 : ℝ)
  | 7 => (1029877241 / 1000000000000 : ℝ)
  | 8 => (259012141 / 250000000000 : ℝ)
  | 9 => (1042206129 / 1000000000000 : ℝ)
  | 10 => (1048349073 / 1000000000000 : ℝ)
  | 11 => (263619131 / 250000000000 : ℝ)
  | 12 => (265146899 / 250000000000 : ℝ)
  | 13 => (106668139 / 100000000000 : ℝ)
  | 14 => (536378497 / 500000000000 : ℝ)
  | 15 => (269703371 / 250000000000 : ℝ)
  | 16 => (542424961 / 500000000000 : ℝ)
  | 17 => (1090865357 / 1000000000000 : ℝ)
  | 18 => (548429413 / 500000000000 : ℝ)
  | 19 => (137853669 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch065Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (992607061 / 1000000000000 : ℝ)
  | 1 => (998843533 / 1000000000000 : ℝ)
  | 2 => (1005071159 / 1000000000000 : ℝ)
  | 3 => (1011289149 / 1000000000000 : ℝ)
  | 4 => (7949193 / 7812500000 : ℝ)
  | 5 => (102369301 / 100000000000 : ℝ)
  | 6 => (514938621 / 500000000000 : ℝ)
  | 7 => (207209713 / 200000000000 : ℝ)
  | 8 => (104220613 / 100000000000 : ℝ)
  | 9 => (524174537 / 500000000000 : ℝ)
  | 10 => (42179061 / 40000000000 : ℝ)
  | 11 => (1060587597 / 1000000000000 : ℝ)
  | 12 => (1066681391 / 1000000000000 : ℝ)
  | 13 => (214551399 / 200000000000 : ℝ)
  | 14 => (215762697 / 200000000000 : ℝ)
  | 15 => (1084849923 / 1000000000000 : ℝ)
  | 16 => (545432679 / 500000000000 : ℝ)
  | 17 => (1096858827 / 1000000000000 : ℝ)
  | 18 => (1102829353 / 1000000000000 : ℝ)
  | 19 => (1108775943 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch065Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1300 : ℝ) + (j.val : ℝ)) / 1600)
      (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch065Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch065Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1300 : ℝ) + (j.val : ℝ)) / 1600)
    (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch065Neg45WeightLower j.val) (hpThetaShiftThreeBatch065Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch065Neg45WeightLower, hpThetaShiftThreeBatch065Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch065Neg45_integral_bounds :
    (1776757 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (3667707 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch065Lower hpThetaJensenCellsBatch065Upper
    hpThetaShiftThreeBatch065Neg45WeightLower hpThetaShiftThreeBatch065Neg45WeightUpper hpThetaJensenCellsBatch065_bounds hpThetaShiftThreeBatch065Neg45_weight_bounds
  have hl : (1776757 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch065Lower j * hpThetaShiftThreeBatch065Neg45WeightLower j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftThreeBatch065Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftThreeBatch065Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch065Lower j * hpThetaShiftThreeBatch065Neg45WeightUpper j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftThreeBatch065Neg45WeightUpper j) / 1600) ≤ (3667707 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftThreeBatch065Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1300 : ℝ) / 1600 = 65 / 80 by norm_num,
    show ((1300 : ℝ) + 20) / 1600 = (65 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch065Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-31403859 / 125000000000 : ℝ)
  | 1 => (-62618687 / 250000000000 : ℝ)
  | 2 => (-124847319 / 500000000000 : ℝ)
  | 3 => (-248890327 / 1000000000000 : ℝ)
  | 4 => (-248061599 / 1000000000000 : ℝ)
  | 5 => (-61802059 / 250000000000 : ℝ)
  | 6 => (-12316501 / 50000000000 : ℝ)
  | 7 => (-245426731 / 1000000000000 : ℝ)
  | 8 => (-244498151 / 1000000000000 : ℝ)
  | 9 => (-243544057 / 1000000000000 : ℝ)
  | 10 => (-60641057 / 250000000000 : ℝ)
  | 11 => (-241558441 / 1000000000000 : ℝ)
  | 12 => (-240526471 / 1000000000000 : ℝ)
  | 13 => (-47893619 / 200000000000 : ℝ)
  | 14 => (-119191543 / 500000000000 : ℝ)
  | 15 => (-237271219 / 1000000000000 : ℝ)
  | 16 => (-29516533 / 125000000000 : ℝ)
  | 17 => (-46993199 / 200000000000 : ℝ)
  | 18 => (-233772181 / 1000000000000 : ℝ)
  | 19 => (-3633603 / 15625000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch065Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-250474747 / 1000000000000 : ℝ)
  | 1 => (-249694637 / 1000000000000 : ℝ)
  | 2 => (-124445163 / 500000000000 : ℝ)
  | 3 => (-124030799 / 500000000000 : ℝ)
  | 4 => (-49441647 / 200000000000 : ℝ)
  | 5 => (-246330019 / 1000000000000 : ℝ)
  | 6 => (-24542673 / 100000000000 : ℝ)
  | 7 => (-4889963 / 20000000000 : ℝ)
  | 8 => (-30443007 / 125000000000 : ℝ)
  | 9 => (-242564227 / 1000000000000 : ℝ)
  | 10 => (-6038961 / 25000000000 : ℝ)
  | 11 => (-24052647 / 100000000000 : ℝ)
  | 12 => (-119734047 / 500000000000 : ℝ)
  | 13 => (-47676617 / 200000000000 : ℝ)
  | 14 => (-118635609 / 500000000000 : ℝ)
  | 15 => (-236132263 / 1000000000000 : ℝ)
  | 16 => (-117482997 / 500000000000 : ℝ)
  | 17 => (-11688609 / 50000000000 : ℝ)
  | 18 => (-232550591 / 1000000000000 : ℝ)
  | 19 => (-57825249 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch065Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1300 : ℝ) + (j.val : ℝ)) / 1600)
      (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch065Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch065Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1300 : ℝ) + (j.val : ℝ)) / 1600)
    (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch065Neg25WeightLower j.val) (hpThetaShiftThreeBatch065Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch065Neg25WeightLower, hpThetaShiftThreeBatch065Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch065Neg25_integral_bounds :
    (-6811 / 8000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-826379 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch065Lower hpThetaJensenCellsBatch065Upper
    hpThetaShiftThreeBatch065Neg25WeightLower hpThetaShiftThreeBatch065Neg25WeightUpper hpThetaJensenCellsBatch065_bounds hpThetaShiftThreeBatch065Neg25_weight_bounds
  have hl : (-6811 / 8000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch065Lower j * hpThetaShiftThreeBatch065Neg25WeightLower j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftThreeBatch065Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftThreeBatch065Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch065Lower j * hpThetaShiftThreeBatch065Neg25WeightUpper j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftThreeBatch065Neg25WeightUpper j) / 1600) ≤ (-826379 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftThreeBatch065Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1300 : ℝ) / 1600 = 65 / 80 by norm_num,
    show ((1300 : ℝ) + 20) / 1600 = (65 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch065Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch065Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch065Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch065Neg25_integral_bounds
end HodgeProofHP
