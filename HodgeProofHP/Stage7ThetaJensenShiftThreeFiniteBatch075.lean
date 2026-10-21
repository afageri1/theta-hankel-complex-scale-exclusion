/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch075

/-! Exact signed weight and batch integral certificates, batch 75 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch075Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-138050463581 / 500000000000 : ℝ)
  | 1 => (-27875471379 / 100000000000 : ℝ)
  | 2 => (-281431256621 / 1000000000000 : ℝ)
  | 3 => (-284130728933 / 1000000000000 : ℝ)
  | 4 => (-286853305167 / 1000000000000 : ℝ)
  | 5 => (-144799580467 / 500000000000 : ℝ)
  | 6 => (-292368473021 / 1000000000000 : ℝ)
  | 7 => (-147580709701 / 500000000000 : ℝ)
  | 8 => (-74494544809 / 250000000000 : ℝ)
  | 9 => (-60163786577 / 200000000000 : ℝ)
  | 10 => (-303683861913 / 1000000000000 : ℝ)
  | 11 => (-61314629819 / 200000000000 : ℝ)
  | 12 => (-12379479137 / 40000000000 : ℝ)
  | 13 => (-2499404281 / 8000000000 : ℝ)
  | 14 => (-157694502823 / 500000000000 : ℝ)
  | 15 => (-159188788841 / 500000000000 : ℝ)
  | 16 => (-80347860043 / 250000000000 : ℝ)
  | 17 => (-20276923957 / 62500000000 : ℝ)
  | 18 => (-327495798557 / 1000000000000 : ℝ)
  | 19 => (-330586678633 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch075Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-136734862307 / 500000000000 : ℝ)
  | 1 => (-276100927161 / 1000000000000 : ℝ)
  | 2 => (-278754713789 / 1000000000000 : ℝ)
  | 3 => (-14071562831 / 50000000000 : ℝ)
  | 4 => (-71032682233 / 250000000000 : ℝ)
  | 5 => (-143426652583 / 500000000000 : ℝ)
  | 6 => (-289599160933 / 1000000000000 : ℝ)
  | 7 => (-14618423651 / 50000000000 : ℝ)
  | 8 => (-295161419401 / 1000000000000 : ℝ)
  | 9 => (-59595635847 / 200000000000 : ℝ)
  | 10 => (-75204733221 / 250000000000 : ℝ)
  | 11 => (-37960482739 / 125000000000 : ℝ)
  | 12 => (-153286574547 / 500000000000 : ℝ)
  | 13 => (-38685872303 / 125000000000 : ℝ)
  | 14 => (-78106383781 / 250000000000 : ℝ)
  | 15 => (-63077801129 / 200000000000 : ℝ)
  | 16 => (-318377577681 / 1000000000000 : ℝ)
  | 17 => (-321391440171 / 1000000000000 : ℝ)
  | 18 => (-324430783311 / 1000000000000 : ℝ)
  | 19 => (-81873949639 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch075Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1500 : ℝ) + (j.val : ℝ)) / 1600)
      (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch075Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch075Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1500 : ℝ) + (j.val : ℝ)) / 1600)
    (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch075Neg100WeightLower j.val) (hpThetaShiftThreeBatch075Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch075Neg100WeightLower, hpThetaShiftThreeBatch075Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch075Neg100_integral_bounds :
    (-19325211 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-3709891 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch075Lower hpThetaJensenCellsBatch075Upper
    hpThetaShiftThreeBatch075Neg100WeightLower hpThetaShiftThreeBatch075Neg100WeightUpper hpThetaJensenCellsBatch075_bounds hpThetaShiftThreeBatch075Neg100_weight_bounds
  have hl : (-19325211 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch075Lower j * hpThetaShiftThreeBatch075Neg100WeightLower j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftThreeBatch075Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftThreeBatch075Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch075Lower j * hpThetaShiftThreeBatch075Neg100WeightUpper j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftThreeBatch075Neg100WeightUpper j) / 1600) ≤ (-3709891 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftThreeBatch075Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1500 : ℝ) / 1600 = 75 / 80 by norm_num,
    show ((1500 : ℝ) + 20) / 1600 = (75 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch075Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-13054885337 / 250000000000 : ℝ)
  | 1 => (-10560931201 / 200000000000 : ℝ)
  | 2 => (-26697694231 / 500000000000 : ℝ)
  | 3 => (-53991785333 / 1000000000000 : ℝ)
  | 4 => (-13648473391 / 250000000000 : ℝ)
  | 5 => (-55201760439 / 1000000000000 : ℝ)
  | 6 => (-2790771679 / 50000000000 : ℝ)
  | 7 => (-14108740237 / 250000000000 : ℝ)
  | 8 => (-57060390849 / 1000000000000 : ℝ)
  | 9 => (-14422942983 / 250000000000 : ℝ)
  | 10 => (-11665830639 / 200000000000 : ℝ)
  | 11 => (-29486291991 / 500000000000 : ℝ)
  | 12 => (-5962211399 / 100000000000 : ℝ)
  | 13 => (-6027779327 / 100000000000 : ℝ)
  | 14 => (-15234918057 / 250000000000 : ℝ)
  | 15 => (-30803900813 / 500000000000 : ℝ)
  | 16 => (-62282232587 / 1000000000000 : ℝ)
  | 17 => (-62963016597 / 1000000000000 : ℝ)
  | 18 => (-12730041101 / 200000000000 : ℝ)
  | 19 => (-32171925763 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch075Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-12909999553 / 250000000000 : ℝ)
  | 1 => (-52219541347 / 1000000000000 : ℝ)
  | 2 => (-13201164001 / 250000000000 : ℝ)
  | 3 => (-53395388461 / 1000000000000 : ℝ)
  | 4 => (-13497946333 / 250000000000 : ℝ)
  | 5 => (-54593893563 / 1000000000000 : ℝ)
  | 6 => (-27600880219 / 500000000000 : ℝ)
  | 7 => (-55815433579 / 1000000000000 : ℝ)
  | 8 => (-56434960947 / 1000000000000 : ℝ)
  | 9 => (-891568607 / 15625000000 : ℝ)
  | 10 => (-57691771931 / 1000000000000 : ℝ)
  | 11 => (-29164576597 / 500000000000 : ℝ)
  | 12 => (-58972583981 / 1000000000000 : ℝ)
  | 13 => (-59622113989 / 1000000000000 : ℝ)
  | 14 => (-60277793269 / 1000000000000 : ℝ)
  | 15 => (-60939672227 / 1000000000000 : ℝ)
  | 16 => (-492862413 / 8000000000 : ℝ)
  | 17 => (-31141116293 / 500000000000 : ℝ)
  | 18 => (-15740754149 / 250000000000 : ℝ)
  | 19 => (-994534461 / 15625000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch075Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1500 : ℝ) + (j.val : ℝ)) / 1600)
      (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch075Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch075Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1500 : ℝ) + (j.val : ℝ)) / 1600)
    (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch075Neg70WeightLower j.val) (hpThetaShiftThreeBatch075Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch075Neg70WeightLower, hpThetaShiftThreeBatch075Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch075Neg70_integral_bounds :
    (-3706213 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-1776021 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch075Lower hpThetaJensenCellsBatch075Upper
    hpThetaShiftThreeBatch075Neg70WeightLower hpThetaShiftThreeBatch075Neg70WeightUpper hpThetaJensenCellsBatch075_bounds hpThetaShiftThreeBatch075Neg70_weight_bounds
  have hl : (-3706213 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch075Lower j * hpThetaShiftThreeBatch075Neg70WeightLower j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftThreeBatch075Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftThreeBatch075Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch075Lower j * hpThetaShiftThreeBatch075Neg70WeightUpper j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftThreeBatch075Neg70WeightUpper j) / 1600) ≤ (-1776021 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftThreeBatch075Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1500 : ℝ) / 1600 = 75 / 80 by norm_num,
    show ((1500 : ℝ) + 20) / 1600 = (75 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch075Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-425121 / 4000000000 : ℝ)
  | 1 => (-17875529 / 125000000000 : ℝ)
  | 2 => (-180349579 / 1000000000000 : ℝ)
  | 3 => (-54580807 / 250000000000 : ℝ)
  | 4 => (-128466089 / 500000000000 : ℝ)
  | 5 => (-296183487 / 1000000000000 : ℝ)
  | 6 => (-336084273 / 1000000000000 : ℝ)
  | 7 => (-376641719 / 1000000000000 : ℝ)
  | 8 => (-83572613 / 200000000000 : ℝ)
  | 9 => (-14367363 / 31250000000 : ℝ)
  | 10 => (-502326739 / 1000000000000 : ℝ)
  | 11 => (-68197983 / 125000000000 : ℝ)
  | 12 => (-117906897 / 200000000000 : ℝ)
  | 13 => (-634186159 / 1000000000000 : ℝ)
  | 14 => (-679546507 / 1000000000000 : ℝ)
  | 15 => (-725623217 / 1000000000000 : ℝ)
  | 16 => (-772424039 / 1000000000000 : ℝ)
  | 17 => (-102494599 / 125000000000 : ℝ)
  | 18 => (-10852867 / 12500000000 : ℝ)
  | 19 => (-917249691 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch075Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-70170753 / 1000000000000 : ℝ)
  | 1 => (-106280249 / 1000000000000 : ℝ)
  | 2 => (-143004231 / 1000000000000 : ℝ)
  | 3 => (-90174789 / 500000000000 : ℝ)
  | 4 => (-218323227 / 1000000000000 : ℝ)
  | 5 => (-256932177 / 1000000000000 : ℝ)
  | 6 => (-148091743 / 500000000000 : ℝ)
  | 7 => (-21005267 / 62500000000 : ℝ)
  | 8 => (-188320859 / 500000000000 : ℝ)
  | 9 => (-52232883 / 125000000000 : ℝ)
  | 10 => (-91951123 / 200000000000 : ℝ)
  | 11 => (-251163369 / 500000000000 : ℝ)
  | 12 => (-545583863 / 1000000000000 : ℝ)
  | 13 => (-147383621 / 250000000000 : ℝ)
  | 14 => (-317093079 / 500000000000 : ℝ)
  | 15 => (-339773253 / 500000000000 : ℝ)
  | 16 => (-45351451 / 62500000000 : ℝ)
  | 17 => (-386212019 / 500000000000 : ℝ)
  | 18 => (-819956791 / 1000000000000 : ℝ)
  | 19 => (-868229359 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch075Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1500 : ℝ) + (j.val : ℝ)) / 1600)
      (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch075Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch075Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1500 : ℝ) + (j.val : ℝ)) / 1600)
    (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch075Neg45WeightLower j.val) (hpThetaShiftThreeBatch075Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch075Neg45WeightLower, hpThetaShiftThreeBatch075Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch075Neg45_integral_bounds :
    (-29579 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-26051 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch075Lower hpThetaJensenCellsBatch075Upper
    hpThetaShiftThreeBatch075Neg45WeightLower hpThetaShiftThreeBatch075Neg45WeightUpper hpThetaJensenCellsBatch075_bounds hpThetaShiftThreeBatch075Neg45_weight_bounds
  have hl : (-29579 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch075Lower j * hpThetaShiftThreeBatch075Neg45WeightLower j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftThreeBatch075Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftThreeBatch075Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch075Lower j * hpThetaShiftThreeBatch075Neg45WeightUpper j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftThreeBatch075Neg45WeightUpper j) / 1600) ≤ (-26051 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftThreeBatch075Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1500 : ℝ) / 1600 = 75 / 80 by norm_num,
    show ((1500 : ℝ) + 20) / 1600 = (75 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch075Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (711081957 / 1000000000000 : ℝ)
  | 1 => (72185839 / 100000000000 : ℝ)
  | 2 => (146542621 / 200000000000 : ℝ)
  | 3 => (743646353 / 1000000000000 : ℝ)
  | 4 => (377329191 / 500000000000 : ℝ)
  | 5 => (765749439 / 1000000000000 : ℝ)
  | 6 => (776919769 / 1000000000000 : ℝ)
  | 7 => (49260601 / 62500000000 : ℝ)
  | 8 => (799499221 / 1000000000000 : ℝ)
  | 9 => (32436353 / 40000000000 : ℝ)
  | 10 => (822398667 / 1000000000000 : ℝ)
  | 11 => (104246123 / 125000000000 : ℝ)
  | 12 => (84562001 / 100000000000 : ℝ)
  | 13 => (857351979 / 1000000000000 : ℝ)
  | 14 => (869165123 / 1000000000000 : ℝ)
  | 15 => (881059671 / 1000000000000 : ℝ)
  | 16 => (893035851 / 1000000000000 : ℝ)
  | 17 => (3535523 / 3906250000 : ℝ)
  | 18 => (458617003 / 500000000000 : ℝ)
  | 19 => (232364107 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch075Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (721858391 / 1000000000000 : ℝ)
  | 1 => (366356553 / 500000000000 : ℝ)
  | 2 => (371823177 / 500000000000 : ℝ)
  | 3 => (754658383 / 1000000000000 : ℝ)
  | 4 => (2392967 / 3125000000 : ℝ)
  | 5 => (77691977 / 100000000000 : ℝ)
  | 6 => (788169617 / 1000000000000 : ℝ)
  | 7 => (399749611 / 500000000000 : ℝ)
  | 8 => (405454413 / 500000000000 : ℝ)
  | 9 => (205599667 / 250000000000 : ℝ)
  | 10 => (166793797 / 200000000000 : ℝ)
  | 11 => (845620011 / 1000000000000 : ℝ)
  | 12 => (42867599 / 50000000000 : ℝ)
  | 13 => (217291281 / 250000000000 : ℝ)
  | 14 => (110132459 / 125000000000 : ℝ)
  | 15 => (223258963 / 250000000000 : ℝ)
  | 16 => (905093889 / 1000000000000 : ℝ)
  | 17 => (917234007 / 1000000000000 : ℝ)
  | 18 => (929456429 / 1000000000000 : ℝ)
  | 19 => (941761373 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch075Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1500 : ℝ) + (j.val : ℝ)) / 1600)
      (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch075Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch075Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1500 : ℝ) + (j.val : ℝ)) / 1600)
    (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch075Neg25WeightLower j.val) (hpThetaShiftThreeBatch075Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch075Neg25WeightLower, hpThetaShiftThreeBatch075Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch075Neg25_integral_bounds :
    (50433 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (10557 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch075Lower hpThetaJensenCellsBatch075Upper
    hpThetaShiftThreeBatch075Neg25WeightLower hpThetaShiftThreeBatch075Neg25WeightUpper hpThetaJensenCellsBatch075_bounds hpThetaShiftThreeBatch075Neg25_weight_bounds
  have hl : (50433 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch075Lower j * hpThetaShiftThreeBatch075Neg25WeightLower j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftThreeBatch075Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftThreeBatch075Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch075Lower j * hpThetaShiftThreeBatch075Neg25WeightUpper j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftThreeBatch075Neg25WeightUpper j) / 1600) ≤ (10557 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftThreeBatch075Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1500 : ℝ) / 1600 = 75 / 80 by norm_num,
    show ((1500 : ℝ) + 20) / 1600 = (75 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch075Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch075Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch075Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch075Neg25_integral_bounds
end HodgeProofHP
