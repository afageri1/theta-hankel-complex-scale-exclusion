/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch018

/-! Exact signed weight and batch integral certificates, batch 18 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch018Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5175184399 / 500000000000 : ℝ)
  | 1 => (-5233745029 / 500000000000 : ℝ)
  | 2 => (-5292144591 / 500000000000 : ℝ)
  | 3 => (-10700743327 / 1000000000000 : ℝ)
  | 4 => (-5408414721 / 500000000000 : ℝ)
  | 5 => (-10932524263 / 1000000000000 : ℝ)
  | 6 => (-11047804317 / 1000000000000 : ℝ)
  | 7 => (-5581322961 / 500000000000 : ℝ)
  | 8 => (-11277025187 / 1000000000000 : ℝ)
  | 9 => (-5695459007 / 500000000000 : ℝ)
  | 10 => (-11504300097 / 1000000000000 : ℝ)
  | 11 => (-11617146923 / 1000000000000 : ℝ)
  | 12 => (-5864716887 / 500000000000 : ℝ)
  | 13 => (-740070983 / 62500000000 : ℝ)
  | 14 => (-11952227657 / 1000000000000 : ℝ)
  | 15 => (-1206268423 / 100000000000 : ℝ)
  | 16 => (-3043119979 / 250000000000 : ℝ)
  | 17 => (-12281588979 / 1000000000000 : ℝ)
  | 18 => (-6194992743 / 500000000000 : ℝ)
  | 19 => (-12497643301 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch018Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1023294803 / 100000000000 : ℝ)
  | 1 => (-10350368797 / 1000000000000 : ℝ)
  | 2 => (-10467490057 / 1000000000000 : ℝ)
  | 3 => (-10584289181 / 1000000000000 : ℝ)
  | 4 => (-5350371663 / 500000000000 : ℝ)
  | 5 => (-10816829441 / 1000000000000 : ℝ)
  | 6 => (-5466262131 / 500000000000 : ℝ)
  | 7 => (-2761951079 / 250000000000 : ℝ)
  | 8 => (-11162645921 / 1000000000000 : ℝ)
  | 9 => (-5638512593 / 500000000000 : ℝ)
  | 10 => (-11390918013 / 1000000000000 : ℝ)
  | 11 => (-179754689 / 15625000000 : ℝ)
  | 12 => (-5808573461 / 500000000000 : ℝ)
  | 13 => (-11729433773 / 1000000000000 : ℝ)
  | 14 => (-11841135727 / 1000000000000 : ℝ)
  | 15 => (-1494028457 / 125000000000 : ℝ)
  | 16 => (-12062684229 / 1000000000000 : ℝ)
  | 17 => (-2434495983 / 200000000000 : ℝ)
  | 18 => (-6140794489 / 500000000000 : ℝ)
  | 19 => (-2477997097 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch018Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((360 : ℝ) + (j.val : ℝ)) / 1600)
      (((360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch018Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch018Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((360 : ℝ) + (j.val : ℝ)) / 1600)
    (((360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch018Neg100WeightLower j.val) (hpThetaShiftOneBatch018Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch018Neg100WeightLower, hpThetaShiftOneBatch018Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch018Neg100_integral_bounds :
    (-153262659289 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-18737541257 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch018Lower hpThetaJensenCellsBatch018Upper
    hpThetaShiftOneBatch018Neg100WeightLower hpThetaShiftOneBatch018Neg100WeightUpper hpThetaJensenCellsBatch018_bounds hpThetaShiftOneBatch018Neg100_weight_bounds
  have hl : (-153262659289 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch018Lower j * hpThetaShiftOneBatch018Neg100WeightLower j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftOneBatch018Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftOneBatch018Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch018Lower j * hpThetaShiftOneBatch018Neg100WeightUpper j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftOneBatch018Neg100WeightUpper j) / 1600) ≤ (-18737541257 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftOneBatch018Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (360 : ℝ) / 1600 = 18 / 80 by norm_num,
    show ((360 : ℝ) + 20) / 1600 = (18 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch018Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3821684989 / 1000000000000 : ℝ)
  | 1 => (-3940385567 / 1000000000000 : ℝ)
  | 2 => (-2029915449 / 500000000000 : ℝ)
  | 3 => (-4180014569 / 1000000000000 : ℝ)
  | 4 => (-2150465021 / 500000000000 : ℝ)
  | 5 => (-4422570651 / 1000000000000 : ℝ)
  | 6 => (-2272464799 / 500000000000 : ℝ)
  | 7 => (-4667999959 / 1000000000000 : ℝ)
  | 8 => (-4791774677 / 1000000000000 : ℝ)
  | 9 => (-614530821 / 125000000000 : ℝ)
  | 10 => (-2520704157 / 500000000000 : ℝ)
  | 11 => (-516725247 / 100000000000 : ℝ)
  | 12 => (-82715179 / 15625000000 : ℝ)
  | 13 => (-2710478781 / 500000000000 : ℝ)
  | 14 => (-5548802947 / 1000000000000 : ℝ)
  | 15 => (-1419324909 / 250000000000 : ℝ)
  | 16 => (-2903219761 / 500000000000 : ℝ)
  | 17 => (-1484053591 / 250000000000 : ℝ)
  | 18 => (-6066615789 / 1000000000000 : ℝ)
  | 19 => (-6197635289 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch018Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-740747089 / 200000000000 : ℝ)
  | 1 => (-955421247 / 250000000000 : ℝ)
  | 2 => (-1970192783 / 500000000000 : ℝ)
  | 3 => (-4059830897 / 1000000000000 : ℝ)
  | 4 => (-522501821 / 125000000000 : ℝ)
  | 5 => (-4300930041 / 1000000000000 : ℝ)
  | 6 => (-88451413 / 20000000000 : ℝ)
  | 7 => (-4544929597 / 1000000000000 : ℝ)
  | 8 => (-2333999979 / 500000000000 : ℝ)
  | 9 => (-1197943669 / 250000000000 : ℝ)
  | 10 => (-4916246567 / 1000000000000 : ℝ)
  | 11 => (-5041408313 / 1000000000000 : ℝ)
  | 12 => (-5167252469 / 1000000000000 : ℝ)
  | 13 => (-1058754291 / 200000000000 : ℝ)
  | 14 => (-5420957561 / 1000000000000 : ℝ)
  | 15 => (-2774401473 / 500000000000 : ℝ)
  | 16 => (-1135459927 / 200000000000 : ℝ)
  | 17 => (-5806439521 / 1000000000000 : ℝ)
  | 18 => (-5936214363 / 1000000000000 : ℝ)
  | 19 => (-1516653947 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch018Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((360 : ℝ) + (j.val : ℝ)) / 1600)
      (((360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch018Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch018Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((360 : ℝ) + (j.val : ℝ)) / 1600)
    (((360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch018Neg65WeightLower j.val) (hpThetaShiftOneBatch018Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch018Neg65WeightLower, hpThetaShiftOneBatch018Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch018Neg65_integral_bounds :
    (-66762025847 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-6429980557 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch018Lower hpThetaJensenCellsBatch018Upper
    hpThetaShiftOneBatch018Neg65WeightLower hpThetaShiftOneBatch018Neg65WeightUpper hpThetaJensenCellsBatch018_bounds hpThetaShiftOneBatch018Neg65_weight_bounds
  have hl : (-66762025847 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch018Lower j * hpThetaShiftOneBatch018Neg65WeightLower j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftOneBatch018Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftOneBatch018Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch018Lower j * hpThetaShiftOneBatch018Neg65WeightUpper j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftOneBatch018Neg65WeightUpper j) / 1600) ≤ (-6429980557 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftOneBatch018Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (360 : ℝ) / 1600 = 18 / 80 by norm_num,
    show ((360 : ℝ) + 20) / 1600 = (18 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch018Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (71243339 / 15625000000 : ℝ)
  | 1 => (449503441 / 100000000000 : ℝ)
  | 2 => (1107400691 / 250000000000 : ℝ)
  | 3 => (4363277247 / 1000000000000 : ℝ)
  | 4 => (4296056397 / 1000000000000 : ℝ)
  | 5 => (2113969401 / 500000000000 : ℝ)
  | 6 => (831784621 / 200000000000 : ℝ)
  | 7 => (4089007997 / 1000000000000 : ℝ)
  | 8 => (4018192221 / 1000000000000 : ℝ)
  | 9 => (246654661 / 62500000000 : ℝ)
  | 10 => (387385391 / 100000000000 : ℝ)
  | 11 => (950082281 / 250000000000 : ℝ)
  | 12 => (465737397 / 125000000000 : ℝ)
  | 13 => (3565003 / 976562500 : ℝ)
  | 14 => (3574319877 / 1000000000000 : ℝ)
  | 15 => (3497168707 / 1000000000000 : ℝ)
  | 16 => (683821747 / 200000000000 : ℝ)
  | 17 => (3340139187 / 1000000000000 : ℝ)
  | 18 => (652051869 / 200000000000 : ℝ)
  | 19 => (3179468547 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch018Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2311611093 / 500000000000 : ℝ)
  | 1 => (4559573697 / 1000000000000 : ℝ)
  | 2 => (4495034411 / 1000000000000 : ℝ)
  | 3 => (885920553 / 200000000000 : ℝ)
  | 4 => (68176207 / 15625000000 : ℝ)
  | 5 => (2148028199 / 500000000000 : ℝ)
  | 6 => (4227938803 / 1000000000000 : ℝ)
  | 7 => (2079461553 / 500000000000 : ℝ)
  | 8 => (2044503999 / 500000000000 : ℝ)
  | 9 => (2009096111 / 500000000000 : ℝ)
  | 10 => (3946474577 / 1000000000000 : ℝ)
  | 11 => (3873853911 / 1000000000000 : ℝ)
  | 12 => (30402633 / 8000000000 : ℝ)
  | 13 => (3725899177 / 1000000000000 : ℝ)
  | 14 => (3650563073 / 1000000000000 : ℝ)
  | 15 => (1787159939 / 500000000000 : ℝ)
  | 16 => (874292177 / 250000000000 : ℝ)
  | 17 => (26711787 / 7812500000 : ℝ)
  | 18 => (835034797 / 250000000000 : ℝ)
  | 19 => (1630129673 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch018Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((360 : ℝ) + (j.val : ℝ)) / 1600)
      (((360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch018Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch018Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((360 : ℝ) + (j.val : ℝ)) / 1600)
    (((360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch018Neg40WeightLower j.val) (hpThetaShiftOneBatch018Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch018Neg40WeightLower, hpThetaShiftOneBatch018Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch018Neg40_integral_bounds :
    (51697435301 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (2664984131 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch018Lower hpThetaJensenCellsBatch018Upper
    hpThetaShiftOneBatch018Neg40WeightLower hpThetaShiftOneBatch018Neg40WeightUpper hpThetaJensenCellsBatch018_bounds hpThetaShiftOneBatch018Neg40_weight_bounds
  have hl : (51697435301 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch018Lower j * hpThetaShiftOneBatch018Neg40WeightLower j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftOneBatch018Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftOneBatch018Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch018Lower j * hpThetaShiftOneBatch018Neg40WeightUpper j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftOneBatch018Neg40WeightUpper j) / 1600) ≤ (2664984131 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftOneBatch018Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (360 : ℝ) / 1600 = 18 / 80 by norm_num,
    show ((360 : ℝ) + 20) / 1600 = (18 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch018Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (6882116059 / 500000000000 : ℝ)
  | 1 => (13783148509 / 1000000000000 : ℝ)
  | 2 => (3450388087 / 250000000000 : ℝ)
  | 3 => (6909720083 / 500000000000 : ℝ)
  | 4 => (6918404249 / 500000000000 : ℝ)
  | 5 => (13853653889 / 1000000000000 : ℝ)
  | 6 => (1733746611 / 125000000000 : ℝ)
  | 7 => (3471440513 / 250000000000 : ℝ)
  | 8 => (1737627243 / 125000000000 : ℝ)
  | 9 => (13915737137 / 1000000000000 : ℝ)
  | 10 => (870619763 / 62500000000 : ℝ)
  | 11 => (54466999 / 3906250000 : ℝ)
  | 12 => (13956640339 / 1000000000000 : ℝ)
  | 13 => (13969178593 / 1000000000000 : ℝ)
  | 14 => (2796232623 / 200000000000 : ℝ)
  | 15 => (13992590523 / 1000000000000 : ℝ)
  | 16 => (7001728721 / 500000000000 : ℝ)
  | 17 => (2802752101 / 200000000000 : ℝ)
  | 18 => (14023496353 / 1000000000000 : ℝ)
  | 19 => (14032661637 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch018Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1378314851 / 100000000000 : ℝ)
  | 1 => (13801552349 / 1000000000000 : ℝ)
  | 2 => (13819440167 / 1000000000000 : ℝ)
  | 3 => (13836808499 / 1000000000000 : ℝ)
  | 4 => (1385365389 / 100000000000 : ℝ)
  | 5 => (13869972889 / 1000000000000 : ℝ)
  | 6 => (13885762053 / 1000000000000 : ℝ)
  | 7 => (2780203589 / 200000000000 : ℝ)
  | 8 => (6957868569 / 500000000000 : ℝ)
  | 9 => (13929916209 / 1000000000000 : ℝ)
  | 10 => (2788710349 / 200000000000 : ℝ)
  | 11 => (697832017 / 50000000000 : ℝ)
  | 12 => (6984589297 / 500000000000 : ℝ)
  | 13 => (3495290779 / 250000000000 : ℝ)
  | 14 => (3498147631 / 250000000000 : ℝ)
  | 15 => (14003457443 / 1000000000000 : ℝ)
  | 16 => (7006880253 / 500000000000 : ℝ)
  | 17 => (7011748177 / 500000000000 : ℝ)
  | 18 => (7016330819 / 500000000000 : ℝ)
  | 19 => (2808250603 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch018Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((360 : ℝ) + (j.val : ℝ)) / 1600)
      (((360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch018Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch018Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((360 : ℝ) + (j.val : ℝ)) / 1600)
    (((360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch018Neg20WeightLower j.val) (hpThetaShiftOneBatch018Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch018Neg20WeightLower, hpThetaShiftOneBatch018Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch018Neg20_integral_bounds :
    (3686305949 / 20000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (186767591119 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch018Lower hpThetaJensenCellsBatch018Upper
    hpThetaShiftOneBatch018Neg20WeightLower hpThetaShiftOneBatch018Neg20WeightUpper hpThetaJensenCellsBatch018_bounds hpThetaShiftOneBatch018Neg20_weight_bounds
  have hl : (3686305949 / 20000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch018Lower j * hpThetaShiftOneBatch018Neg20WeightLower j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftOneBatch018Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftOneBatch018Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch018Lower j * hpThetaShiftOneBatch018Neg20WeightUpper j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftOneBatch018Neg20WeightUpper j) / 1600) ≤ (186767591119 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftOneBatch018Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (360 : ℝ) / 1600 = 18 / 80 by norm_num,
    show ((360 : ℝ) + 20) / 1600 = (18 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch018Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch018Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch018Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch018Neg20_integral_bounds
end HodgeProofHP
