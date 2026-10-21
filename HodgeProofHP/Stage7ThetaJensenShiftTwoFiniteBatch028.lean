/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch028

/-! Exact signed weight and batch integral certificates, batch 28 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch028Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-47231043 / 200000000000 : ℝ)
  | 1 => (-235273579 / 1000000000000 : ℝ)
  | 2 => (-3661351 / 15625000000 : ℝ)
  | 3 => (-2916411 / 12500000000 : ℝ)
  | 4 => (-232231827 / 1000000000000 : ℝ)
  | 5 => (-231082303 / 1000000000000 : ℝ)
  | 6 => (-229863301 / 1000000000000 : ℝ)
  | 7 => (-114286903 / 500000000000 : ℝ)
  | 8 => (-113606401 / 500000000000 : ℝ)
  | 9 => (-45155853 / 200000000000 : ℝ)
  | 10 => (-224272167 / 1000000000000 : ℝ)
  | 11 => (-222690477 / 1000000000000 : ℝ)
  | 12 => (-221033157 / 1000000000000 : ℝ)
  | 13 => (-43859833 / 200000000000 : ℝ)
  | 14 => (-6796483 / 31250000000 : ℝ)
  | 15 => (-215596979 / 1000000000000 : ℝ)
  | 16 => (-5340667 / 25000000000 : ℝ)
  | 17 => (-211575501 / 1000000000000 : ℝ)
  | 18 => (-209442377 / 1000000000000 : ℝ)
  | 19 => (-207226243 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch028Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-117636789 / 500000000000 : ℝ)
  | 1 => (-234326463 / 1000000000000 : ℝ)
  | 2 => (-233312879 / 1000000000000 : ℝ)
  | 3 => (-116115913 / 500000000000 : ℝ)
  | 4 => (-115541151 / 500000000000 : ℝ)
  | 5 => (-2298633 / 10000000000 : ℝ)
  | 6 => (-45714761 / 200000000000 : ℝ)
  | 7 => (-227212801 / 1000000000000 : ℝ)
  | 8 => (-3527801 / 15625000000 : ℝ)
  | 9 => (-112136083 / 500000000000 : ℝ)
  | 10 => (-55672619 / 250000000000 : ℝ)
  | 11 => (-55258289 / 250000000000 : ℝ)
  | 12 => (-54824791 / 250000000000 : ℝ)
  | 13 => (-43497491 / 200000000000 : ℝ)
  | 14 => (-107798489 / 500000000000 : ℝ)
  | 15 => (-213626679 / 1000000000000 : ℝ)
  | 16 => (-423151 / 2000000000 : ℝ)
  | 17 => (-26180297 / 125000000000 : ℝ)
  | 18 => (-103613121 / 500000000000 : ℝ)
  | 19 => (-51231507 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch028Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((560 : ℝ) + (j.val : ℝ)) / 1600)
      (((560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch028Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch028Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((560 : ℝ) + (j.val : ℝ)) / 1600)
    (((560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch028Neg100WeightLower j.val) (hpThetaShiftTwoBatch028Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch028Neg100WeightLower, hpThetaShiftTwoBatch028Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch028Neg100_integral_bounds :
    (-2802999 / 2000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-1372688269 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch028Lower hpThetaJensenCellsBatch028Upper
    hpThetaShiftTwoBatch028Neg100WeightLower hpThetaShiftTwoBatch028Neg100WeightUpper hpThetaJensenCellsBatch028_bounds hpThetaShiftTwoBatch028Neg100_weight_bounds
  have hl : (-2802999 / 2000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch028Lower j * hpThetaShiftTwoBatch028Neg100WeightLower j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftTwoBatch028Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftTwoBatch028Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch028Lower j * hpThetaShiftTwoBatch028Neg100WeightUpper j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftTwoBatch028Neg100WeightUpper j) / 1600) ≤ (-1372688269 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftTwoBatch028Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (560 : ℝ) / 1600 = 28 / 80 by norm_num,
    show ((560 : ℝ) + 20) / 1600 = (28 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch028Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-29149819 / 100000000000 : ℝ)
  | 1 => (-73695829 / 250000000000 : ℝ)
  | 2 => (-74518537 / 250000000000 : ℝ)
  | 3 => (-75342579 / 250000000000 : ℝ)
  | 4 => (-304671449 / 1000000000000 : ℝ)
  | 5 => (-307977167 / 1000000000000 : ℝ)
  | 6 => (-311287087 / 1000000000000 : ℝ)
  | 7 => (-314600819 / 1000000000000 : ℝ)
  | 8 => (-317917967 / 1000000000000 : ℝ)
  | 9 => (-32123813 / 100000000000 : ℝ)
  | 10 => (-324560899 / 1000000000000 : ℝ)
  | 11 => (-327885863 / 1000000000000 : ℝ)
  | 12 => (-331212601 / 1000000000000 : ℝ)
  | 13 => (-334540689 / 1000000000000 : ℝ)
  | 14 => (-337869697 / 1000000000000 : ℝ)
  | 15 => (-170599593 / 500000000000 : ℝ)
  | 16 => (-68905743 / 200000000000 : ℝ)
  | 17 => (-173928917 / 500000000000 : ℝ)
  | 18 => (-43898261 / 125000000000 : ℝ)
  | 19 => (-354513017 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch028Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-36027391 / 125000000000 : ℝ)
  | 1 => (-291498189 / 1000000000000 : ℝ)
  | 2 => (-58956663 / 200000000000 : ℝ)
  | 3 => (-298074147 / 1000000000000 : ℝ)
  | 4 => (-60274063 / 200000000000 : ℝ)
  | 5 => (-38083931 / 125000000000 : ℝ)
  | 6 => (-153988583 / 500000000000 : ℝ)
  | 7 => (-155643543 / 500000000000 : ℝ)
  | 8 => (-157300409 / 500000000000 : ℝ)
  | 9 => (-158958983 / 500000000000 : ℝ)
  | 10 => (-321238129 / 1000000000000 : ℝ)
  | 11 => (-162280449 / 500000000000 : ℝ)
  | 12 => (-163942931 / 500000000000 : ℝ)
  | 13 => (-1656063 / 5000000000 : ℝ)
  | 14 => (-20908793 / 62500000000 : ℝ)
  | 15 => (-2639607 / 7812500000 : ℝ)
  | 16 => (-68239837 / 200000000000 : ℝ)
  | 17 => (-172264357 / 500000000000 : ℝ)
  | 18 => (-347857833 / 1000000000000 : ℝ)
  | 19 => (-351186087 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch028Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((560 : ℝ) + (j.val : ℝ)) / 1600)
      (((560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch028Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch028Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((560 : ℝ) + (j.val : ℝ)) / 1600)
    (((560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch028Neg65WeightLower j.val) (hpThetaShiftTwoBatch028Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch028Neg65WeightLower, hpThetaShiftTwoBatch028Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch028Neg65_integral_bounds :
    (-2016801249 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-984319829 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch028Lower hpThetaJensenCellsBatch028Upper
    hpThetaShiftTwoBatch028Neg65WeightLower hpThetaShiftTwoBatch028Neg65WeightUpper hpThetaJensenCellsBatch028_bounds hpThetaShiftTwoBatch028Neg65_weight_bounds
  have hl : (-2016801249 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch028Lower j * hpThetaShiftTwoBatch028Neg65WeightLower j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftTwoBatch028Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftTwoBatch028Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch028Lower j * hpThetaShiftTwoBatch028Neg65WeightUpper j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftTwoBatch028Neg65WeightUpper j) / 1600) ≤ (-984319829 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftTwoBatch028Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (560 : ℝ) / 1600 = 28 / 80 by norm_num,
    show ((560 : ℝ) + 20) / 1600 = (28 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch028Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2795339 / 31250000000 : ℝ)
  | 1 => (-92570513 / 1000000000000 : ℝ)
  | 2 => (-47859327 / 500000000000 : ℝ)
  | 3 => (-98895291 / 1000000000000 : ℝ)
  | 4 => (-2552511 / 25000000000 : ℝ)
  | 5 => (-21066823 / 200000000000 : ℝ)
  | 6 => (-13574541 / 125000000000 : ℝ)
  | 7 => (-111887087 / 1000000000000 : ℝ)
  | 8 => (-115206399 / 1000000000000 : ℝ)
  | 9 => (-29638567 / 250000000000 : ℝ)
  | 10 => (-60965347 / 500000000000 : ℝ)
  | 11 => (-62667839 / 500000000000 : ℝ)
  | 12 => (-64384607 / 500000000000 : ℝ)
  | 13 => (-26446259 / 200000000000 : ℝ)
  | 14 => (-16965239 / 125000000000 : ℝ)
  | 15 => (-34810263 / 250000000000 : ℝ)
  | 16 => (-142788701 / 1000000000000 : ℝ)
  | 17 => (-146364841 / 1000000000000 : ℝ)
  | 18 => (-2999389 / 20000000000 : ℝ)
  | 19 => (-19200313 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch028Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-86359637 / 1000000000000 : ℝ)
  | 1 => (-89450847 / 1000000000000 : ℝ)
  | 2 => (-5785657 / 62500000000 : ℝ)
  | 3 => (-95718653 / 1000000000000 : ℝ)
  | 4 => (-9889529 / 100000000000 : ℝ)
  | 5 => (-102100439 / 1000000000000 : ℝ)
  | 6 => (-52667057 / 500000000000 : ℝ)
  | 7 => (-108596327 / 1000000000000 : ℝ)
  | 8 => (-55943543 / 500000000000 : ℝ)
  | 9 => (-57603199 / 500000000000 : ℝ)
  | 10 => (-118554267 / 1000000000000 : ℝ)
  | 11 => (-121930693 / 1000000000000 : ℝ)
  | 12 => (-125335677 / 1000000000000 : ℝ)
  | 13 => (-128769213 / 1000000000000 : ℝ)
  | 14 => (-66115647 / 500000000000 : ℝ)
  | 15 => (-135721911 / 1000000000000 : ℝ)
  | 16 => (-139241051 / 1000000000000 : ℝ)
  | 17 => (-1427887 / 10000000000 : ℝ)
  | 18 => (-3659121 / 25000000000 : ℝ)
  | 19 => (-149969449 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch028Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((560 : ℝ) + (j.val : ℝ)) / 1600)
      (((560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch028Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch028Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((560 : ℝ) + (j.val : ℝ)) / 1600)
    (((560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch028Neg45WeightLower j.val) (hpThetaShiftTwoBatch028Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch028Neg45WeightLower, hpThetaShiftTwoBatch028Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch028Neg45_integral_bounds :
    (-187934769 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-720690321 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch028Lower hpThetaJensenCellsBatch028Upper
    hpThetaShiftTwoBatch028Neg45WeightLower hpThetaShiftTwoBatch028Neg45WeightUpper hpThetaJensenCellsBatch028_bounds hpThetaShiftTwoBatch028Neg45_weight_bounds
  have hl : (-187934769 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch028Lower j * hpThetaShiftTwoBatch028Neg45WeightLower j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftTwoBatch028Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftTwoBatch028Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch028Lower j * hpThetaShiftTwoBatch028Neg45WeightUpper j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftTwoBatch028Neg45WeightUpper j) / 1600) ≤ (-720690321 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftTwoBatch028Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (560 : ℝ) / 1600 = 28 / 80 by norm_num,
    show ((560 : ℝ) + 20) / 1600 = (28 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch028Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (338624437 / 1000000000000 : ℝ)
  | 1 => (541681 / 1600000000 : ℝ)
  | 2 => (8461379 / 25000000000 : ℝ)
  | 3 => (6766757 / 20000000000 : ℝ)
  | 4 => (169099251 / 500000000000 : ℝ)
  | 5 => (169018461 / 500000000000 : ℝ)
  | 6 => (337852917 / 1000000000000 : ℝ)
  | 7 => (168823147 / 500000000000 : ℝ)
  | 8 => (168708429 / 500000000000 : ℝ)
  | 9 => (67432883 / 200000000000 : ℝ)
  | 10 => (336888771 / 1000000000000 : ℝ)
  | 11 => (33658973 / 100000000000 : ℝ)
  | 12 => (336267097 / 1000000000000 : ℝ)
  | 13 => (335920677 / 1000000000000 : ℝ)
  | 14 => (13422011 / 40000000000 : ℝ)
  | 15 => (67031139 / 200000000000 : ℝ)
  | 16 => (16736837 / 50000000000 : ℝ)
  | 17 => (66858643 / 200000000000 : ℝ)
  | 18 => (333824923 / 1000000000000 : ℝ)
  | 19 => (83332917 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch028Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (33867679 / 100000000000 : ℝ)
  | 1 => (169312219 / 500000000000 : ℝ)
  | 2 => (169275313 / 500000000000 : ℝ)
  | 3 => (338455161 / 1000000000000 : ℝ)
  | 4 => (338337851 / 1000000000000 : ℝ)
  | 5 => (338198503 / 1000000000000 : ℝ)
  | 6 => (338036923 / 1000000000000 : ℝ)
  | 7 => (168926459 / 500000000000 : ℝ)
  | 8 => (67529259 / 200000000000 : ℝ)
  | 9 => (337416859 / 1000000000000 : ℝ)
  | 10 => (2634097 / 7812500000 : ℝ)
  | 11 => (84222193 / 250000000000 : ℝ)
  | 12 => (336589731 / 1000000000000 : ℝ)
  | 13 => (168133549 / 500000000000 : ℝ)
  | 14 => (167960339 / 500000000000 : ℝ)
  | 15 => (83887569 / 250000000000 : ℝ)
  | 16 => (20947231 / 62500000000 : ℝ)
  | 17 => (334736741 / 1000000000000 : ℝ)
  | 18 => (10446663 / 31250000000 : ℝ)
  | 19 => (83456231 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch028Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((560 : ℝ) + (j.val : ℝ)) / 1600)
      (((560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch028Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch028Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((560 : ℝ) + (j.val : ℝ)) / 1600)
    (((560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch028Neg25WeightLower j.val) (hpThetaShiftTwoBatch028Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch028Neg25WeightLower, hpThetaShiftTwoBatch028Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch028Neg25_integral_bounds :
    (207718307 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (263470747 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch028Lower hpThetaJensenCellsBatch028Upper
    hpThetaShiftTwoBatch028Neg25WeightLower hpThetaShiftTwoBatch028Neg25WeightUpper hpThetaJensenCellsBatch028_bounds hpThetaShiftTwoBatch028Neg25_weight_bounds
  have hl : (207718307 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch028Lower j * hpThetaShiftTwoBatch028Neg25WeightLower j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftTwoBatch028Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftTwoBatch028Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch028Lower j * hpThetaShiftTwoBatch028Neg25WeightUpper j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftTwoBatch028Neg25WeightUpper j) / 1600) ≤ (263470747 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftTwoBatch028Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (560 : ℝ) / 1600 = 28 / 80 by norm_num,
    show ((560 : ℝ) + 20) / 1600 = (28 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch028Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch028Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch028Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch028Neg25_integral_bounds
end HodgeProofHP
