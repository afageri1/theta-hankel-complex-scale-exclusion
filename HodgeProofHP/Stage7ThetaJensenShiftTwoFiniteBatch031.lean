/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch031

/-! Exact signed weight and batch integral certificates, batch 31 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch031Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-31348453 / 1000000000000 : ℝ)
  | 1 => (-12324939 / 500000000000 : ℝ)
  | 2 => (-1782063 / 100000000000 : ℝ)
  | 3 => (-5429807 / 500000000000 : ℝ)
  | 4 => (-3765739 / 1000000000000 : ℝ)
  | 5 => (3462083 / 1000000000000 : ℝ)
  | 6 => (10824933 / 1000000000000 : ℝ)
  | 7 => (4580973 / 250000000000 : ℝ)
  | 8 => (811251 / 31250000000 : ℝ)
  | 9 => (16867211 / 500000000000 : ℝ)
  | 10 => (41648127 / 1000000000000 : ℝ)
  | 11 => (9940441 / 200000000000 : ℝ)
  | 12 => (14474427 / 250000000000 : ℝ)
  | 13 => (66235683 / 1000000000000 : ℝ)
  | 14 => (74717171 / 1000000000000 : ℝ)
  | 15 => (20835801 / 250000000000 : ℝ)
  | 16 => (92114811 / 1000000000000 : ℝ)
  | 17 => (10103301 / 100000000000 : ℝ)
  | 18 => (55049407 / 500000000000 : ℝ)
  | 19 => (29828307 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch031Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-24649877 / 1000000000000 : ℝ)
  | 1 => (-17820629 / 1000000000000 : ℝ)
  | 2 => (-10859613 / 1000000000000 : ℝ)
  | 3 => (-1882869 / 500000000000 : ℝ)
  | 4 => (865521 / 250000000000 : ℝ)
  | 5 => (5412467 / 500000000000 : ℝ)
  | 6 => (18323893 / 1000000000000 : ℝ)
  | 7 => (25960033 / 1000000000000 : ℝ)
  | 8 => (33734423 / 1000000000000 : ℝ)
  | 9 => (10168 / 244140625 : ℝ)
  | 10 => (24851103 / 500000000000 : ℝ)
  | 11 => (57897709 / 1000000000000 : ℝ)
  | 12 => (16558921 / 250000000000 : ℝ)
  | 13 => (18679293 / 250000000000 : ℝ)
  | 14 => (16668641 / 200000000000 : ℝ)
  | 15 => (23028703 / 250000000000 : ℝ)
  | 16 => (101033011 / 1000000000000 : ℝ)
  | 17 => (22019763 / 200000000000 : ℝ)
  | 18 => (119313229 / 1000000000000 : ℝ)
  | 19 => (128677249 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch031Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((620 : ℝ) + (j.val : ℝ)) / 1600)
      (((620 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch031Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch031Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((620 : ℝ) + (j.val : ℝ)) / 1600)
    (((620 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch031Neg100WeightLower j.val) (hpThetaShiftTwoBatch031Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch031Neg100WeightLower, hpThetaShiftTwoBatch031Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch031Neg100_integral_bounds :
    (8721173 / 50000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (107070697 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (620 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch031Lower hpThetaJensenCellsBatch031Upper
    hpThetaShiftTwoBatch031Neg100WeightLower hpThetaShiftTwoBatch031Neg100WeightUpper hpThetaJensenCellsBatch031_bounds hpThetaShiftTwoBatch031Neg100_weight_bounds
  have hl : (8721173 / 50000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch031Lower j * hpThetaShiftTwoBatch031Neg100WeightLower j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftTwoBatch031Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftTwoBatch031Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch031Lower j * hpThetaShiftTwoBatch031Neg100WeightUpper j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftTwoBatch031Neg100WeightUpper j) / 1600) ≤ (107070697 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftTwoBatch031Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (620 : ℝ) / 1600 = 31 / 80 by norm_num,
    show ((620 : ℝ) + 20) / 1600 = (31 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch031Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-483232749 / 1000000000000 : ℝ)
  | 1 => (-7593809 / 15625000000 : ℝ)
  | 2 => (-488747587 / 1000000000000 : ℝ)
  | 3 => (-491463431 / 1000000000000 : ℝ)
  | 4 => (-494150553 / 1000000000000 : ℝ)
  | 5 => (-49680819 / 100000000000 : ℝ)
  | 6 => (-499435571 / 1000000000000 : ℝ)
  | 7 => (-6275399 / 12500000000 : ℝ)
  | 8 => (-504596453 / 1000000000000 : ℝ)
  | 9 => (-507128379 / 1000000000000 : ℝ)
  | 10 => (-509626901 / 1000000000000 : ℝ)
  | 11 => (-512091213 / 1000000000000 : ℝ)
  | 12 => (-102904101 / 200000000000 : ℝ)
  | 13 => (-258456979 / 500000000000 : ℝ)
  | 14 => (-259635373 / 500000000000 : ℝ)
  | 15 => (-521590037 / 1000000000000 : ℝ)
  | 16 => (-32741937 / 62500000000 : ℝ)
  | 17 => (-105222553 / 200000000000 : ℝ)
  | 18 => (-264157251 / 500000000000 : ℝ)
  | 19 => (-33154709 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch031Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-480435247 / 1000000000000 : ℝ)
  | 1 => (-120808187 / 250000000000 : ℝ)
  | 2 => (-19440151 / 40000000000 : ℝ)
  | 3 => (-244373793 / 500000000000 : ℝ)
  | 4 => (-49146343 / 100000000000 : ℝ)
  | 5 => (-61768819 / 125000000000 : ℝ)
  | 6 => (-496808189 / 1000000000000 : ℝ)
  | 7 => (-49943557 / 100000000000 : ℝ)
  | 8 => (-502031919 / 1000000000000 : ℝ)
  | 9 => (-126149113 / 250000000000 : ℝ)
  | 10 => (-253564189 / 500000000000 : ℝ)
  | 11 => (-5096269 / 10000000000 : ℝ)
  | 12 => (-128022803 / 250000000000 : ℝ)
  | 13 => (-64315063 / 125000000000 : ℝ)
  | 14 => (-516913957 / 1000000000000 : ℝ)
  | 15 => (-103854149 / 200000000000 : ℝ)
  | 16 => (-130397509 / 250000000000 : ℝ)
  | 17 => (-523870991 / 1000000000000 : ℝ)
  | 18 => (-131528191 / 250000000000 : ℝ)
  | 19 => (-528314501 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch031Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((620 : ℝ) + (j.val : ℝ)) / 1600)
      (((620 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch031Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch031Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((620 : ℝ) + (j.val : ℝ)) / 1600)
    (((620 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch031Neg65WeightLower j.val) (hpThetaShiftTwoBatch031Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch031Neg65WeightLower, hpThetaShiftTwoBatch031Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch031Neg65_integral_bounds :
    (-2332641703 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-1143936097 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (620 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch031Lower hpThetaJensenCellsBatch031Upper
    hpThetaShiftTwoBatch031Neg65WeightLower hpThetaShiftTwoBatch031Neg65WeightUpper hpThetaJensenCellsBatch031_bounds hpThetaShiftTwoBatch031Neg65_weight_bounds
  have hl : (-2332641703 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch031Lower j * hpThetaShiftTwoBatch031Neg65WeightLower j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftTwoBatch031Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftTwoBatch031Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch031Lower j * hpThetaShiftTwoBatch031Neg65WeightUpper j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftTwoBatch031Neg65WeightUpper j) / 1600) ≤ (-1143936097 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftTwoBatch031Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (620 : ℝ) / 1600 = 31 / 80 by norm_num,
    show ((620 : ℝ) + 20) / 1600 = (31 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch031Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-16316599 / 50000000000 : ℝ)
  | 1 => (-165548017 / 500000000000 : ℝ)
  | 2 => (-33588439 / 100000000000 : ℝ)
  | 3 => (-34069687 / 100000000000 : ℝ)
  | 4 => (-345533291 / 1000000000000 : ℝ)
  | 5 => (-175196733 / 500000000000 : ℝ)
  | 6 => (-71055441 / 200000000000 : ℝ)
  | 7 => (-360184311 / 1000000000000 : ℝ)
  | 8 => (-73022917 / 200000000000 : ℝ)
  | 9 => (-23129239 / 62500000000 : ℝ)
  | 10 => (-375043819 / 1000000000000 : ℝ)
  | 11 => (-380042357 / 1000000000000 : ℝ)
  | 12 => (-385063221 / 1000000000000 : ℝ)
  | 13 => (-39010619 / 100000000000 : ℝ)
  | 14 => (-197585519 / 500000000000 : ℝ)
  | 15 => (-200128767 / 500000000000 : ℝ)
  | 16 => (-101341361 / 250000000000 : ℝ)
  | 17 => (-410494529 / 1000000000000 : ℝ)
  | 18 => (-415644543 / 1000000000000 : ℝ)
  | 19 => (-420815239 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch031Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-321592401 / 1000000000000 : ℝ)
  | 1 => (-326331979 / 1000000000000 : ℝ)
  | 2 => (-331096033 / 1000000000000 : ℝ)
  | 3 => (-335884389 / 1000000000000 : ℝ)
  | 4 => (-340696869 / 1000000000000 : ℝ)
  | 5 => (-34553329 / 100000000000 : ℝ)
  | 6 => (-70078693 / 200000000000 : ℝ)
  | 7 => (-88819301 / 250000000000 : ℝ)
  | 8 => (-36018431 / 100000000000 : ℝ)
  | 9 => (-45639323 / 125000000000 : ℝ)
  | 10 => (-370067823 / 1000000000000 : ℝ)
  | 11 => (-187521909 / 500000000000 : ℝ)
  | 12 => (-95010589 / 250000000000 : ℝ)
  | 13 => (-19253161 / 50000000000 : ℝ)
  | 14 => (-390106189 / 1000000000000 : ℝ)
  | 15 => (-395171037 / 1000000000000 : ℝ)
  | 16 => (-400257533 / 1000000000000 : ℝ)
  | 17 => (-405365443 / 1000000000000 : ℝ)
  | 18 => (-6413977 / 15625000000 : ℝ)
  | 19 => (-207822271 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch031Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((620 : ℝ) + (j.val : ℝ)) / 1600)
      (((620 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch031Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch031Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((620 : ℝ) + (j.val : ℝ)) / 1600)
    (((620 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch031Neg45WeightLower j.val) (hpThetaShiftTwoBatch031Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch031Neg45WeightLower, hpThetaShiftTwoBatch031Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch031Neg45_integral_bounds :
    (-855202353 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-415860759 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (620 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch031Lower hpThetaJensenCellsBatch031Upper
    hpThetaShiftTwoBatch031Neg45WeightLower hpThetaShiftTwoBatch031Neg45WeightUpper hpThetaJensenCellsBatch031_bounds hpThetaShiftTwoBatch031Neg45_weight_bounds
  have hl : (-855202353 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch031Lower j * hpThetaShiftTwoBatch031Neg45WeightLower j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftTwoBatch031Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftTwoBatch031Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch031Lower j * hpThetaShiftTwoBatch031Neg45WeightUpper j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftTwoBatch031Neg45WeightUpper j) / 1600) ≤ (-415860759 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftTwoBatch031Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (620 : ℝ) / 1600 = 31 / 80 by norm_num,
    show ((620 : ℝ) + 20) / 1600 = (31 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch031Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (289174997 / 1000000000000 : ℝ)
  | 1 => (57490947 / 200000000000 : ℝ)
  | 2 => (285701019 / 1000000000000 : ℝ)
  | 3 => (141956827 / 500000000000 : ℝ)
  | 4 => (282092447 / 1000000000000 : ℝ)
  | 5 => (70059301 / 250000000000 : ℝ)
  | 6 => (278347729 / 1000000000000 : ℝ)
  | 7 => (276423831 / 1000000000000 : ℝ)
  | 8 => (54893063 / 200000000000 : ℝ)
  | 9 => (272471989 / 1000000000000 : ℝ)
  | 10 => (13522183 / 50000000000 : ℝ)
  | 11 => (33547517 / 125000000000 : ℝ)
  | 12 => (10651249 / 40000000000 : ℝ)
  | 13 => (264146737 / 1000000000000 : ℝ)
  | 14 => (261976479 / 1000000000000 : ℝ)
  | 15 => (259770263 / 1000000000000 : ℝ)
  | 16 => (257527897 / 1000000000000 : ℝ)
  | 17 => (31906149 / 125000000000 : ℝ)
  | 18 => (252933959 / 1000000000000 : ℝ)
  | 19 => (25058201 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch031Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (290862003 / 1000000000000 : ℝ)
  | 1 => (144587499 / 500000000000 : ℝ)
  | 2 => (17965921 / 62500000000 : ℝ)
  | 3 => (14285051 / 50000000000 : ℝ)
  | 4 => (56782731 / 200000000000 : ℝ)
  | 5 => (8815389 / 31250000000 : ℝ)
  | 6 => (56047441 / 200000000000 : ℝ)
  | 7 => (27834773 / 100000000000 : ℝ)
  | 8 => (34552979 / 125000000000 : ℝ)
  | 9 => (68616329 / 250000000000 : ℝ)
  | 10 => (27247199 / 100000000000 : ℝ)
  | 11 => (270443661 / 1000000000000 : ℝ)
  | 12 => (268380137 / 1000000000000 : ℝ)
  | 13 => (133140613 / 500000000000 : ℝ)
  | 14 => (132073369 / 500000000000 : ℝ)
  | 15 => (1637353 / 6250000000 : ℝ)
  | 16 => (32471283 / 125000000000 : ℝ)
  | 17 => (128763949 / 500000000000 : ℝ)
  | 18 => (255249193 / 1000000000000 : ℝ)
  | 19 => (6323349 / 25000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch031Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((620 : ℝ) + (j.val : ℝ)) / 1600)
      (((620 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch031Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch031Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((620 : ℝ) + (j.val : ℝ)) / 1600)
    (((620 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch031Neg25WeightLower j.val) (hpThetaShiftTwoBatch031Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch031Neg25WeightLower, hpThetaShiftTwoBatch031Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch031Neg25_integral_bounds :
    (1229220061 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (1256303247 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (620 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch031Lower hpThetaJensenCellsBatch031Upper
    hpThetaShiftTwoBatch031Neg25WeightLower hpThetaShiftTwoBatch031Neg25WeightUpper hpThetaJensenCellsBatch031_bounds hpThetaShiftTwoBatch031Neg25_weight_bounds
  have hl : (1229220061 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch031Lower j * hpThetaShiftTwoBatch031Neg25WeightLower j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftTwoBatch031Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftTwoBatch031Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch031Lower j * hpThetaShiftTwoBatch031Neg25WeightUpper j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftTwoBatch031Neg25WeightUpper j) / 1600) ≤ (1256303247 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftTwoBatch031Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (620 : ℝ) / 1600 = 31 / 80 by norm_num,
    show ((620 : ℝ) + 20) / 1600 = (31 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch031Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch031Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch031Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch031Neg25_integral_bounds
end HodgeProofHP
