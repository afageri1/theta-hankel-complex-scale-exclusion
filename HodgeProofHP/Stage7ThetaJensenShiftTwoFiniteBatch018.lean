/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch018

/-! Exact signed weight and batch integral certificates, batch 18 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch018Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5232969 / 1000000000000 : ℝ)
  | 1 => (-5983411 / 1000000000000 : ℝ)
  | 2 => (-674621 / 100000000000 : ℝ)
  | 3 => (-3760707 / 500000000000 : ℝ)
  | 4 => (-8309063 / 1000000000000 : ℝ)
  | 5 => (-9109199 / 1000000000000 : ℝ)
  | 6 => (-4960931 / 500000000000 : ℝ)
  | 7 => (-671693 / 62500000000 : ℝ)
  | 8 => (-724057 / 62500000000 : ℝ)
  | 9 => (-12435367 / 1000000000000 : ℝ)
  | 10 => (-13298483 / 1000000000000 : ℝ)
  | 11 => (-1417429 / 100000000000 : ℝ)
  | 12 => (-7531407 / 500000000000 : ℝ)
  | 13 => (-15964079 / 1000000000000 : ℝ)
  | 14 => (-8439053 / 500000000000 : ℝ)
  | 15 => (-4451229 / 250000000000 : ℝ)
  | 16 => (-9372263 / 500000000000 : ℝ)
  | 17 => (-19696949 / 1000000000000 : ℝ)
  | 18 => (-20662199 / 1000000000000 : ℝ)
  | 19 => (-10820143 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch018Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2247419 / 500000000000 : ℝ)
  | 1 => (-654121 / 125000000000 : ℝ)
  | 2 => (-598341 / 100000000000 : ℝ)
  | 3 => (-6746209 / 1000000000000 : ℝ)
  | 4 => (-7521413 / 1000000000000 : ℝ)
  | 5 => (-4154531 / 500000000000 : ℝ)
  | 6 => (-4554599 / 500000000000 : ℝ)
  | 7 => (-9921861 / 1000000000000 : ℝ)
  | 8 => (-10747087 / 1000000000000 : ℝ)
  | 9 => (-11584911 / 1000000000000 : ℝ)
  | 10 => (-6217683 / 500000000000 : ℝ)
  | 11 => (-6649241 / 500000000000 : ℝ)
  | 12 => (-14174289 / 1000000000000 : ℝ)
  | 13 => (-15062813 / 1000000000000 : ℝ)
  | 14 => (-7982039 / 500000000000 : ℝ)
  | 15 => (-3375621 / 200000000000 : ℝ)
  | 16 => (-3560983 / 200000000000 : ℝ)
  | 17 => (-749781 / 40000000000 : ℝ)
  | 18 => (-4924237 / 250000000000 : ℝ)
  | 19 => (-10331099 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch018Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((360 : ℝ) + (j.val : ℝ)) / 1600)
      (((360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch018Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch018Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((360 : ℝ) + (j.val : ℝ)) / 1600)
    (((360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch018Neg100WeightLower j.val) (hpThetaShiftTwoBatch018Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch018Neg100WeightLower, hpThetaShiftTwoBatch018Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch018Neg100_integral_bounds :
    (-8712569 / 50000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-80395757 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch018Lower hpThetaJensenCellsBatch018Upper
    hpThetaShiftTwoBatch018Neg100WeightLower hpThetaShiftTwoBatch018Neg100WeightUpper hpThetaJensenCellsBatch018_bounds hpThetaShiftTwoBatch018Neg100_weight_bounds
  have hl : (-8712569 / 50000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch018Lower j * hpThetaShiftTwoBatch018Neg100WeightLower j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftTwoBatch018Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftTwoBatch018Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch018Lower j * hpThetaShiftTwoBatch018Neg100WeightUpper j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftTwoBatch018Neg100WeightUpper j) / 1600) ≤ (-80395757 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftTwoBatch018Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (360 : ℝ) / 1600 = 18 / 80 by norm_num,
    show ((360 : ℝ) + 20) / 1600 = (18 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch018Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (49144451 / 1000000000000 : ℝ)
  | 1 => (12251547 / 250000000000 : ℝ)
  | 2 => (48857967 / 1000000000000 : ℝ)
  | 3 => (24349833 / 500000000000 : ℝ)
  | 4 => (48531161 / 1000000000000 : ℝ)
  | 5 => (4835233 / 100000000000 : ℝ)
  | 6 => (48163051 / 1000000000000 : ℝ)
  | 7 => (29977 / 625000000 : ℝ)
  | 8 => (9550531 / 200000000000 : ℝ)
  | 9 => (11882823 / 250000000000 : ℝ)
  | 10 => (11824747 / 250000000000 : ℝ)
  | 11 => (47055621 / 1000000000000 : ℝ)
  | 12 => (11700267 / 250000000000 : ℝ)
  | 13 => (23267603 / 500000000000 : ℝ)
  | 14 => (46257911 / 1000000000000 : ℝ)
  | 15 => (45969061 / 1000000000000 : ℝ)
  | 16 => (45668533 / 1000000000000 : ℝ)
  | 17 => (11339051 / 250000000000 : ℝ)
  | 18 => (2814497 / 62500000000 : ℝ)
  | 19 => (8939131 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch018Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (49272879 / 1000000000000 : ℝ)
  | 1 => (12286113 / 250000000000 : ℝ)
  | 2 => (49006189 / 1000000000000 : ℝ)
  | 3 => (3053623 / 62500000000 : ℝ)
  | 4 => (48699667 / 1000000000000 : ℝ)
  | 5 => (24265581 / 500000000000 : ℝ)
  | 6 => (48352331 / 1000000000000 : ℝ)
  | 7 => (12040763 / 250000000000 : ℝ)
  | 8 => (47963201 / 1000000000000 : ℝ)
  | 9 => (2984541 / 62500000000 : ℝ)
  | 10 => (47531293 / 1000000000000 : ℝ)
  | 11 => (47298989 / 1000000000000 : ℝ)
  | 12 => (23527811 / 500000000000 : ℝ)
  | 13 => (46801069 / 1000000000000 : ℝ)
  | 14 => (46535207 / 1000000000000 : ℝ)
  | 15 => (5782239 / 125000000000 : ℝ)
  | 16 => (22984531 / 500000000000 : ℝ)
  | 17 => (22834267 / 500000000000 : ℝ)
  | 18 => (9071241 / 200000000000 : ℝ)
  | 19 => (45031953 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch018Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((360 : ℝ) + (j.val : ℝ)) / 1600)
      (((360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch018Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch018Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((360 : ℝ) + (j.val : ℝ)) / 1600)
    (((360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch018Neg65WeightLower j.val) (hpThetaShiftTwoBatch018Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch018Neg65WeightLower, hpThetaShiftTwoBatch018Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch018Neg65_integral_bounds :
    (78256909 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (79600737 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch018Lower hpThetaJensenCellsBatch018Upper
    hpThetaShiftTwoBatch018Neg65WeightLower hpThetaShiftTwoBatch018Neg65WeightUpper hpThetaJensenCellsBatch018_bounds hpThetaShiftTwoBatch018Neg65_weight_bounds
  have hl : (78256909 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch018Lower j * hpThetaShiftTwoBatch018Neg65WeightLower j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftTwoBatch018Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftTwoBatch018Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch018Lower j * hpThetaShiftTwoBatch018Neg65WeightUpper j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftTwoBatch018Neg65WeightUpper j) / 1600) ≤ (79600737 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftTwoBatch018Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (360 : ℝ) / 1600 = 18 / 80 by norm_num,
    show ((360 : ℝ) + 20) / 1600 = (18 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch018Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (90359391 / 1000000000000 : ℝ)
  | 1 => (45398719 / 500000000000 : ℝ)
  | 2 => (5701933 / 62500000000 : ℝ)
  | 3 => (11457469 / 125000000000 : ℝ)
  | 4 => (92083797 / 1000000000000 : ℝ)
  | 5 => (1850059 / 20000000000 : ℝ)
  | 6 => (92917099 / 1000000000000 : ℝ)
  | 7 => (93326129 / 1000000000000 : ℝ)
  | 8 => (46864963 / 500000000000 : ℝ)
  | 9 => (47064187 / 500000000000 : ℝ)
  | 10 => (94521357 / 1000000000000 : ℝ)
  | 11 => (47454379 / 500000000000 : ℝ)
  | 12 => (95290459 / 1000000000000 : ℝ)
  | 13 => (95666343 / 1000000000000 : ℝ)
  | 14 => (9603629 / 100000000000 : ℝ)
  | 15 => (96400181 / 1000000000000 : ℝ)
  | 16 => (48378947 / 500000000000 : ℝ)
  | 17 => (9710931 / 100000000000 : ℝ)
  | 18 => (97454307 / 1000000000000 : ℝ)
  | 19 => (97792761 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch018Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (90797439 / 1000000000000 : ℝ)
  | 1 => (91230929 / 1000000000000 : ℝ)
  | 2 => (91659753 / 1000000000000 : ℝ)
  | 3 => (46041899 / 500000000000 : ℝ)
  | 4 => (92502951 / 1000000000000 : ℝ)
  | 5 => (929171 / 10000000000 : ℝ)
  | 6 => (9332613 / 100000000000 : ℝ)
  | 7 => (93729927 / 1000000000000 : ℝ)
  | 8 => (753027 / 8000000000 : ℝ)
  | 9 => (47260679 / 500000000000 : ℝ)
  | 10 => (94908759 / 1000000000000 : ℝ)
  | 11 => (4764523 / 50000000000 : ℝ)
  | 12 => (11958293 / 125000000000 : ℝ)
  | 13 => (96036291 / 1000000000000 : ℝ)
  | 14 => (48200091 / 500000000000 : ℝ)
  | 15 => (19351579 / 200000000000 : ℝ)
  | 16 => (97109311 / 1000000000000 : ℝ)
  | 17 => (24363577 / 250000000000 : ℝ)
  | 18 => (48896381 / 500000000000 : ℝ)
  | 19 => (12265569 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch018Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((360 : ℝ) + (j.val : ℝ)) / 1600)
      (((360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch018Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch018Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((360 : ℝ) + (j.val : ℝ)) / 1600)
    (((360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch018Neg45WeightLower j.val) (hpThetaShiftTwoBatch018Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch018Neg45WeightLower, hpThetaShiftTwoBatch018Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch018Neg45_integral_bounds :
    (623961693 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (317119871 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch018Lower hpThetaJensenCellsBatch018Upper
    hpThetaShiftTwoBatch018Neg45WeightLower hpThetaShiftTwoBatch018Neg45WeightUpper hpThetaJensenCellsBatch018_bounds hpThetaShiftTwoBatch018Neg45_weight_bounds
  have hl : (623961693 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch018Lower j * hpThetaShiftTwoBatch018Neg45WeightLower j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftTwoBatch018Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftTwoBatch018Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch018Lower j * hpThetaShiftTwoBatch018Neg45WeightUpper j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftTwoBatch018Neg45WeightUpper j) / 1600) ≤ (317119871 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftTwoBatch018Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (360 : ℝ) / 1600 = 18 / 80 by norm_num,
    show ((360 : ℝ) + 20) / 1600 = (18 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch018Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (69820877 / 500000000000 : ℝ)
  | 1 => (140823429 / 1000000000000 : ℝ)
  | 2 => (142009107 / 1000000000000 : ℝ)
  | 3 => (7159937 / 50000000000 : ℝ)
  | 4 => (36098069 / 250000000000 : ℝ)
  | 5 => (145589663 / 1000000000000 : ℝ)
  | 6 => (36697713 / 250000000000 : ℝ)
  | 7 => (147995787 / 1000000000000 : ℝ)
  | 8 => (149204417 / 1000000000000 : ℝ)
  | 9 => (75208343 / 500000000000 : ℝ)
  | 10 => (7581627 / 50000000000 : ℝ)
  | 11 => (152851923 / 1000000000000 : ℝ)
  | 12 => (154074779 / 1000000000000 : ℝ)
  | 13 => (155301049 / 1000000000000 : ℝ)
  | 14 => (39132669 / 250000000000 : ℝ)
  | 15 => (157763601 / 1000000000000 : ℝ)
  | 16 => (39749941 / 250000000000 : ℝ)
  | 17 => (32047821 / 200000000000 : ℝ)
  | 18 => (161481563 / 1000000000000 : ℝ)
  | 19 => (6509083 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch018Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (14082343 / 100000000000 : ℝ)
  | 1 => (35502277 / 250000000000 : ℝ)
  | 2 => (143198741 / 1000000000000 : ℝ)
  | 3 => (144392277 / 1000000000000 : ℝ)
  | 4 => (4549677 / 31250000000 : ℝ)
  | 5 => (146790853 / 1000000000000 : ℝ)
  | 6 => (36998947 / 250000000000 : ℝ)
  | 7 => (74602209 / 500000000000 : ℝ)
  | 8 => (150416687 / 1000000000000 : ℝ)
  | 9 => (151632541 / 1000000000000 : ℝ)
  | 10 => (38212981 / 250000000000 : ℝ)
  | 11 => (7703739 / 50000000000 : ℝ)
  | 12 => (3106021 / 20000000000 : ℝ)
  | 13 => (156530677 / 1000000000000 : ℝ)
  | 14 => (78881801 / 500000000000 : ℝ)
  | 15 => (31799953 / 200000000000 : ℝ)
  | 16 => (80119553 / 500000000000 : ℝ)
  | 17 => (40370391 / 250000000000 : ℝ)
  | 18 => (40681769 / 250000000000 : ℝ)
  | 19 => (8198779 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch018Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((360 : ℝ) + (j.val : ℝ)) / 1600)
      (((360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch018Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch018Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((360 : ℝ) + (j.val : ℝ)) / 1600)
    (((360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch018Neg25WeightLower j.val) (hpThetaShiftTwoBatch018Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch018Neg25WeightLower, hpThetaShiftTwoBatch018Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch018Neg25_integral_bounds :
    (400005409 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (18 / 80 : ℝ) ((18 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (127558107 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch018Lower hpThetaJensenCellsBatch018Upper
    hpThetaShiftTwoBatch018Neg25WeightLower hpThetaShiftTwoBatch018Neg25WeightUpper hpThetaJensenCellsBatch018_bounds hpThetaShiftTwoBatch018Neg25_weight_bounds
  have hl : (400005409 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch018Lower j * hpThetaShiftTwoBatch018Neg25WeightLower j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftTwoBatch018Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftTwoBatch018Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch018Lower j * hpThetaShiftTwoBatch018Neg25WeightUpper j)
        (hpThetaJensenCellsBatch018Upper j * hpThetaShiftTwoBatch018Neg25WeightUpper j) / 1600) ≤ (127558107 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch018Lower, hpThetaJensenCellsBatch018Upper,
      hpThetaShiftTwoBatch018Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (360 : ℝ) / 1600 = 18 / 80 by norm_num,
    show ((360 : ℝ) + 20) / 1600 = (18 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch018Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch018Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch018Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch018Neg25_integral_bounds
end HodgeProofHP
