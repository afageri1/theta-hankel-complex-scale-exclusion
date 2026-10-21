/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch008

/-! Exact signed weight and batch integral certificates, batch 8 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch008Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2744047619 / 1000000000000 : ℝ)
  | 1 => (344109131 / 125000000000 : ℝ)
  | 2 => (138059469 / 50000000000 : ℝ)
  | 3 => (2768988851 / 1000000000000 : ℝ)
  | 4 => (2776263729 / 1000000000000 : ℝ)
  | 5 => (695751579 / 250000000000 : ℝ)
  | 6 => (2789208951 / 1000000000000 : ℝ)
  | 7 => (279486401 / 100000000000 : ℝ)
  | 8 => (2799963907 / 1000000000000 : ℝ)
  | 9 => (350562637 / 125000000000 : ℝ)
  | 10 => (1404234037 / 500000000000 : ℝ)
  | 11 => (2811857377 / 1000000000000 : ℝ)
  | 12 => (281466159 / 100000000000 : ℝ)
  | 13 => (2816873339 / 1000000000000 : ℝ)
  | 14 => (2818485299 / 1000000000000 : ℝ)
  | 15 => (2819490193 / 1000000000000 : ℝ)
  | 16 => (2819649921 / 1000000000000 : ℝ)
  | 17 => (1409395227 / 500000000000 : ℝ)
  | 18 => (70432383 / 25000000000 : ℝ)
  | 19 => (2815157503 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch008Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2752873049 / 1000000000000 : ℝ)
  | 1 => (2761189381 / 1000000000000 : ℝ)
  | 2 => (692247213 / 250000000000 : ℝ)
  | 3 => (277626373 / 100000000000 : ℝ)
  | 4 => (2783006317 / 1000000000000 : ℝ)
  | 5 => (348651119 / 125000000000 : ℝ)
  | 6 => (2794864011 / 1000000000000 : ℝ)
  | 7 => (699990977 / 250000000000 : ℝ)
  | 8 => (2804501097 / 1000000000000 : ℝ)
  | 9 => (112338723 / 40000000000 : ℝ)
  | 10 => (1405928689 / 500000000000 : ℝ)
  | 11 => (2814661591 / 1000000000000 : ℝ)
  | 12 => (140843667 / 50000000000 : ℝ)
  | 13 => (28184853 / 10000000000 : ℝ)
  | 14 => (1409745097 / 500000000000 : ℝ)
  | 15 => (2819880793 / 1000000000000 : ℝ)
  | 16 => (112795637 / 40000000000 : ℝ)
  | 17 => (1409824961 / 500000000000 : ℝ)
  | 18 => (563758091 / 200000000000 : ℝ)
  | 19 => (2817295321 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch008Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((160 : ℝ) + (j.val : ℝ)) / 1600)
      (((160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch008Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch008Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((160 : ℝ) + (j.val : ℝ)) / 1600)
    (((160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch008Neg100WeightLower j.val) (hpThetaShiftOneBatch008Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch008Neg100WeightLower, hpThetaShiftOneBatch008Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch008Neg100_integral_bounds :
    (55900004247 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (28302526347 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch008Lower hpThetaJensenCellsBatch008Upper
    hpThetaShiftOneBatch008Neg100WeightLower hpThetaShiftOneBatch008Neg100WeightUpper hpThetaJensenCellsBatch008_bounds hpThetaShiftOneBatch008Neg100_weight_bounds
  have hl : (55900004247 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch008Lower j * hpThetaShiftOneBatch008Neg100WeightLower j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftOneBatch008Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftOneBatch008Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch008Lower j * hpThetaShiftOneBatch008Neg100WeightUpper j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftOneBatch008Neg100WeightUpper j) / 1600) ≤ (28302526347 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftOneBatch008Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (160 : ℝ) / 1600 = 8 / 80 by norm_num,
    show ((160 : ℝ) + 20) / 1600 = (8 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch008Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3478990327 / 1000000000000 : ℝ)
  | 1 => (438077249 / 125000000000 : ℝ)
  | 2 => (1764994101 / 500000000000 : ℝ)
  | 3 => (3555094389 / 1000000000000 : ℝ)
  | 4 => (178996499 / 50000000000 : ℝ)
  | 5 => (901122099 / 250000000000 : ℝ)
  | 6 => (3628763059 / 1000000000000 : ℝ)
  | 7 => (730549477 / 200000000000 : ℝ)
  | 8 => (3676434789 / 1000000000000 : ℝ)
  | 9 => (1849909343 / 500000000000 : ℝ)
  | 10 => (3722892489 / 1000000000000 : ℝ)
  | 11 => (936412403 / 250000000000 : ℝ)
  | 12 => (3768083467 / 1000000000000 : ℝ)
  | 13 => (236886717 / 62500000000 : ℝ)
  | 14 => (1905977521 / 500000000000 : ℝ)
  | 15 => (3833379599 / 1000000000000 : ℝ)
  | 16 => (963613641 / 250000000000 : ℝ)
  | 17 => (1937586683 / 500000000000 : ℝ)
  | 18 => (779105887 / 200000000000 : ℝ)
  | 19 => (3915516209 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch008Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3504617993 / 1000000000000 : ℝ)
  | 1 => (3529988203 / 1000000000000 : ℝ)
  | 2 => (355509439 / 100000000000 : ℝ)
  | 3 => (3579929981 / 1000000000000 : ℝ)
  | 4 => (3604488397 / 1000000000000 : ℝ)
  | 5 => (181438153 / 50000000000 : ℝ)
  | 6 => (1826373693 / 500000000000 : ℝ)
  | 7 => (367643479 / 100000000000 : ℝ)
  | 8 => (3699818687 / 1000000000000 : ℝ)
  | 9 => (372289249 / 100000000000 : ℝ)
  | 10 => (3745649613 / 1000000000000 : ℝ)
  | 11 => (942020867 / 250000000000 : ℝ)
  | 12 => (3790187473 / 1000000000000 : ℝ)
  | 13 => (3811955043 / 1000000000000 : ℝ)
  | 14 => (9583449 / 2500000000 : ℝ)
  | 15 => (770890913 / 200000000000 : ℝ)
  | 16 => (3875173367 / 1000000000000 : ℝ)
  | 17 => (973882359 / 250000000000 : ℝ)
  | 18 => (391551621 / 100000000000 : ℝ)
  | 19 => (3935127131 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch008Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((160 : ℝ) + (j.val : ℝ)) / 1600)
      (((160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch008Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch008Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((160 : ℝ) + (j.val : ℝ)) / 1600)
    (((160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch008Neg65WeightLower j.val) (hpThetaShiftOneBatch008Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch008Neg65WeightLower, hpThetaShiftOneBatch008Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch008Neg65_integral_bounds :
    (74061443737 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (9418557119 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch008Lower hpThetaJensenCellsBatch008Upper
    hpThetaShiftOneBatch008Neg65WeightLower hpThetaShiftOneBatch008Neg65WeightUpper hpThetaJensenCellsBatch008_bounds hpThetaShiftOneBatch008Neg65_weight_bounds
  have hl : (74061443737 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch008Lower j * hpThetaShiftOneBatch008Neg65WeightLower j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftOneBatch008Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftOneBatch008Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch008Lower j * hpThetaShiftOneBatch008Neg65WeightUpper j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftOneBatch008Neg65WeightUpper j) / 1600) ≤ (9418557119 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftOneBatch008Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (160 : ℝ) / 1600 = 8 / 80 by norm_num,
    show ((160 : ℝ) + 20) / 1600 = (8 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch008Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4039619047 / 1000000000000 : ℝ)
  | 1 => (4078583171 / 1000000000000 : ℝ)
  | 2 => (4117510483 / 1000000000000 : ℝ)
  | 3 => (4156396243 / 1000000000000 : ℝ)
  | 4 => (1048808923 / 250000000000 : ℝ)
  | 5 => (211701203 / 50000000000 : ℝ)
  | 6 => (4272756559 / 1000000000000 : ℝ)
  | 7 => (4311428389 / 1000000000000 : ℝ)
  | 8 => (870006947 / 200000000000 : ℝ)
  | 9 => (274285673 / 62500000000 : ℝ)
  | 10 => (2213515823 / 500000000000 : ℝ)
  | 11 => (4465412513 / 1000000000000 : ℝ)
  | 12 => (9007417 / 2000000000 : ℝ)
  | 13 => (2270957363 / 500000000000 : ℝ)
  | 14 => (572503287 / 125000000000 : ℝ)
  | 15 => (923607661 / 200000000000 : ℝ)
  | 16 => (2327972917 / 500000000000 : ℝ)
  | 17 => (4693743953 / 1000000000000 : ℝ)
  | 18 => (118285693 / 25000000000 : ℝ)
  | 19 => (4768992183 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch008Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1019645793 / 250000000000 : ℝ)
  | 1 => (1029377621 / 250000000000 : ℝ)
  | 2 => (1039099061 / 250000000000 : ℝ)
  | 3 => (4195235693 / 1000000000000 : ℝ)
  | 4 => (4234024061 / 1000000000000 : ℝ)
  | 5 => (53409457 / 12500000000 : ℝ)
  | 6 => (431142839 / 100000000000 : ℝ)
  | 7 => (271877171 / 62500000000 : ℝ)
  | 8 => (4388570769 / 1000000000000 : ℝ)
  | 9 => (4427031647 / 1000000000000 : ℝ)
  | 10 => (2232706257 / 500000000000 : ℝ)
  | 11 => (4503708501 / 1000000000000 : ℝ)
  | 12 => (4541914727 / 1000000000000 : ℝ)
  | 13 => (4580026297 / 1000000000000 : ℝ)
  | 14 => (2309019153 / 500000000000 : ℝ)
  | 15 => (931189167 / 200000000000 : ℝ)
  | 16 => (2346871977 / 500000000000 : ℝ)
  | 17 => (4731427721 / 1000000000000 : ℝ)
  | 18 => (596124023 / 125000000000 : ℝ)
  | 19 => (4806432379 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch008Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((160 : ℝ) + (j.val : ℝ)) / 1600)
      (((160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch008Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch008Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((160 : ℝ) + (j.val : ℝ)) / 1600)
    (((160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch008Neg40WeightLower j.val) (hpThetaShiftOneBatch008Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch008Neg40WeightLower, hpThetaShiftOneBatch008Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch008Neg40_integral_bounds :
    (17609423519 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (22450965961 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch008Lower hpThetaJensenCellsBatch008Upper
    hpThetaShiftOneBatch008Neg40WeightLower hpThetaShiftOneBatch008Neg40WeightUpper hpThetaJensenCellsBatch008_bounds hpThetaShiftOneBatch008Neg40_weight_bounds
  have hl : (17609423519 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch008Lower j * hpThetaShiftOneBatch008Neg40WeightLower j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftOneBatch008Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftOneBatch008Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch008Lower j * hpThetaShiftOneBatch008Neg40WeightUpper j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftOneBatch008Neg40WeightUpper j) / 1600) ≤ (22450965961 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftOneBatch008Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (160 : ℝ) / 1600 = 8 / 80 by norm_num,
    show ((160 : ℝ) + 20) / 1600 = (8 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch008Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (225497619 / 50000000000 : ℝ)
  | 1 => (4560408491 / 1000000000000 : ℝ)
  | 2 => (2305514909 / 500000000000 : ℝ)
  | 3 => (2330906851 / 500000000000 : ℝ)
  | 4 => (4712757469 / 1000000000000 : ℝ)
  | 5 => (952771687 / 200000000000 : ℝ)
  | 6 => (48151139 / 10000000000 : ℝ)
  | 7 => (973304231 / 200000000000 : ℝ)
  | 8 => (1229519369 / 250000000000 : ℝ)
  | 9 => (4969780127 / 1000000000000 : ℝ)
  | 10 => (125540659 / 25000000000 : ℝ)
  | 11 => (2536806707 / 500000000000 : ℝ)
  | 12 => (5125738517 / 1000000000000 : ℝ)
  | 13 => (1294499721 / 250000000000 : ℝ)
  | 14 => (5230391717 / 1000000000000 : ℝ)
  | 15 => (5282914207 / 1000000000000 : ℝ)
  | 16 => (2667781767 / 500000000000 : ℝ)
  | 17 => (168385527 / 31250000000 : ℝ)
  | 18 => (680153919 / 125000000000 : ℝ)
  | 19 => (5494244141 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch008Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1140102123 / 250000000000 : ℝ)
  | 1 => (4611029819 / 1000000000000 : ℝ)
  | 2 => (4661813703 / 1000000000000 : ℝ)
  | 3 => (471275747 / 100000000000 : ℝ)
  | 4 => (1190964609 / 250000000000 : ℝ)
  | 5 => (4815113901 / 1000000000000 : ℝ)
  | 6 => (1216630289 / 250000000000 : ℝ)
  | 7 => (4918077477 / 1000000000000 : ℝ)
  | 8 => (155305629 / 31250000000 : ℝ)
  | 9 => (5021626361 / 1000000000000 : ℝ)
  | 10 => (1014722683 / 200000000000 : ℝ)
  | 11 => (2562869259 / 500000000000 : ℝ)
  | 12 => (1035599777 / 200000000000 : ℝ)
  | 13 => (2615195859 / 500000000000 : ℝ)
  | 14 => (165091069 / 31250000000 : ℝ)
  | 15 => (1067112707 / 200000000000 : ℝ)
  | 16 => (1077667373 / 200000000000 : ℝ)
  | 17 => (5441231353 / 1000000000000 : ℝ)
  | 18 => (2747122071 / 500000000000 : ℝ)
  | 19 => (1109474473 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch008Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((160 : ℝ) + (j.val : ℝ)) / 1600)
      (((160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch008Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch008Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((160 : ℝ) + (j.val : ℝ)) / 1600)
    (((160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch008Neg20WeightLower j.val) (hpThetaShiftOneBatch008Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch008Neg20WeightLower, hpThetaShiftOneBatch008Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch008Neg20_integral_bounds :
    (24964898087 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (102021356429 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch008Lower hpThetaJensenCellsBatch008Upper
    hpThetaShiftOneBatch008Neg20WeightLower hpThetaShiftOneBatch008Neg20WeightUpper hpThetaJensenCellsBatch008_bounds hpThetaShiftOneBatch008Neg20_weight_bounds
  have hl : (24964898087 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch008Lower j * hpThetaShiftOneBatch008Neg20WeightLower j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftOneBatch008Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftOneBatch008Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch008Lower j * hpThetaShiftOneBatch008Neg20WeightUpper j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftOneBatch008Neg20WeightUpper j) / 1600) ≤ (102021356429 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftOneBatch008Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (160 : ℝ) / 1600 = 8 / 80 by norm_num,
    show ((160 : ℝ) + 20) / 1600 = (8 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch008Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch008Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch008Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch008Neg20_integral_bounds
end HodgeProofHP
