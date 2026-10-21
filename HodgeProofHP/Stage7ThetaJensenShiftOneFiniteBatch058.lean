/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch058

/-! Exact signed weight and batch integral certificates, batch 58 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch058Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-15924037087463 / 1000000000000 : ℝ)
  | 1 => (-642987454913 / 40000000000 : ℝ)
  | 2 => (-8113246301063 / 500000000000 : ℝ)
  | 3 => (-16379462958953 / 1000000000000 : ℝ)
  | 4 => (-8266802331163 / 500000000000 : ℝ)
  | 5 => (-16688924966831 / 1000000000000 : ℝ)
  | 6 => (-131604930959 / 7812500000 : ℝ)
  | 7 => (-1062695661013 / 62500000000 : ℝ)
  | 8 => (-17162030569287 / 1000000000000 : ℝ)
  | 9 => (-3464427708037 / 200000000000 : ℝ)
  | 10 => (-8741730961669 / 500000000000 : ℝ)
  | 11 => (-441150204739 / 25000000000 : ℝ)
  | 12 => (-17809784846181 / 1000000000000 : ℝ)
  | 13 => (-8987399718591 / 500000000000 : ℝ)
  | 14 => (-9070529771667 / 500000000000 : ℝ)
  | 15 => (-3661714556467 / 200000000000 : ℝ)
  | 16 => (-369546936179 / 20000000000 : ℝ)
  | 17 => (-4661847328787 / 250000000000 : ℝ)
  | 18 => (-18818708030241 / 1000000000000 : ℝ)
  | 19 => (-4636550469 / 244140625 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch058Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-15774537597747 / 1000000000000 : ℝ)
  | 1 => (-7962018543731 / 500000000000 : ℝ)
  | 2 => (-2009335796603 / 125000000000 : ℝ)
  | 3 => (-129811940817 / 8000000000 : ℝ)
  | 4 => (-2047432869869 / 125000000000 : ℝ)
  | 5 => (-661344186493 / 40000000000 : ℝ)
  | 6 => (-1668892496683 / 100000000000 : ℝ)
  | 7 => (-16845431162751 / 1000000000000 : ℝ)
  | 8 => (-17003130576207 / 1000000000000 : ℝ)
  | 9 => (-8581015284643 / 500000000000 : ℝ)
  | 10 => (-2165267317523 / 125000000000 : ℝ)
  | 11 => (-17483461923337 / 1000000000000 : ℝ)
  | 12 => (-17646008189559 / 1000000000000 : ℝ)
  | 13 => (-890489242309 / 50000000000 : ℝ)
  | 14 => (-17974799437181 / 1000000000000 : ℝ)
  | 15 => (-18141059543333 / 1000000000000 : ℝ)
  | 16 => (-9154286391167 / 500000000000 : ℝ)
  | 17 => (-18477346808949 / 1000000000000 : ℝ)
  | 18 => (-18647389315147 / 1000000000000 : ℝ)
  | 19 => (-117616925189 / 6250000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch058Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1160 : ℝ) + (j.val : ℝ)) / 1600)
      (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch058Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch058Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1160 : ℝ) + (j.val : ℝ)) / 1600)
    (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch058Neg100WeightLower j.val) (hpThetaShiftOneBatch058Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch058Neg100WeightLower, hpThetaShiftOneBatch058Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch058Neg100_integral_bounds :
    (-133891193739 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-259392131347 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch058Lower hpThetaJensenCellsBatch058Upper
    hpThetaShiftOneBatch058Neg100WeightLower hpThetaShiftOneBatch058Neg100WeightUpper hpThetaJensenCellsBatch058_bounds hpThetaShiftOneBatch058Neg100_weight_bounds
  have hl : (-133891193739 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch058Lower j * hpThetaShiftOneBatch058Neg100WeightLower j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftOneBatch058Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftOneBatch058Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch058Lower j * hpThetaShiftOneBatch058Neg100WeightUpper j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftOneBatch058Neg100WeightUpper j) / 1600) ≤ (-259392131347 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftOneBatch058Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1160 : ℝ) / 1600 = 58 / 80 by norm_num,
    show ((1160 : ℝ) + 20) / 1600 = (58 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch058Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1387404390953 / 1000000000000 : ℝ)
  | 1 => (-1409473765207 / 1000000000000 : ℝ)
  | 2 => (-715881631493 / 500000000000 : ℝ)
  | 3 => (-727137240813 / 500000000000 : ℝ)
  | 4 => (-295401805431 / 200000000000 : ℝ)
  | 5 => (-187496064291 / 125000000000 : ℝ)
  | 6 => (-76157728333 / 50000000000 : ℝ)
  | 7 => (-96660551029 / 62500000000 : ℝ)
  | 8 => (-314042580977 / 200000000000 : ℝ)
  | 9 => (-99630530121 / 62500000000 : ℝ)
  | 10 => (-1618197206533 / 1000000000000 : ℝ)
  | 11 => (-164254074653 / 100000000000 : ℝ)
  | 12 => (-833560389379 / 500000000000 : ℝ)
  | 13 => (-1652284169 / 976562500 : ℝ)
  | 14 => (-171699707231 / 100000000000 : ℝ)
  | 15 => (-1742296732487 / 1000000000000 : ℝ)
  | 16 => (-70713587307 / 40000000000 : ℝ)
  | 17 => (-358725529023 / 200000000000 : ℝ)
  | 18 => (-909831175619 / 500000000000 : ℝ)
  | 19 => (-230743192713 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch058Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-682776775773 / 500000000000 : ℝ)
  | 1 => (-173425548869 / 125000000000 : ℝ)
  | 2 => (-704736882603 / 500000000000 : ℝ)
  | 3 => (-286352652597 / 200000000000 : ℝ)
  | 4 => (-11634195853 / 8000000000 : ℝ)
  | 5 => (-738504513577 / 500000000000 : ℝ)
  | 6 => (-1499968514327 / 1000000000000 : ℝ)
  | 7 => (-1523154566659 / 1000000000000 : ℝ)
  | 8 => (-1546568816463 / 1000000000000 : ℝ)
  | 9 => (-392553226221 / 250000000000 : ℝ)
  | 10 => (-318817696387 / 200000000000 : ℝ)
  | 11 => (-404549301633 / 250000000000 : ℝ)
  | 12 => (-1642540746529 / 1000000000000 : ℝ)
  | 13 => (-1667120778757 / 1000000000000 : ℝ)
  | 14 => (-338387797811 / 200000000000 : ℝ)
  | 15 => (-1716997072309 / 1000000000000 : ℝ)
  | 16 => (-871148366243 / 500000000000 : ℝ)
  | 17 => (-883919841337 / 500000000000 : ℝ)
  | 18 => (-896813822557 / 500000000000 : ℝ)
  | 19 => (-1819662351237 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch058Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1160 : ℝ) + (j.val : ℝ)) / 1600)
      (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch058Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch058Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1160 : ℝ) + (j.val : ℝ)) / 1600)
    (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch058Neg65WeightLower j.val) (hpThetaShiftOneBatch058Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch058Neg65WeightLower, hpThetaShiftOneBatch058Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch058Neg65_integral_bounds :
    (-49358307511 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-11883929329 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch058Lower hpThetaJensenCellsBatch058Upper
    hpThetaShiftOneBatch058Neg65WeightLower hpThetaShiftOneBatch058Neg65WeightUpper hpThetaJensenCellsBatch058_bounds hpThetaShiftOneBatch058Neg65_weight_bounds
  have hl : (-49358307511 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch058Lower j * hpThetaShiftOneBatch058Neg65WeightLower j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftOneBatch058Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftOneBatch058Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch058Lower j * hpThetaShiftOneBatch058Neg65WeightUpper j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftOneBatch058Neg65WeightUpper j) / 1600) ≤ (-11883929329 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftOneBatch058Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1160 : ℝ) / 1600 = 58 / 80 by norm_num,
    show ((1160 : ℝ) + 20) / 1600 = (58 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch058Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (200474604489 / 500000000000 : ℝ)
  | 1 => (100464707119 / 250000000000 : ℝ)
  | 2 => (402752467053 / 1000000000000 : ℝ)
  | 3 => (100907475119 / 250000000000 : ℝ)
  | 4 => (80898180583 / 200000000000 : ℝ)
  | 5 => (405335246941 / 1000000000000 : ℝ)
  | 6 => (81232540703 / 200000000000 : ℝ)
  | 7 => (406973041981 / 1000000000000 : ℝ)
  | 8 => (203883015029 / 500000000000 : ℝ)
  | 9 => (102135358459 / 250000000000 : ℝ)
  | 10 => (102324754441 / 250000000000 : ℝ)
  | 11 => (82007708929 / 200000000000 : ℝ)
  | 12 => (102689943907 / 250000000000 : ℝ)
  | 13 => (411462470201 / 1000000000000 : ℝ)
  | 14 => (206073193091 / 500000000000 : ℝ)
  | 15 => (206405639857 / 500000000000 : ℝ)
  | 16 => (413456905253 / 1000000000000 : ℝ)
  | 17 => (207041507783 / 500000000000 : ℝ)
  | 18 => (414689361717 / 1000000000000 : ℝ)
  | 19 => (207637846533 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch058Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (401858828477 / 1000000000000 : ℝ)
  | 1 => (201376233527 / 500000000000 : ℝ)
  | 2 => (403629900477 / 1000000000000 : ℝ)
  | 3 => (101122725729 / 250000000000 : ℝ)
  | 4 => (202667623471 / 500000000000 : ℝ)
  | 5 => (101540675879 / 250000000000 : ℝ)
  | 6 => (203486520991 / 500000000000 : ℝ)
  | 7 => (407766030059 / 1000000000000 : ℝ)
  | 8 => (408541433837 / 1000000000000 : ℝ)
  | 9 => (81859803553 / 200000000000 : ℝ)
  | 10 => (205019272323 / 500000000000 : ℝ)
  | 11 => (410759775629 / 1000000000000 : ℝ)
  | 12 => (205731235101 / 500000000000 : ℝ)
  | 13 => (412146386183 / 1000000000000 : ℝ)
  | 14 => (82562255943 / 200000000000 : ℝ)
  | 15 => (206728452627 / 500000000000 : ℝ)
  | 16 => (414083015567 / 1000000000000 : ℝ)
  | 17 => (207344680859 / 500000000000 : ℝ)
  | 18 => (415275693067 / 1000000000000 : ℝ)
  | 19 => (415841757257 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch058Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1160 : ℝ) + (j.val : ℝ)) / 1600)
      (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch058Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch058Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1160 : ℝ) + (j.val : ℝ)) / 1600)
    (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch058Neg40WeightLower j.val) (hpThetaShiftOneBatch058Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch058Neg40WeightLower, hpThetaShiftOneBatch058Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch058Neg40_integral_bounds :
    (12323071873 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (12627320689 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch058Lower hpThetaJensenCellsBatch058Upper
    hpThetaShiftOneBatch058Neg40WeightLower hpThetaShiftOneBatch058Neg40WeightUpper hpThetaJensenCellsBatch058_bounds hpThetaShiftOneBatch058Neg40_weight_bounds
  have hl : (12323071873 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch058Lower j * hpThetaShiftOneBatch058Neg40WeightLower j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftOneBatch058Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftOneBatch058Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch058Lower j * hpThetaShiftOneBatch058Neg40WeightUpper j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftOneBatch058Neg40WeightUpper j) / 1600) ≤ (12627320689 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftOneBatch058Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1160 : ℝ) / 1600 = 58 / 80 by norm_num,
    show ((1160 : ℝ) + 20) / 1600 = (58 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch058Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-14936938477 / 500000000000 : ℝ)
  | 1 => (-14588471011 / 500000000000 : ℝ)
  | 2 => (-28474674063 / 1000000000000 : ℝ)
  | 3 => (-27767061021 / 1000000000000 : ℝ)
  | 4 => (-3381761363 / 125000000000 : ℝ)
  | 5 => (-2633575179 / 100000000000 : ℝ)
  | 6 => (-6403007957 / 250000000000 : ℝ)
  | 7 => (-12441459617 / 500000000000 : ℝ)
  | 8 => (-12074201149 / 500000000000 : ℝ)
  | 9 => (-1170423469 / 50000000000 : ℝ)
  | 10 => (-22663108913 / 1000000000000 : ℝ)
  | 11 => (-21912309401 / 1000000000000 : ℝ)
  | 12 => (-846242377 / 40000000000 : ℝ)
  | 13 => (-20394347637 / 1000000000000 : ℝ)
  | 14 => (-9813581383 / 500000000000 : ℝ)
  | 15 => (-1178405851 / 62500000000 : ℝ)
  | 16 => (-4519082267 / 250000000000 : ℝ)
  | 17 => (-17292658079 / 1000000000000 : ℝ)
  | 18 => (-4125867421 / 250000000000 : ℝ)
  | 19 => (-7854376499 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch058Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-29176942021 / 1000000000000 : ℝ)
  | 1 => (-14237337031 / 500000000000 : ℝ)
  | 2 => (-1388353051 / 50000000000 : ℝ)
  | 3 => (-27054090903 / 1000000000000 : ℝ)
  | 4 => (-26335751789 / 1000000000000 : ℝ)
  | 5 => (-25612031827 / 1000000000000 : ℝ)
  | 6 => (-24882919233 / 1000000000000 : ℝ)
  | 7 => (-24148402297 / 1000000000000 : ℝ)
  | 8 => (-23408469379 / 1000000000000 : ℝ)
  | 9 => (-1416444307 / 62500000000 : ℝ)
  | 10 => (-109561547 / 5000000000 : ℝ)
  | 11 => (-661126857 / 31250000000 : ℝ)
  | 12 => (-5098586909 / 250000000000 : ℝ)
  | 13 => (-3925432553 / 200000000000 : ℝ)
  | 14 => (-3770898723 / 200000000000 : ℝ)
  | 15 => (-18076329067 / 1000000000000 : ℝ)
  | 16 => (-8646329039 / 500000000000 : ℝ)
  | 17 => (-16503469683 / 1000000000000 : ℝ)
  | 18 => (-15708752997 / 1000000000000 : ℝ)
  | 19 => (-3727124303 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch058Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1160 : ℝ) + (j.val : ℝ)) / 1600)
      (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch058Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch058Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1160 : ℝ) + (j.val : ℝ)) / 1600)
    (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch058Neg20WeightLower j.val) (hpThetaShiftOneBatch058Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch058Neg20WeightLower, hpThetaShiftOneBatch058Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch058Neg20_integral_bounds :
    (-179763871 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-680531877 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch058Lower hpThetaJensenCellsBatch058Upper
    hpThetaShiftOneBatch058Neg20WeightLower hpThetaShiftOneBatch058Neg20WeightUpper hpThetaJensenCellsBatch058_bounds hpThetaShiftOneBatch058Neg20_weight_bounds
  have hl : (-179763871 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch058Lower j * hpThetaShiftOneBatch058Neg20WeightLower j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftOneBatch058Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftOneBatch058Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch058Lower j * hpThetaShiftOneBatch058Neg20WeightUpper j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftOneBatch058Neg20WeightUpper j) / 1600) ≤ (-680531877 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftOneBatch058Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1160 : ℝ) / 1600 = 58 / 80 by norm_num,
    show ((1160 : ℝ) + 20) / 1600 = (58 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch058Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch058Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch058Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch058Neg20_integral_bounds
end HodgeProofHP
