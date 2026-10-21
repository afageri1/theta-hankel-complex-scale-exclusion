/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch059

/-! Exact signed weight and batch integral certificates, batch 59 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch059Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-9582602595957 / 500000000000 : ℝ)
  | 1 => (-9670199642547 / 500000000000 : ℝ)
  | 2 => (-19516900880647 / 1000000000000 : ℝ)
  | 3 => (-19694717896701 / 1000000000000 : ℝ)
  | 4 => (-4968464572393 / 250000000000 : ℝ)
  | 5 => (-200543300539 / 10000000000 : ℝ)
  | 6 => (-20236141222797 / 1000000000000 : ℝ)
  | 7 => (-10209649933993 / 500000000000 : ℝ)
  | 8 => (-2575476762493 / 125000000000 : ℝ)
  | 9 => (-20789692068047 / 1000000000000 : ℝ)
  | 10 => (-2622117745089 / 125000000000 : ℝ)
  | 11 => (-10582786002771 / 500000000000 : ℝ)
  | 12 => (-21355590469469 / 1000000000000 : ℝ)
  | 13 => (-215470056589 / 10000000000 : ℝ)
  | 14 => (-10869912959931 / 500000000000 : ℝ)
  | 15 => (-5483514909537 / 250000000000 : ℝ)
  | 16 => (-1106485761973 / 50000000000 : ℝ)
  | 17 => (-558170029739 / 25000000000 : ℝ)
  | 18 => (-22525325994413 / 1000000000000 : ℝ)
  | 19 => (-4545059640067 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch059Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-18991310721023 / 1000000000000 : ℝ)
  | 1 => (-19165205191913 / 1000000000000 : ℝ)
  | 2 => (-19340399285093 / 1000000000000 : ℝ)
  | 3 => (-9758450440323 / 500000000000 : ℝ)
  | 4 => (-196947178967 / 10000000000 : ℝ)
  | 5 => (-19873858289571 / 1000000000000 : ℝ)
  | 6 => (-20054330053899 / 1000000000000 : ℝ)
  | 7 => (-5059035305699 / 250000000000 : ℝ)
  | 8 => (-4083859973597 / 200000000000 : ℝ)
  | 9 => (-20603814099943 / 1000000000000 : ℝ)
  | 10 => (-10394846034023 / 500000000000 : ℝ)
  | 11 => (-20976941960711 / 1000000000000 : ℝ)
  | 12 => (-21165572005541 / 1000000000000 : ℝ)
  | 13 => (-5338897617367 / 250000000000 : ℝ)
  | 14 => (-21547005658899 / 1000000000000 : ℝ)
  | 15 => (-21739825919861 / 1000000000000 : ℝ)
  | 16 => (-21934059638147 / 1000000000000 : ℝ)
  | 17 => (-22129715239459 / 1000000000000 : ℝ)
  | 18 => (-22326801189559 / 1000000000000 : ℝ)
  | 19 => (-5631331498603 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch059Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1180 : ℝ) + (j.val : ℝ)) / 1600)
      (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch059Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch059Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1180 : ℝ) + (j.val : ℝ)) / 1600)
    (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch059Neg100WeightLower j.val) (hpThetaShiftOneBatch059Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch059Neg100WeightLower, hpThetaShiftOneBatch059Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch059Neg100_integral_bounds :
    (-241979207193 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-234369271381 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch059Lower hpThetaJensenCellsBatch059Upper
    hpThetaShiftOneBatch059Neg100WeightLower hpThetaShiftOneBatch059Neg100WeightUpper hpThetaJensenCellsBatch059_bounds hpThetaShiftOneBatch059Neg100_weight_bounds
  have hl : (-241979207193 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch059Lower j * hpThetaShiftOneBatch059Neg100WeightLower j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftOneBatch059Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftOneBatch059Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch059Lower j * hpThetaShiftOneBatch059Neg100WeightUpper j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftOneBatch059Neg100WeightUpper j) / 1600) ≤ (-234369271381 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftOneBatch059Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1180 : ℝ) / 1600 = 59 / 80 by norm_num,
    show ((1180 : ℝ) + 20) / 1600 = (59 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch059Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1872478966437 / 1000000000000 : ℝ)
  | 1 => (-949632192329 / 500000000000 : ℝ)
  | 2 => (-1926303564931 / 1000000000000 : ℝ)
  | 3 => (-488399571297 / 250000000000 : ℝ)
  | 4 => (-247643791597 / 125000000000 : ℝ)
  | 5 => (-200896150449 / 100000000000 : ℝ)
  | 6 => (-2037033606607 / 1000000000000 : ℝ)
  | 7 => (-129085528433 / 62500000000 : ℝ)
  | 8 => (-418793574963 / 200000000000 : ℝ)
  | 9 => (-1061416850613 / 500000000000 : ℝ)
  | 10 => (-1075983889377 / 500000000000 : ℝ)
  | 11 => (-1090685980831 / 500000000000 : ℝ)
  | 12 => (-276381014241 / 125000000000 : ℝ)
  | 13 => (-2240998109273 / 1000000000000 : ℝ)
  | 14 => (-2271223831207 / 1000000000000 : ℝ)
  | 15 => (-2301727173063 / 1000000000000 : ℝ)
  | 16 => (-2332510038037 / 1000000000000 : ℝ)
  | 17 => (-2363574339223 / 1000000000000 : ℝ)
  | 18 => (-299365249957 / 125000000000 : ℝ)
  | 19 => (-2426554952349 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch059Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1845945541703 / 1000000000000 : ℝ)
  | 1 => (-468119741609 / 250000000000 : ℝ)
  | 2 => (-1899264384657 / 1000000000000 : ℝ)
  | 3 => (-192630356493 / 100000000000 : ℝ)
  | 4 => (-1953598285187 / 1000000000000 : ℝ)
  | 5 => (-79246013311 / 40000000000 : ℝ)
  | 6 => (-2008961504489 / 1000000000000 : ℝ)
  | 7 => (-1018516803303 / 500000000000 : ℝ)
  | 8 => (-2065368454927 / 1000000000000 : ℝ)
  | 9 => (-1046983937407 / 500000000000 : ℝ)
  | 10 => (-84913348049 / 40000000000 : ℝ)
  | 11 => (-2151967778753 / 1000000000000 : ℝ)
  | 12 => (-2181371961661 / 1000000000000 : ℝ)
  | 13 => (-2211048113927 / 1000000000000 : ℝ)
  | 14 => (-280124763659 / 125000000000 : ℝ)
  | 15 => (-1135611915603 / 500000000000 : ℝ)
  | 16 => (-1150863586531 / 500000000000 : ℝ)
  | 17 => (-583127509509 / 250000000000 : ℝ)
  | 18 => (-1181787169611 / 500000000000 : ℝ)
  | 19 => (-478984399931 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch059Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1180 : ℝ) + (j.val : ℝ)) / 1600)
      (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch059Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch059Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1180 : ℝ) + (j.val : ℝ)) / 1600)
    (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch059Neg65WeightLower j.val) (hpThetaShiftOneBatch059Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch059Neg65WeightLower, hpThetaShiftOneBatch059Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch059Neg65_integral_bounds :
    (-9894280357 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-11922712013 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch059Lower hpThetaJensenCellsBatch059Upper
    hpThetaShiftOneBatch059Neg65WeightLower hpThetaShiftOneBatch059Neg65WeightUpper hpThetaJensenCellsBatch059_bounds hpThetaShiftOneBatch059Neg65_weight_bounds
  have hl : (-9894280357 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch059Lower j * hpThetaShiftOneBatch059Neg65WeightLower j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftOneBatch059Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftOneBatch059Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch059Lower j * hpThetaShiftOneBatch059Neg65WeightUpper j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftOneBatch059Neg65WeightUpper j) / 1600) ≤ (-11922712013 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftOneBatch059Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1180 : ℝ) / 1600 = 59 / 80 by norm_num,
    show ((1180 : ℝ) + 20) / 1600 = (59 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch059Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (51980219657 / 125000000000 : ℝ)
  | 1 => (26024206263 / 62500000000 : ℝ)
  | 2 => (416912066111 / 1000000000000 : ℝ)
  | 3 => (208707898709 / 500000000000 : ℝ)
  | 4 => (83579646967 / 200000000000 : ℝ)
  | 5 => (418359117313 / 1000000000000 : ℝ)
  | 6 => (209399091021 / 500000000000 : ℝ)
  | 7 => (419215164443 / 1000000000000 : ℝ)
  | 8 => (419609798159 / 1000000000000 : ℝ)
  | 9 => (52497726881 / 125000000000 : ℝ)
  | 10 => (105082736293 / 250000000000 : ℝ)
  | 11 => (84131383359 / 200000000000 : ℝ)
  | 12 => (42095945637 / 100000000000 : ℝ)
  | 13 => (421238288533 / 1000000000000 : ℝ)
  | 14 => (84298627219 / 200000000000 : ℝ)
  | 15 => (13178866251 / 31250000000 : ℝ)
  | 16 => (10548243987 / 25000000000 : ℝ)
  | 17 => (105527742931 / 250000000000 : ℝ)
  | 18 => (422267072193 / 1000000000000 : ℝ)
  | 19 => (26399860903 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch059Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (416387300209 / 1000000000000 : ℝ)
  | 1 => (6514251033 / 15625000000 : ℝ)
  | 2 => (417415797419 / 1000000000000 : ℝ)
  | 3 => (104474558709 / 250000000000 : ℝ)
  | 4 => (209179558657 / 500000000000 : ℝ)
  | 5 => (418798182043 / 1000000000000 : ℝ)
  | 6 => (104803791111 / 250000000000 : ℝ)
  | 7 => (5245122477 / 12500000000 : ℝ)
  | 8 => (419981815049 / 1000000000000 : ℝ)
  | 9 => (420330945173 / 1000000000000 : ℝ)
  | 10 => (105164229199 / 250000000000 : ℝ)
  | 11 => (420959456371 / 1000000000000 : ℝ)
  | 12 => (210619144267 / 500000000000 : ℝ)
  | 13 => (13171660503 / 31250000000 : ℝ)
  | 14 => (421723720033 / 1000000000000 : ℝ)
  | 15 => (421929759481 / 1000000000000 : ℝ)
  | 16 => (16884438869 / 40000000000 : ℝ)
  | 17 => (211133536097 / 500000000000 : ℝ)
  | 18 => (422397774449 / 1000000000000 : ℝ)
  | 19 => (422502790179 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch059Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1180 : ℝ) + (j.val : ℝ)) / 1600)
      (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch059Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch059Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1180 : ℝ) + (j.val : ℝ)) / 1600)
    (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch059Neg40WeightLower j.val) (hpThetaShiftOneBatch059Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch059Neg40WeightLower, hpThetaShiftOneBatch059Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch059Neg40_integral_bounds :
    (2383471999 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (2440855427 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch059Lower hpThetaJensenCellsBatch059Upper
    hpThetaShiftOneBatch059Neg40WeightLower hpThetaShiftOneBatch059Neg40WeightUpper hpThetaJensenCellsBatch059_bounds hpThetaShiftOneBatch059Neg40_weight_bounds
  have hl : (2383471999 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch059Lower j * hpThetaShiftOneBatch059Neg40WeightLower j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftOneBatch059Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftOneBatch059Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch059Lower j * hpThetaShiftOneBatch059Neg40WeightUpper j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftOneBatch059Neg40WeightUpper j) / 1600) ≤ (2440855427 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftOneBatch059Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1180 : ℝ) / 1600 = 59 / 80 by norm_num,
    show ((1180 : ℝ) + 20) / 1600 = (59 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch059Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-14908497213 / 1000000000000 : ℝ)
  | 1 => (-14102691603 / 1000000000000 : ℝ)
  | 2 => (-13291325521 / 1000000000000 : ℝ)
  | 3 => (-12474388403 / 1000000000000 : ℝ)
  | 4 => (-5825934883 / 500000000000 : ℝ)
  | 5 => (-1082375921 / 100000000000 : ℝ)
  | 6 => (-4995023209 / 500000000000 : ℝ)
  | 7 => (-9150721159 / 1000000000000 : ℝ)
  | 8 => (-4152886643 / 500000000000 : ℝ)
  | 9 => (-232974773 / 31250000000 : ℝ)
  | 10 => (-1319793907 / 200000000000 : ℝ)
  | 11 => (-5737093797 / 1000000000000 : ℝ)
  | 12 => (-121738893 / 25000000000 : ℝ)
  | 13 => (-1998172797 / 500000000000 : ℝ)
  | 14 => (-1558726899 / 500000000000 : ℝ)
  | 15 => (-5582177 / 2500000000 : ℝ)
  | 16 => (-33564679 / 25000000000 : ℝ)
  | 17 => (-44659353 / 100000000000 : ℝ)
  | 18 => (455119347 / 1000000000000 : ℝ)
  | 19 => (1362560633 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch059Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-7051345801 / 500000000000 : ℝ)
  | 1 => (-166141569 / 12500000000 : ℝ)
  | 2 => (-6237194201 / 500000000000 : ℝ)
  | 3 => (-2330373953 / 200000000000 : ℝ)
  | 4 => (-10823759209 / 1000000000000 : ℝ)
  | 5 => (-9990046417 / 1000000000000 : ℝ)
  | 6 => (-4575360579 / 500000000000 : ℝ)
  | 7 => (-1661154657 / 200000000000 : ℝ)
  | 8 => (-1491038547 / 200000000000 : ℝ)
  | 9 => (-3299484767 / 500000000000 : ℝ)
  | 10 => (-1434273449 / 250000000000 : ℝ)
  | 11 => (-4869555719 / 1000000000000 : ℝ)
  | 12 => (-3996345593 / 1000000000000 : ℝ)
  | 13 => (-3117453797 / 1000000000000 : ℝ)
  | 14 => (-2232870799 / 1000000000000 : ℝ)
  | 15 => (-1342587159 / 1000000000000 : ℝ)
  | 16 => (-446593529 / 1000000000000 : ℝ)
  | 17 => (113779837 / 250000000000 : ℝ)
  | 18 => (681280317 / 500000000000 : ℝ)
  | 19 => (1137869699 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch059Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1180 : ℝ) + (j.val : ℝ)) / 1600)
      (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch059Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch059Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1180 : ℝ) + (j.val : ℝ)) / 1600)
    (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch059Neg20WeightLower j.val) (hpThetaShiftOneBatch059Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch059Neg20WeightLower, hpThetaShiftOneBatch059Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch059Neg20_integral_bounds :
    (-85381227 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-73650681 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch059Lower hpThetaJensenCellsBatch059Upper
    hpThetaShiftOneBatch059Neg20WeightLower hpThetaShiftOneBatch059Neg20WeightUpper hpThetaJensenCellsBatch059_bounds hpThetaShiftOneBatch059Neg20_weight_bounds
  have hl : (-85381227 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch059Lower j * hpThetaShiftOneBatch059Neg20WeightLower j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftOneBatch059Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftOneBatch059Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch059Lower j * hpThetaShiftOneBatch059Neg20WeightUpper j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftOneBatch059Neg20WeightUpper j) / 1600) ≤ (-73650681 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftOneBatch059Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1180 : ℝ) / 1600 = 59 / 80 by norm_num,
    show ((1180 : ℝ) + 20) / 1600 = (59 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch059Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch059Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch059Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch059Neg20_integral_bounds
end HodgeProofHP
