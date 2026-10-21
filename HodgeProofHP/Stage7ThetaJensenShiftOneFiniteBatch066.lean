/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch066

/-! Exact signed weight and batch integral certificates, batch 66 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch066Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-15151629308297 / 250000000000 : ℝ)
  | 1 => (-6106123335851 / 100000000000 : ℝ)
  | 2 => (-61518806608253 / 1000000000000 : ℝ)
  | 3 => (-30989625903021 / 500000000000 : ℝ)
  | 4 => (-62442583837533 / 1000000000000 : ℝ)
  | 5 => (-31454408825311 / 500000000000 : ℝ)
  | 6 => (-63377968255637 / 1000000000000 : ℝ)
  | 7 => (-63850050725551 / 1000000000000 : ℝ)
  | 8 => (-2573003207847 / 40000000000 : ℝ)
  | 9 => (-64803071866371 / 1000000000000 : ℝ)
  | 10 => (-65284040998249 / 1000000000000 : ℝ)
  | 11 => (-64226565349 / 976562500 : ℝ)
  | 12 => (-33127486506489 / 500000000000 : ℝ)
  | 13 => (-16686241684537 / 250000000000 : ℝ)
  | 14 => (-16809499902513 / 250000000000 : ℝ)
  | 15 => (-67734087210133 / 1000000000000 : ℝ)
  | 16 => (-68233245184319 / 1000000000000 : ℝ)
  | 17 => (-34367744621617 / 500000000000 : ℝ)
  | 18 => (-86551043953 / 1250000000 : ℝ)
  | 19 => (-17437324695613 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch066Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-60154643470491 / 1000000000000 : ℝ)
  | 1 => (-60606517233187 / 1000000000000 : ℝ)
  | 2 => (-61061233358509 / 1000000000000 : ℝ)
  | 3 => (-15379701652063 / 250000000000 : ℝ)
  | 4 => (-61979251806041 / 1000000000000 : ℝ)
  | 5 => (-15610645959383 / 250000000000 : ℝ)
  | 6 => (-62908817650621 / 1000000000000 : ℝ)
  | 7 => (-15844492063909 / 250000000000 : ℝ)
  | 8 => (-1277001014511 / 20000000000 : ℝ)
  | 9 => (-32162540098087 / 500000000000 : ℝ)
  | 10 => (-6480307186637 / 100000000000 : ℝ)
  | 11 => (-8160505124781 / 125000000000 : ℝ)
  | 12 => (-526144023339 / 8000000000 : ℝ)
  | 13 => (-66254973012977 / 1000000000000 : ℝ)
  | 14 => (-66744966738147 / 1000000000000 : ℝ)
  | 15 => (-67237999610051 / 1000000000000 : ℝ)
  | 16 => (-16933521802533 / 250000000000 : ℝ)
  | 17 => (-34116622592159 / 500000000000 : ℝ)
  | 18 => (-68735489243233 / 1000000000000 : ℝ)
  | 19 => (-69240835162399 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch066Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1320 : ℝ) + (j.val : ℝ)) / 1600)
      (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch066Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch066Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1320 : ℝ) + (j.val : ℝ)) / 1600)
    (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch066Neg100WeightLower j.val) (hpThetaShiftOneBatch066Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch066Neg100WeightLower, hpThetaShiftOneBatch066Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch066Neg100_integral_bounds :
    (-159943896557 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-38661957949 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch066Lower hpThetaJensenCellsBatch066Upper
    hpThetaShiftOneBatch066Neg100WeightLower hpThetaShiftOneBatch066Neg100WeightUpper hpThetaJensenCellsBatch066_bounds hpThetaShiftOneBatch066Neg100_weight_bounds
  have hl : (-159943896557 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch066Lower j * hpThetaShiftOneBatch066Neg100WeightLower j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftOneBatch066Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftOneBatch066Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch066Lower j * hpThetaShiftOneBatch066Neg100WeightUpper j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftOneBatch066Neg100WeightUpper j) / 1600) ≤ (-38661957949 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftOneBatch066Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1320 : ℝ) / 1600 = 66 / 80 by norm_num,
    show ((1320 : ℝ) + 20) / 1600 = (66 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch066Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-9048017768651 / 1000000000000 : ℝ)
  | 1 => (-4566226864199 / 500000000000 : ℝ)
  | 2 => (-2304375540387 / 250000000000 : ℝ)
  | 3 => (-4651583286433 / 500000000000 : ℝ)
  | 4 => (-9389450482799 / 1000000000000 : ℝ)
  | 5 => (-9476357427531 / 1000000000000 : ℝ)
  | 6 => (-9563890959031 / 1000000000000 : ℝ)
  | 7 => (-9652054645113 / 1000000000000 : ℝ)
  | 8 => (-4870426034743 / 500000000000 : ℝ)
  | 9 => (-9830286831807 / 1000000000000 : ℝ)
  | 10 => (-496018127387 / 50000000000 : ℝ)
  | 11 => (-5005541424501 / 500000000000 : ℝ)
  | 12 => (-404098055337 / 40000000000 : ℝ)
  | 13 => (-318577244219 / 31250000000 : ℝ)
  | 14 => (-10287147823967 / 1000000000000 : ℝ)
  | 15 => (-2595120776699 / 250000000000 : ℝ)
  | 16 => (-5237240688159 / 500000000000 : ℝ)
  | 17 => (-10569146361741 / 1000000000000 : ℝ)
  | 18 => (-10664481808713 / 1000000000000 : ℝ)
  | 19 => (-10760491479377 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch066Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8964190793169 / 1000000000000 : ℝ)
  | 1 => (-180960355373 / 20000000000 : ℝ)
  | 2 => (-9132453728397 / 1000000000000 : ℝ)
  | 3 => (-9217502161547 / 1000000000000 : ℝ)
  | 4 => (-1860633314573 / 200000000000 : ℝ)
  | 5 => (-4694725241399 / 500000000000 : ℝ)
  | 6 => (-947635742753 / 100000000000 : ℝ)
  | 7 => (-956389095903 / 100000000000 : ℝ)
  | 8 => (-1206506830639 / 125000000000 : ℝ)
  | 9 => (-1948170413897 / 200000000000 : ℝ)
  | 10 => (-4915143415903 / 500000000000 : ℝ)
  | 11 => (-9920362547739 / 1000000000000 : ℝ)
  | 12 => (-10011082849001 / 1000000000000 : ℝ)
  | 13 => (-78925401433 / 7812500000 : ℝ)
  | 14 => (-10194471815007 / 1000000000000 : ℝ)
  | 15 => (-5143573911983 / 500000000000 : ℝ)
  | 16 => (-2076096621359 / 200000000000 : ℝ)
  | 17 => (-10474481376317 / 1000000000000 : ℝ)
  | 18 => (-528457318087 / 50000000000 : ℝ)
  | 19 => (-1333060226089 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch066Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1320 : ℝ) + (j.val : ℝ)) / 1600)
      (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch066Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch066Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1320 : ℝ) + (j.val : ℝ)) / 1600)
    (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch066Neg65WeightLower j.val) (hpThetaShiftOneBatch066Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch066Neg65WeightLower, hpThetaShiftOneBatch066Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch066Neg65_integral_bounds :
    (-3033330301 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-11711209539 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch066Lower hpThetaJensenCellsBatch066Upper
    hpThetaShiftOneBatch066Neg65WeightLower hpThetaShiftOneBatch066Neg65WeightUpper hpThetaJensenCellsBatch066_bounds hpThetaShiftOneBatch066Neg65_weight_bounds
  have hl : (-3033330301 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch066Lower j * hpThetaShiftOneBatch066Neg65WeightLower j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftOneBatch066Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftOneBatch066Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch066Lower j * hpThetaShiftOneBatch066Neg65WeightUpper j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftOneBatch066Neg65WeightUpper j) / 1600) ≤ (-11711209539 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftOneBatch066Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1320 : ℝ) / 1600 = 66 / 80 by norm_num,
    show ((1320 : ℝ) + 20) / 1600 = (66 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch066Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (138746371729 / 1000000000000 : ℝ)
  | 1 => (4152746083 / 31250000000 : ℝ)
  | 2 => (126951087037 / 1000000000000 : ℝ)
  | 3 => (120935416539 / 1000000000000 : ℝ)
  | 4 => (28710066933 / 250000000000 : ℝ)
  | 5 => (4346601683 / 40000000000 : ℝ)
  | 6 => (6400571119 / 62500000000 : ℝ)
  | 7 => (4803597521 / 50000000000 : ℝ)
  | 8 => (89652871679 / 1000000000000 : ℝ)
  | 9 => (83151290579 / 1000000000000 : ℝ)
  | 10 => (76566592849 / 1000000000000 : ℝ)
  | 11 => (34949080519 / 500000000000 : ℝ)
  | 12 => (63145374499 / 1000000000000 : ℝ)
  | 13 => (11261521877 / 200000000000 : ℝ)
  | 14 => (4938423863 / 100000000000 : ℝ)
  | 15 => (42374631939 / 1000000000000 : ℝ)
  | 16 => (35278155781 / 1000000000000 : ℝ)
  | 17 => (28094173367 / 1000000000000 : ℝ)
  | 18 => (20822044651 / 1000000000000 : ℝ)
  | 19 => (2692225261 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch066Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (72263583749 / 500000000000 : ℝ)
  | 1 => (13874637173 / 100000000000 : ℝ)
  | 2 => (132887874657 / 1000000000000 : ℝ)
  | 3 => (63475543519 / 500000000000 : ℝ)
  | 4 => (6046770827 / 50000000000 : ℝ)
  | 5 => (114840267733 / 1000000000000 : ℝ)
  | 6 => (27166260519 / 250000000000 : ℝ)
  | 7 => (20481827581 / 200000000000 : ℝ)
  | 8 => (96071950421 / 1000000000000 : ℝ)
  | 9 => (35020653 / 390625000 : ℝ)
  | 10 => (4157564529 / 50000000000 : ℝ)
  | 11 => (1531331857 / 20000000000 : ℝ)
  | 12 => (69898161039 / 1000000000000 : ℝ)
  | 13 => (126290749 / 2000000000 : ℝ)
  | 14 => (28153804693 / 500000000000 : ℝ)
  | 15 => (49384238631 / 1000000000000 : ℝ)
  | 16 => (2118731597 / 50000000000 : ℝ)
  | 17 => (17639077891 / 500000000000 : ℝ)
  | 18 => (3511771671 / 125000000000 : ℝ)
  | 19 => (5205511163 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch066Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1320 : ℝ) + (j.val : ℝ)) / 1600)
      (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch066Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch066Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1320 : ℝ) + (j.val : ℝ)) / 1600)
    (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch066Neg40WeightLower j.val) (hpThetaShiftOneBatch066Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch066Neg40WeightLower, hpThetaShiftOneBatch066Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch066Neg40_integral_bounds :
    (24749649 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (43860927 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch066Lower hpThetaJensenCellsBatch066Upper
    hpThetaShiftOneBatch066Neg40WeightLower hpThetaShiftOneBatch066Neg40WeightUpper hpThetaJensenCellsBatch066_bounds hpThetaShiftOneBatch066Neg40_weight_bounds
  have hl : (24749649 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch066Lower j * hpThetaShiftOneBatch066Neg40WeightLower j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftOneBatch066Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftOneBatch066Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch066Lower j * hpThetaShiftOneBatch066Neg40WeightUpper j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftOneBatch066Neg40WeightUpper j) / 1600) ≤ (43860927 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftOneBatch066Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1320 : ℝ) / 1600 = 66 / 80 by norm_num,
    show ((1320 : ℝ) + 20) / 1600 = (66 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch066Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (155149354189 / 1000000000000 : ℝ)
  | 1 => (31357478683 / 200000000000 : ℝ)
  | 2 => (39607826367 / 250000000000 : ℝ)
  | 3 => (80040540539 / 500000000000 : ℝ)
  | 4 => (32347342153 / 200000000000 : ℝ)
  | 5 => (163398184833 / 1000000000000 : ℝ)
  | 6 => (41266373343 / 250000000000 : ℝ)
  | 7 => (166738626257 / 1000000000000 : ℝ)
  | 8 => (168417573147 / 1000000000000 : ℝ)
  | 9 => (170102323481 / 1000000000000 : ℝ)
  | 10 => (171792866479 / 1000000000000 : ℝ)
  | 11 => (86744595571 / 500000000000 : ℝ)
  | 12 => (175191286249 / 1000000000000 : ℝ)
  | 13 => (35379828071 / 200000000000 : ℝ)
  | 14 => (178612741793 / 1000000000000 : ℝ)
  | 15 => (180332078669 / 1000000000000 : ℝ)
  | 16 => (36411427773 / 200000000000 : ℝ)
  | 17 => (11486744377 / 62500000000 : ℝ)
  | 18 => (37104875919 / 200000000000 : ℝ)
  | 19 => (46816633687 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch066Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (19598424177 / 125000000000 : ℝ)
  | 1 => (158431305469 / 1000000000000 : ℝ)
  | 2 => (160081081079 / 1000000000000 : ℝ)
  | 3 => (80868355383 / 500000000000 : ℝ)
  | 4 => (81699092417 / 500000000000 : ℝ)
  | 5 => (165065493373 / 1000000000000 : ℝ)
  | 6 => (83369313129 / 500000000000 : ℝ)
  | 7 => (42104393287 / 250000000000 : ℝ)
  | 8 => (85051161741 / 500000000000 : ℝ)
  | 9 => (2147410831 / 12500000000 : ℝ)
  | 10 => (173489191143 / 1000000000000 : ℝ)
  | 11 => (140153029 / 800000000 : ℝ)
  | 12 => (44224785089 / 250000000000 : ℝ)
  | 13 => (89306370897 / 500000000000 : ℝ)
  | 14 => (18033207867 / 100000000000 : ℝ)
  | 15 => (91028569433 / 500000000000 : ℝ)
  | 16 => (183787910033 / 1000000000000 : ℝ)
  | 17 => (46381094899 / 250000000000 : ℝ)
  | 18 => (187266534749 / 1000000000000 : ℝ)
  | 19 => (189014362457 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch066Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1320 : ℝ) + (j.val : ℝ)) / 1600)
      (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch066Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch066Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1320 : ℝ) + (j.val : ℝ)) / 1600)
    (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch066Neg20WeightLower j.val) (hpThetaShiftOneBatch066Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch066Neg20WeightLower, hpThetaShiftOneBatch066Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch066Neg20_integral_bounds :
    (81755929 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (423831921 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch066Lower hpThetaJensenCellsBatch066Upper
    hpThetaShiftOneBatch066Neg20WeightLower hpThetaShiftOneBatch066Neg20WeightUpper hpThetaJensenCellsBatch066_bounds hpThetaShiftOneBatch066Neg20_weight_bounds
  have hl : (81755929 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch066Lower j * hpThetaShiftOneBatch066Neg20WeightLower j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftOneBatch066Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftOneBatch066Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch066Lower j * hpThetaShiftOneBatch066Neg20WeightUpper j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftOneBatch066Neg20WeightUpper j) / 1600) ≤ (423831921 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftOneBatch066Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1320 : ℝ) / 1600 = 66 / 80 by norm_num,
    show ((1320 : ℝ) + 20) / 1600 = (66 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch066Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch066Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch066Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch066Neg20_integral_bounds
end HodgeProofHP
