/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch029

/-! Exact signed weight and batch integral certificates, batch 29 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch029Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (23798584699 / 1000000000000 : ℝ)
  | 1 => (1223562329 / 50000000000 : ℝ)
  | 2 => (25149933009 / 1000000000000 : ℝ)
  | 3 => (25834632733 / 1000000000000 : ℝ)
  | 4 => (6631333389 / 250000000000 : ℝ)
  | 5 => (6805505581 / 250000000000 : ℝ)
  | 6 => (1745292807 / 62500000000 : ℝ)
  | 7 => (7158326553 / 250000000000 : ℝ)
  | 8 => (29347870121 / 1000000000000 : ℝ)
  | 9 => (30068359531 / 1000000000000 : ℝ)
  | 10 => (30794756309 / 1000000000000 : ℝ)
  | 11 => (15763520647 / 500000000000 : ℝ)
  | 12 => (16132597139 / 500000000000 : ℝ)
  | 13 => (33009193993 / 1000000000000 : ℝ)
  | 14 => (16879509051 / 500000000000 : ℝ)
  | 15 => (17257321591 / 500000000000 : ℝ)
  | 16 => (17638022357 / 500000000000 : ℝ)
  | 17 => (36043197067 / 1000000000000 : ℝ)
  | 18 => (36816073487 / 1000000000000 : ℝ)
  | 19 => (37594646083 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch029Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (24471246581 / 1000000000000 : ℝ)
  | 1 => (2514993301 / 100000000000 : ℝ)
  | 2 => (12917316367 / 500000000000 : ℝ)
  | 3 => (26525333557 / 1000000000000 : ℝ)
  | 4 => (1088880893 / 40000000000 : ℝ)
  | 5 => (27924684913 / 1000000000000 : ℝ)
  | 6 => (28633306213 / 1000000000000 : ℝ)
  | 7 => (14673935061 / 500000000000 : ℝ)
  | 8 => (7517089883 / 250000000000 : ℝ)
  | 9 => (3079475631 / 100000000000 : ℝ)
  | 10 => (6305408259 / 200000000000 : ℝ)
  | 11 => (32265194279 / 1000000000000 : ℝ)
  | 12 => (16504596997 / 500000000000 : ℝ)
  | 13 => (33759018103 / 1000000000000 : ℝ)
  | 14 => (34514643183 / 1000000000000 : ℝ)
  | 15 => (7055208943 / 200000000000 : ℝ)
  | 16 => (9010799267 / 250000000000 : ℝ)
  | 17 => (2301004593 / 62500000000 : ℝ)
  | 18 => (9398661521 / 250000000000 : ℝ)
  | 19 => (7675777163 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch029Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((580 : ℝ) + (j.val : ℝ)) / 1600)
      (((580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch029Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch029Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((580 : ℝ) + (j.val : ℝ)) / 1600)
    (((580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch029Neg100WeightLower j.val) (hpThetaShiftOneBatch029Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch029Neg100WeightLower, hpThetaShiftOneBatch029Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch029Neg100_integral_bounds :
    (85003375101 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (88268486853 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch029Lower hpThetaJensenCellsBatch029Upper
    hpThetaShiftOneBatch029Neg100WeightLower hpThetaShiftOneBatch029Neg100WeightUpper hpThetaJensenCellsBatch029_bounds hpThetaShiftOneBatch029Neg100_weight_bounds
  have hl : (85003375101 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch029Lower j * hpThetaShiftOneBatch029Neg100WeightLower j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftOneBatch029Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftOneBatch029Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch029Lower j * hpThetaShiftOneBatch029Neg100WeightUpper j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftOneBatch029Neg100WeightUpper j) / 1600) ≤ (88268486853 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftOneBatch029Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (580 : ℝ) / 1600 = 29 / 80 by norm_num,
    show ((580 : ℝ) + 20) / 1600 = (29 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch029Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-11982926133 / 500000000000 : ℝ)
  | 1 => (-11932782971 / 500000000000 : ℝ)
  | 2 => (-4752321929 / 200000000000 : ℝ)
  | 3 => (-4730790891 / 200000000000 : ℝ)
  | 4 => (-588564287 / 25000000000 : ℝ)
  | 5 => (-23427431851 / 1000000000000 : ℝ)
  | 6 => (-4661701347 / 200000000000 : ℝ)
  | 7 => (-724555229 / 31250000000 : ℝ)
  | 8 => (-23059184863 / 1000000000000 : ℝ)
  | 9 => (-22928730609 / 1000000000000 : ℝ)
  | 10 => (-5698593969 / 250000000000 : ℝ)
  | 11 => (-11328046009 / 500000000000 : ℝ)
  | 12 => (-22513850433 / 1000000000000 : ℝ)
  | 13 => (-22367622567 / 1000000000000 : ℝ)
  | 14 => (-22217379917 / 1000000000000 : ℝ)
  | 15 => (-11031547017 / 500000000000 : ℝ)
  | 16 => (-10952368261 / 500000000000 : ℝ)
  | 17 => (-21742279047 / 1000000000000 : ℝ)
  | 18 => (-10787846667 / 500000000000 : ℝ)
  | 19 => (-5351237793 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch029Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-23865565941 / 1000000000000 : ℝ)
  | 1 => (-5940402411 / 250000000000 : ℝ)
  | 2 => (-11826977227 / 500000000000 : ℝ)
  | 3 => (-23542571479 / 1000000000000 : ℝ)
  | 4 => (-468548637 / 20000000000 : ℝ)
  | 5 => (-11654253367 / 500000000000 : ℝ)
  | 6 => (-23185767327 / 1000000000000 : ℝ)
  | 7 => (-11529592431 / 500000000000 : ℝ)
  | 8 => (-1433045663 / 62500000000 : ℝ)
  | 9 => (-182355007 / 8000000000 : ℝ)
  | 10 => (-22656092017 / 1000000000000 : ℝ)
  | 11 => (-351778913 / 15625000000 : ℝ)
  | 12 => (-11183811283 / 500000000000 : ℝ)
  | 13 => (-5554344979 / 250000000000 : ℝ)
  | 14 => (-22063094033 / 1000000000000 : ℝ)
  | 15 => (-21904736521 / 1000000000000 : ℝ)
  | 16 => (-10871139523 / 500000000000 : ℝ)
  | 17 => (-21575693333 / 1000000000000 : ℝ)
  | 18 => (-21404951171 / 1000000000000 : ℝ)
  | 19 => (-10615012209 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch029Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((580 : ℝ) + (j.val : ℝ)) / 1600)
      (((580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch029Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch029Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((580 : ℝ) + (j.val : ℝ)) / 1600)
    (((580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch029Neg65WeightLower j.val) (hpThetaShiftOneBatch029Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch029Neg65WeightLower, hpThetaShiftOneBatch029Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch029Neg65_integral_bounds :
    (-25876964561 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-126822094209 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch029Lower hpThetaJensenCellsBatch029Upper
    hpThetaShiftOneBatch029Neg65WeightLower hpThetaShiftOneBatch029Neg65WeightUpper hpThetaJensenCellsBatch029_bounds hpThetaShiftOneBatch029Neg65_weight_bounds
  have hl : (-25876964561 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch029Lower j * hpThetaShiftOneBatch029Neg65WeightLower j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftOneBatch029Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftOneBatch029Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch029Lower j * hpThetaShiftOneBatch029Neg65WeightUpper j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftOneBatch029Neg65WeightUpper j) / 1600) ≤ (-126822094209 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftOneBatch029Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (580 : ℝ) / 1600 = 29 / 80 by norm_num,
    show ((580 : ℝ) + 20) / 1600 = (29 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch029Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-13875380231 / 500000000000 : ℝ)
  | 1 => (-27932146201 / 1000000000000 : ℝ)
  | 2 => (-1757066717 / 62500000000 : ℝ)
  | 3 => (-7073377261 / 250000000000 : ℝ)
  | 4 => (-3559181951 / 125000000000 : ℝ)
  | 5 => (-28652891767 / 1000000000000 : ℝ)
  | 6 => (-5766360409 / 200000000000 : ℝ)
  | 7 => (-14505085441 / 500000000000 : ℝ)
  | 8 => (-7296995659 / 250000000000 : ℝ)
  | 9 => (-14682610791 / 500000000000 : ℝ)
  | 10 => (-7385467979 / 250000000000 : ℝ)
  | 11 => (-29717917751 / 1000000000000 : ℝ)
  | 12 => (-7473335779 / 250000000000 : ℝ)
  | 13 => (-30068131963 / 1000000000000 : ℝ)
  | 14 => (-30242268161 / 1000000000000 : ℝ)
  | 15 => (-30415735499 / 1000000000000 : ℝ)
  | 16 => (-30588517683 / 1000000000000 : ℝ)
  | 17 => (-30760598343 / 1000000000000 : ℝ)
  | 18 => (-1237278441 / 40000000000 : ℝ)
  | 19 => (-31102589199 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch029Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-27568925399 / 1000000000000 : ℝ)
  | 1 => (-27750760461 / 1000000000000 : ℝ)
  | 2 => (-139660731 / 5000000000 : ℝ)
  | 3 => (-28113067471 / 1000000000000 : ℝ)
  | 4 => (-28293509043 / 1000000000000 : ℝ)
  | 5 => (-28473455607 / 1000000000000 : ℝ)
  | 6 => (-14326445883 / 500000000000 : ℝ)
  | 7 => (-7207950511 / 250000000000 : ℝ)
  | 8 => (-29010170881 / 1000000000000 : ℝ)
  | 9 => (-5837596527 / 200000000000 : ℝ)
  | 10 => (-29365221581 / 1000000000000 : ℝ)
  | 11 => (-5908374383 / 200000000000 : ℝ)
  | 12 => (-118871671 / 4000000000 : ℝ)
  | 13 => (-5978668623 / 200000000000 : ℝ)
  | 14 => (-15034065981 / 500000000000 : ℝ)
  | 15 => (-5906693 / 195312500 : ℝ)
  | 16 => (-15207867749 / 500000000000 : ℝ)
  | 17 => (-15294258841 / 500000000000 : ℝ)
  | 18 => (-15380299171 / 500000000000 : ℝ)
  | 19 => (-483311891 / 15625000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch029Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((580 : ℝ) + (j.val : ℝ)) / 1600)
      (((580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch029Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch029Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((580 : ℝ) + (j.val : ℝ)) / 1600)
    (((580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch029Neg40WeightLower j.val) (hpThetaShiftOneBatch029Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch029Neg40WeightLower, hpThetaShiftOneBatch029Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch029Neg40_integral_bounds :
    (-2605889659 / 15625000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-16346566003 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch029Lower hpThetaJensenCellsBatch029Upper
    hpThetaShiftOneBatch029Neg40WeightLower hpThetaShiftOneBatch029Neg40WeightUpper hpThetaJensenCellsBatch029_bounds hpThetaShiftOneBatch029Neg40_weight_bounds
  have hl : (-2605889659 / 15625000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch029Lower j * hpThetaShiftOneBatch029Neg40WeightLower j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftOneBatch029Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftOneBatch029Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch029Lower j * hpThetaShiftOneBatch029Neg40WeightUpper j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftOneBatch029Neg40WeightUpper j) / 1600) ≤ (-16346566003 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftOneBatch029Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (580 : ℝ) / 1600 = 29 / 80 by norm_num,
    show ((580 : ℝ) + 20) / 1600 = (29 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch029Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (120446989 / 250000000000 : ℝ)
  | 1 => (326711139 / 1000000000000 : ℝ)
  | 2 => (170734147 / 1000000000000 : ℝ)
  | 3 => (6928977 / 500000000000 : ℝ)
  | 4 => (-28783287 / 200000000000 : ℝ)
  | 5 => (-151293991 / 500000000000 : ℝ)
  | 6 => (-462155613 / 1000000000000 : ℝ)
  | 7 => (-38913639 / 62500000000 : ℝ)
  | 8 => (-31358987 / 40000000000 : ℝ)
  | 9 => (-473111897 / 500000000000 : ℝ)
  | 10 => (-554682187 / 500000000000 : ℝ)
  | 11 => (-636697587 / 500000000000 : ℝ)
  | 12 => (-719157461 / 500000000000 : ℝ)
  | 13 => (-1604122307 / 1000000000000 : ℝ)
  | 14 => (-1770815989 / 1000000000000 : ℝ)
  | 15 => (-1938394591 / 1000000000000 : ℝ)
  | 16 => (-2106856701 / 1000000000000 : ℝ)
  | 17 => (-18209607 / 8000000000 : ℝ)
  | 18 => (-2446425633 / 1000000000000 : ℝ)
  | 19 => (-2617529461 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch029Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (31798183 / 50000000000 : ℝ)
  | 1 => (481787957 / 1000000000000 : ℝ)
  | 2 => (16335557 / 50000000000 : ℝ)
  | 3 => (42683537 / 250000000000 : ℝ)
  | 4 => (2771591 / 200000000000 : ℝ)
  | 5 => (-71958217 / 500000000000 : ℝ)
  | 6 => (-302587981 / 1000000000000 : ℝ)
  | 7 => (-115538903 / 250000000000 : ℝ)
  | 8 => (-622618223 / 1000000000000 : ℝ)
  | 9 => (-391987337 / 500000000000 : ℝ)
  | 10 => (-946223793 / 1000000000000 : ℝ)
  | 11 => (-1109364373 / 1000000000000 : ℝ)
  | 12 => (-1273395173 / 1000000000000 : ℝ)
  | 13 => (-1438314921 / 1000000000000 : ℝ)
  | 14 => (-802061153 / 500000000000 : ℝ)
  | 15 => (-442703997 / 250000000000 : ℝ)
  | 16 => (-193839459 / 100000000000 : ℝ)
  | 17 => (-21068567 / 10000000000 : ℝ)
  | 18 => (-1138100437 / 500000000000 : ℝ)
  | 19 => (-76450801 / 31250000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch029Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((580 : ℝ) + (j.val : ℝ)) / 1600)
      (((580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch029Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch029Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((580 : ℝ) + (j.val : ℝ)) / 1600)
    (((580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch029Neg20WeightLower j.val) (hpThetaShiftOneBatch029Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch029Neg20WeightLower, hpThetaShiftOneBatch029Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch029Neg20_integral_bounds :
    (-2880258553 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-2380320911 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch029Lower hpThetaJensenCellsBatch029Upper
    hpThetaShiftOneBatch029Neg20WeightLower hpThetaShiftOneBatch029Neg20WeightUpper hpThetaJensenCellsBatch029_bounds hpThetaShiftOneBatch029Neg20_weight_bounds
  have hl : (-2880258553 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch029Lower j * hpThetaShiftOneBatch029Neg20WeightLower j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftOneBatch029Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftOneBatch029Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch029Lower j * hpThetaShiftOneBatch029Neg20WeightUpper j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftOneBatch029Neg20WeightUpper j) / 1600) ≤ (-2380320911 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftOneBatch029Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (580 : ℝ) / 1600 = 29 / 80 by norm_num,
    show ((580 : ℝ) + 20) / 1600 = (29 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch029Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch029Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch029Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch029Neg20_integral_bounds
end HodgeProofHP
