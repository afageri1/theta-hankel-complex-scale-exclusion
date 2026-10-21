/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch062

/-! Exact signed weight and batch integral certificates, batch 62 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch062Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6456300434141 / 200000000000 : ℝ)
  | 1 => (-16275269706629 / 500000000000 : ℝ)
  | 2 => (-3282143187249 / 100000000000 : ℝ)
  | 3 => (-33094190021819 / 1000000000000 : ℝ)
  | 4 => (-16684412191023 / 500000000000 : ℝ)
  | 5 => (-33645345521523 / 1000000000000 : ℝ)
  | 6 => (-33923764056317 / 1000000000000 : ℝ)
  | 7 => (-17102045325189 / 500000000000 : ℝ)
  | 8 => (-6897267203141 / 200000000000 : ℝ)
  | 9 => (-34770510912517 / 1000000000000 : ℝ)
  | 10 => (-35056626149413 / 1000000000000 : ℝ)
  | 11 => (-35344692583549 / 1000000000000 : ℝ)
  | 12 => (-35634721120801 / 1000000000000 : ℝ)
  | 13 => (-35926722715937 / 1000000000000 : ℝ)
  | 14 => (-7244141674557 / 200000000000 : ℝ)
  | 15 => (-18258344572201 / 500000000000 : ℝ)
  | 16 => (-147258704533 / 4000000000 : ℝ)
  | 17 => (-18557340245679 / 500000000000 : ℝ)
  | 18 => (-37416713420501 / 1000000000000 : ℝ)
  | 19 => (-2357549135773 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch062Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-32014309718631 / 1000000000000 : ℝ)
  | 1 => (-2017593885669 / 62500000000 : ℝ)
  | 2 => (-32550539413257 / 1000000000000 : ℝ)
  | 3 => (-32821431872489 / 1000000000000 : ℝ)
  | 4 => (-16547095010909 / 500000000000 : ℝ)
  | 5 => (-6673764876409 / 200000000000 : ℝ)
  | 6 => (-16822672760761 / 500000000000 : ℝ)
  | 7 => (-8480941014079 / 250000000000 : ℝ)
  | 8 => (-34204090650377 / 1000000000000 : ℝ)
  | 9 => (-4310792001963 / 125000000000 : ℝ)
  | 10 => (-8692627728129 / 250000000000 : ℝ)
  | 11 => (-8764156537353 / 250000000000 : ℝ)
  | 12 => (-8836173145887 / 250000000000 : ℝ)
  | 13 => (-44543401401 / 1250000000 : ℝ)
  | 14 => (-1122710084873 / 31250000000 : ℝ)
  | 15 => (-2263794273299 / 62500000000 : ℝ)
  | 16 => (-36516689144401 / 1000000000000 : ℝ)
  | 17 => (-36814676133249 / 1000000000000 : ℝ)
  | 18 => (-37114680491357 / 1000000000000 : ℝ)
  | 19 => (-74833426841 / 2000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch062Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1240 : ℝ) + (j.val : ℝ)) / 1600)
      (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch062Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch062Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1240 : ℝ) + (j.val : ℝ)) / 1600)
    (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch062Neg100WeightLower j.val) (hpThetaShiftOneBatch062Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch062Neg100WeightLower, hpThetaShiftOneBatch062Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch062Neg100_integral_bounds :
    (-327527461551 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-31704736213 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch062Lower hpThetaJensenCellsBatch062Upper
    hpThetaShiftOneBatch062Neg100WeightLower hpThetaShiftOneBatch062Neg100WeightUpper hpThetaJensenCellsBatch062_bounds hpThetaShiftOneBatch062Neg100_weight_bounds
  have hl : (-327527461551 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch062Lower j * hpThetaShiftOneBatch062Neg100WeightLower j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftOneBatch062Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftOneBatch062Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch062Lower j * hpThetaShiftOneBatch062Neg100WeightUpper j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftOneBatch062Neg100WeightUpper j) / 1600) ≤ (-31704736213 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftOneBatch062Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1240 : ℝ) / 1600 = 62 / 80 by norm_num,
    show ((1240 : ℝ) + 20) / 1600 = (62 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch062Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1997200204873 / 500000000000 : ℝ)
  | 1 => (-4039899168657 / 1000000000000 : ℝ)
  | 2 => (-4085776341597 / 1000000000000 : ℝ)
  | 3 => (-4132034340321 / 1000000000000 : ℝ)
  | 4 => (-835735117681 / 200000000000 : ℝ)
  | 5 => (-4225702521293 / 1000000000000 : ℝ)
  | 6 => (-854623517267 / 200000000000 : ℝ)
  | 7 => (-2160461621417 / 500000000000 : ℝ)
  | 8 => (-1092280490523 / 250000000000 : ℝ)
  | 9 => (-4417716227447 / 1000000000000 : ℝ)
  | 10 => (-2233354267163 / 500000000000 : ℝ)
  | 11 => (-4516101390281 / 1000000000000 : ℝ)
  | 12 => (-4565897315041 / 1000000000000 : ℝ)
  | 13 => (-4616098840549 / 1000000000000 : ℝ)
  | 14 => (-4666708511013 / 1000000000000 : ℝ)
  | 15 => (-2358864441473 / 500000000000 : ℝ)
  | 16 => (-4769162525213 / 1000000000000 : ℝ)
  | 17 => (-4821012019077 / 1000000000000 : ℝ)
  | 18 => (-30457999739 / 6250000000 : ℝ)
  | 19 => (-2462984474447 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch062Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-789855532977 / 200000000000 : ℝ)
  | 1 => (-798880081949 / 200000000000 : ℝ)
  | 2 => (-252493698041 / 62500000000 : ℝ)
  | 3 => (-1021444085399 / 250000000000 : ℝ)
  | 4 => (-25825214627 / 6250000000 : ℝ)
  | 5 => (-1044668897101 / 250000000000 : ℝ)
  | 6 => (-1056425630323 / 250000000000 : ℝ)
  | 7 => (-2136558793167 / 500000000000 : ℝ)
  | 8 => (-4320923242833 / 1000000000000 : ℝ)
  | 9 => (-4369121962091 / 1000000000000 : ℝ)
  | 10 => (-2208858113723 / 500000000000 : ℝ)
  | 11 => (-178668341373 / 40000000000 : ℝ)
  | 12 => (-112902534757 / 25000000000 : ℝ)
  | 13 => (-28536858219 / 6250000000 : ℝ)
  | 14 => (-1154024710137 / 250000000000 : ℝ)
  | 15 => (-1166677127753 / 250000000000 : ℝ)
  | 16 => (-943545776589 / 200000000000 : ℝ)
  | 17 => (-1192290631303 / 250000000000 : ℝ)
  | 18 => (-1205253004769 / 250000000000 : ℝ)
  | 19 => (-4873279958239 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch062Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1240 : ℝ) + (j.val : ℝ)) / 1600)
      (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch062Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch062Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1240 : ℝ) + (j.val : ℝ)) / 1600)
    (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch062Neg65WeightLower j.val) (hpThetaShiftOneBatch062Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch062Neg65WeightLower, hpThetaShiftOneBatch062Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch062Neg65_integral_bounds :
    (-41634378609 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-8037477227 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch062Lower hpThetaJensenCellsBatch062Upper
    hpThetaShiftOneBatch062Neg65WeightLower hpThetaShiftOneBatch062Neg65WeightUpper hpThetaJensenCellsBatch062_bounds hpThetaShiftOneBatch062Neg65_weight_bounds
  have hl : (-41634378609 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch062Lower j * hpThetaShiftOneBatch062Neg65WeightLower j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftOneBatch062Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftOneBatch062Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch062Lower j * hpThetaShiftOneBatch062Neg65WeightUpper j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftOneBatch062Neg65WeightUpper j) / 1600) ≤ (-8037477227 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftOneBatch062Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1240 : ℝ) / 1600 = 62 / 80 by norm_num,
    show ((1240 : ℝ) + 20) / 1600 = (62 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch062Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (40086964031 / 100000000000 : ℝ)
  | 1 => (99902350767 / 250000000000 : ℝ)
  | 2 => (398309188909 / 1000000000000 : ℝ)
  | 3 => (99242154647 / 250000000000 : ℝ)
  | 4 => (79117462119 / 200000000000 : ℝ)
  | 5 => (394164881143 / 1000000000000 : ℝ)
  | 6 => (196350472079 / 500000000000 : ℝ)
  | 7 => (391195111271 / 1000000000000 : ℝ)
  | 8 => (6088234247 / 15625000000 : ℝ)
  | 9 => (194028096389 / 500000000000 : ℝ)
  | 10 => (386422318869 / 1000000000000 : ℝ)
  | 11 => (76948994487 / 200000000000 : ℝ)
  | 12 => (76604750697 / 200000000000 : ℝ)
  | 13 => (190629129839 / 500000000000 : ℝ)
  | 14 => (94862021577 / 250000000000 : ℝ)
  | 15 => (377592826301 / 1000000000000 : ℝ)
  | 16 => (375692070199 / 1000000000000 : ℝ)
  | 17 => (373745406153 / 1000000000000 : ℝ)
  | 18 => (74350483983 / 200000000000 : ℝ)
  | 19 => (14788507793 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch062Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (402090277617 / 1000000000000 : ℝ)
  | 1 => (400869640311 / 1000000000000 : ℝ)
  | 2 => (399609403069 / 1000000000000 : ℝ)
  | 3 => (39830918891 / 100000000000 : ℝ)
  | 4 => (396968618589 / 1000000000000 : ℝ)
  | 5 => (98896827649 / 250000000000 : ℝ)
  | 6 => (49270610143 / 125000000000 : ℝ)
  | 7 => (392700944159 / 1000000000000 : ℝ)
  | 8 => (48899388909 / 125000000000 : ℝ)
  | 9 => (389646991809 / 1000000000000 : ℝ)
  | 10 => (388056192779 / 1000000000000 : ℝ)
  | 11 => (38642231887 / 100000000000 : ℝ)
  | 12 => (96186243109 / 250000000000 : ℝ)
  | 13 => (191511876743 / 500000000000 : ℝ)
  | 14 => (381258259679 / 1000000000000 : ℝ)
  | 15 => (379448086309 / 1000000000000 : ℝ)
  | 16 => (188796413151 / 500000000000 : ℝ)
  | 17 => (1878460351 / 5000000000 : ℝ)
  | 18 => (186872703077 / 500000000000 : ℝ)
  | 19 => (92938104979 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch062Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1240 : ℝ) + (j.val : ℝ)) / 1600)
      (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch062Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch062Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1240 : ℝ) + (j.val : ℝ)) / 1600)
    (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch062Neg40WeightLower j.val) (hpThetaShiftOneBatch062Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch062Neg40WeightLower, hpThetaShiftOneBatch062Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch062Neg40_integral_bounds :
    (3558768591 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (3661357099 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch062Lower hpThetaJensenCellsBatch062Upper
    hpThetaShiftOneBatch062Neg40WeightLower hpThetaShiftOneBatch062Neg40WeightUpper hpThetaJensenCellsBatch062_bounds hpThetaShiftOneBatch062Neg40_weight_bounds
  have hl : (3558768591 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch062Lower j * hpThetaShiftOneBatch062Neg40WeightLower j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftOneBatch062Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftOneBatch062Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch062Lower j * hpThetaShiftOneBatch062Neg40WeightUpper j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftOneBatch062Neg40WeightUpper j) / 1600) ≤ (3661357099 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftOneBatch062Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1240 : ℝ) / 1600 = 62 / 80 by norm_num,
    show ((1240 : ℝ) + 20) / 1600 = (62 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch062Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (10899818551 / 250000000000 : ℝ)
  | 1 => (44754230123 / 1000000000000 : ℝ)
  | 2 => (918304179 / 20000000000 : ℝ)
  | 3 => (23541107473 / 500000000000 : ℝ)
  | 4 => (24127626121 / 500000000000 : ℝ)
  | 5 => (49434324837 / 1000000000000 : ℝ)
  | 6 => (253097183 / 5000000000 : ℝ)
  | 7 => (1619080977 / 31250000000 : ℝ)
  | 8 => (13251948107 / 250000000000 : ℝ)
  | 9 => (54211043559 / 1000000000000 : ℝ)
  | 10 => (3463771749 / 62500000000 : ℝ)
  | 11 => (11327141779 / 200000000000 : ℝ)
  | 12 => (57857129347 / 1000000000000 : ℝ)
  | 13 => (1846394133 / 31250000000 : ℝ)
  | 14 => (60318160397 / 1000000000000 : ℝ)
  | 15 => (12311555281 / 200000000000 : ℝ)
  | 16 => (2512138511 / 40000000000 : ℝ)
  | 17 => (64055221859 / 1000000000000 : ℝ)
  | 18 => (65313055863 / 1000000000000 : ℝ)
  | 19 => (16644241713 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch062Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (11188557531 / 250000000000 : ℝ)
  | 1 => (45915208951 / 1000000000000 : ℝ)
  | 2 => (47082214947 / 1000000000000 : ℝ)
  | 3 => (48255252243 / 1000000000000 : ℝ)
  | 4 => (24717162419 / 500000000000 : ℝ)
  | 5 => (50619436601 / 1000000000000 : ℝ)
  | 6 => (10362118253 / 200000000000 : ℝ)
  | 7 => (53007792429 / 1000000000000 : ℝ)
  | 8 => (1355276089 / 25000000000 : ℝ)
  | 9 => (11084069597 / 200000000000 : ℝ)
  | 10 => (1769865903 / 31250000000 : ℝ)
  | 11 => (14464282337 / 250000000000 : ℝ)
  | 12 => (59084612257 / 1000000000000 : ℝ)
  | 13 => (30159080199 / 500000000000 : ℝ)
  | 14 => (30778888203 / 500000000000 : ℝ)
  | 15 => (7850432847 / 125000000000 : ℝ)
  | 16 => (3202761093 / 50000000000 : ℝ)
  | 17 => (8164131983 / 125000000000 : ℝ)
  | 18 => (66576966853 / 1000000000000 : ℝ)
  | 19 => (33923478373 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch062Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1240 : ℝ) + (j.val : ℝ)) / 1600)
      (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch062Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch062Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1240 : ℝ) + (j.val : ℝ)) / 1600)
    (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch062Neg20WeightLower j.val) (hpThetaShiftOneBatch062Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch062Neg20WeightLower, hpThetaShiftOneBatch062Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch062Neg20_integral_bounds :
    (498674327 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (10446731 / 20000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch062Lower hpThetaJensenCellsBatch062Upper
    hpThetaShiftOneBatch062Neg20WeightLower hpThetaShiftOneBatch062Neg20WeightUpper hpThetaJensenCellsBatch062_bounds hpThetaShiftOneBatch062Neg20_weight_bounds
  have hl : (498674327 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch062Lower j * hpThetaShiftOneBatch062Neg20WeightLower j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftOneBatch062Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftOneBatch062Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch062Lower j * hpThetaShiftOneBatch062Neg20WeightUpper j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftOneBatch062Neg20WeightUpper j) / 1600) ≤ (10446731 / 20000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftOneBatch062Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1240 : ℝ) / 1600 = 62 / 80 by norm_num,
    show ((1240 : ℝ) + 20) / 1600 = (62 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch062Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch062Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch062Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch062Neg20_integral_bounds
end HodgeProofHP
