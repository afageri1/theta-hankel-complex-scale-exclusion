/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch075

/-! Exact signed weight and batch integral certificates, batch 75 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch075Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-51399686553653 / 250000000000 : ℝ)
  | 1 => (-206875126180909 / 1000000000000 : ℝ)
  | 2 => (-104079122538067 / 500000000000 : ℝ)
  | 3 => (-209448132629501 / 1000000000000 : ℝ)
  | 4 => (-42148963735403 / 200000000000 : ℝ)
  | 5 => (-212048333161769 / 1000000000000 : ℝ)
  | 6 => (-26669838266781 / 125000000000 : ℝ)
  | 7 => (-21467596775263 / 100000000000 : ℝ)
  | 8 => (-216000148283089 / 1000000000000 : ℝ)
  | 9 => (-108665639050047 / 500000000000 : ℝ)
  | 10 => (-109334693843359 / 500000000000 : ℝ)
  | 11 => (-110007253817469 / 500000000000 : ℝ)
  | 12 => (-221366668645943 / 1000000000000 : ℝ)
  | 13 => (-222725901530437 / 1000000000000 : ℝ)
  | 14 => (-14005764825559 / 62500000000 : ℝ)
  | 15 => (-225465706712119 / 1000000000000 : ℝ)
  | 16 => (-226846341181051 / 1000000000000 : ℝ)
  | 17 => (-228234171867573 / 1000000000000 : ℝ)
  | 18 => (-22962923013457 / 100000000000 : ℝ)
  | 19 => (-7219735858009 / 31250000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch075Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-102164537777259 / 500000000000 : ℝ)
  | 1 => (-205598746214611 / 1000000000000 : ℝ)
  | 2 => (-51718781545227 / 250000000000 : ℝ)
  | 3 => (-208158245076133 / 1000000000000 : ℝ)
  | 4 => (-418896265259 / 2000000000 : ℝ)
  | 5 => (-105372409338507 / 500000000000 : ℝ)
  | 6 => (-26506041645221 / 125000000000 : ℝ)
  | 7 => (-213358706134247 / 1000000000000 : ℝ)
  | 8 => (-214675967752629 / 1000000000000 : ℝ)
  | 9 => (-13500009267693 / 62500000000 : ℝ)
  | 10 => (-217331278100093 / 1000000000000 : ℝ)
  | 11 => (-218669387686717 / 1000000000000 : ℝ)
  | 12 => (-220014507634937 / 1000000000000 : ℝ)
  | 13 => (-110683334322971 / 500000000000 : ℝ)
  | 14 => (-55681475382609 / 250000000000 : ℝ)
  | 15 => (-224092237208943 / 1000000000000 : ℝ)
  | 16 => (-112732853356059 / 500000000000 : ℝ)
  | 17 => (-4536926823621 / 20000000000 : ℝ)
  | 18 => (-57058542966893 / 250000000000 : ℝ)
  | 19 => (-229629230134569 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch075Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1500 : ℝ) + (j.val : ℝ)) / 1600)
      (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch075Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch075Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1500 : ℝ) + (j.val : ℝ)) / 1600)
    (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch075Neg100WeightLower j.val) (hpThetaShiftOneBatch075Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch075Neg100WeightLower, hpThetaShiftOneBatch075Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch075Neg100_integral_bounds :
    (-3490727331 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-13447348741 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch075Lower hpThetaJensenCellsBatch075Upper
    hpThetaShiftOneBatch075Neg100WeightLower hpThetaShiftOneBatch075Neg100WeightUpper hpThetaJensenCellsBatch075_bounds hpThetaShiftOneBatch075Neg100_weight_bounds
  have hl : (-3490727331 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch075Lower j * hpThetaShiftOneBatch075Neg100WeightLower j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftOneBatch075Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftOneBatch075Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch075Lower j * hpThetaShiftOneBatch075Neg100WeightUpper j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftOneBatch075Neg100WeightUpper j) / 1600) ≤ (-13447348741 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftOneBatch075Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1500 : ℝ) / 1600 = 75 / 80 by norm_num,
    show ((1500 : ℝ) + 20) / 1600 = (75 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch075Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-19106003542391 / 500000000000 : ℝ)
  | 1 => (-19240298168273 / 500000000000 : ℝ)
  | 2 => (-9687684575599 / 250000000000 : ℝ)
  | 3 => (-39022440301463 / 1000000000000 : ℝ)
  | 4 => (-39295709680447 / 1000000000000 : ℝ)
  | 5 => (-7914110762739 / 200000000000 : ℝ)
  | 6 => (-39846980103289 / 1000000000000 : ℝ)
  | 7 => (-40124995979117 / 1000000000000 : ℝ)
  | 8 => (-505057611237 / 12500000000 : ℝ)
  | 9 => (-4068582634857 / 100000000000 : ℝ)
  | 10 => (-40968655841751 / 1000000000000 : ℝ)
  | 11 => (-10313276230111 / 250000000000 : ℝ)
  | 12 => (-41539181154801 / 1000000000000 : ℝ)
  | 13 => (-41826892143273 / 1000000000000 : ℝ)
  | 14 => (-4211624551269 / 100000000000 : ℝ)
  | 15 => (-21203624459169 / 500000000000 : ℝ)
  | 16 => (-42699910044051 / 1000000000000 : ℝ)
  | 17 => (-21497118301141 / 500000000000 : ℝ)
  | 18 => (-43290236334193 / 1000000000000 : ℝ)
  | 19 => (-21793958504867 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch075Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-18972481627731 / 500000000000 : ℝ)
  | 1 => (-38212007084781 / 1000000000000 : ℝ)
  | 2 => (-7696119267309 / 200000000000 : ℝ)
  | 3 => (-7750147660479 / 200000000000 : ℝ)
  | 4 => (-19511220150731 / 500000000000 : ℝ)
  | 5 => (-19647854840223 / 500000000000 : ℝ)
  | 6 => (-19785276906847 / 500000000000 : ℝ)
  | 7 => (-4980872512911 / 125000000000 : ℝ)
  | 8 => (-10031248994779 / 250000000000 : ℝ)
  | 9 => (-40404608898959 / 1000000000000 : ℝ)
  | 10 => (-40685826348569 / 1000000000000 : ℝ)
  | 11 => (-163874623367 / 4000000000 : ℝ)
  | 12 => (-41253104920443 / 1000000000000 : ℝ)
  | 13 => (-103847952887 / 2500000000 : ℝ)
  | 14 => (-5228361517909 / 125000000000 : ℝ)
  | 15 => (-42116245512689 / 1000000000000 : ℝ)
  | 16 => (-42407248918337 / 1000000000000 : ℝ)
  | 17 => (-853998200881 / 20000000000 : ℝ)
  | 18 => (-42994236602281 / 1000000000000 : ℝ)
  | 19 => (-2705639770887 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch075Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1500 : ℝ) + (j.val : ℝ)) / 1600)
      (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch075Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch075Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1500 : ℝ) + (j.val : ℝ)) / 1600)
    (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch075Neg65WeightLower j.val) (hpThetaShiftOneBatch075Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch075Neg65WeightLower, hpThetaShiftOneBatch075Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch075Neg65_integral_bounds :
    (-2613729197 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-1257612471 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch075Lower hpThetaJensenCellsBatch075Upper
    hpThetaShiftOneBatch075Neg65WeightLower hpThetaShiftOneBatch075Neg65WeightUpper hpThetaJensenCellsBatch075_bounds hpThetaShiftOneBatch075Neg65_weight_bounds
  have hl : (-2613729197 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch075Lower j * hpThetaShiftOneBatch075Neg65WeightLower j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftOneBatch075Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftOneBatch075Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch075Lower j * hpThetaShiftOneBatch075Neg65WeightUpper j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftOneBatch075Neg65WeightUpper j) / 1600) ≤ (-1257612471 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftOneBatch075Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1500 : ℝ) / 1600 = 75 / 80 by norm_num,
    show ((1500 : ℝ) + 20) / 1600 = (75 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch075Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2892857668599 / 1000000000000 : ℝ)
  | 1 => (-45716377929 / 15625000000 : ℝ)
  | 2 => (-2959085911361 / 1000000000000 : ℝ)
  | 3 => (-598514441389 / 200000000000 : ℝ)
  | 4 => (-3026308446539 / 1000000000000 : ℝ)
  | 5 => (-765074002049 / 250000000000 : ℝ)
  | 6 => (-618907255141 / 200000000000 : ℝ)
  | 7 => (-312903063861 / 100000000000 : ℝ)
  | 8 => (-790945123057 / 250000000000 : ℝ)
  | 9 => (-3198787237667 / 1000000000000 : ℝ)
  | 10 => (-808513070461 / 250000000000 : ℝ)
  | 11 => (-3269577037501 / 1000000000000 : ℝ)
  | 12 => (-1652681461613 / 500000000000 : ℝ)
  | 13 => (-3341411363469 / 1000000000000 : ℝ)
  | 14 => (-3377723788559 / 1000000000000 : ℝ)
  | 15 => (-1707150817363 / 500000000000 : ℝ)
  | 16 => (-862786586029 / 250000000000 : ℝ)
  | 17 => (-436032420601 / 125000000000 : ℝ)
  | 18 => (-705128430167 / 200000000000 : ℝ)
  | 19 => (-3563296162203 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch075Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-715028248461 / 250000000000 : ℝ)
  | 1 => (-1446428834299 / 500000000000 : ℝ)
  | 2 => (-585169637491 / 200000000000 : ℝ)
  | 3 => (-9247143473 / 3125000000 : ℝ)
  | 4 => (-93517881467 / 31250000000 : ℝ)
  | 5 => (-1513154223269 / 500000000000 : ℝ)
  | 6 => (-612059201639 / 200000000000 : ℝ)
  | 7 => (-386817034463 / 125000000000 : ℝ)
  | 8 => (-3129030638609 / 1000000000000 : ℝ)
  | 9 => (-3163780492227 / 1000000000000 : ℝ)
  | 10 => (-1599393618833 / 500000000000 : ℝ)
  | 11 => (-3234052281843 / 1000000000000 : ℝ)
  | 12 => (-261566163 / 80000000 : ℝ)
  | 13 => (-132214516929 / 40000000000 : ℝ)
  | 14 => (-835352840867 / 250000000000 : ℝ)
  | 15 => (-1688861894279 / 500000000000 : ℝ)
  | 16 => (-136572065389 / 40000000000 : ℝ)
  | 17 => (-690229268823 / 200000000000 : ℝ)
  | 18 => (-3488259364807 / 1000000000000 : ℝ)
  | 19 => (-1762821075417 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch075Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1500 : ℝ) + (j.val : ℝ)) / 1600)
      (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch075Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch075Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1500 : ℝ) + (j.val : ℝ)) / 1600)
    (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch075Neg40WeightLower j.val) (hpThetaShiftOneBatch075Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch075Neg40WeightLower, hpThetaShiftOneBatch075Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch075Neg40_integral_bounds :
    (-205416899 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-196871423 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch075Lower hpThetaJensenCellsBatch075Upper
    hpThetaShiftOneBatch075Neg40WeightLower hpThetaShiftOneBatch075Neg40WeightUpper hpThetaJensenCellsBatch075_bounds hpThetaShiftOneBatch075Neg40_weight_bounds
  have hl : (-205416899 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch075Lower j * hpThetaShiftOneBatch075Neg40WeightLower j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftOneBatch075Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftOneBatch075Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch075Lower j * hpThetaShiftOneBatch075Neg40WeightUpper j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftOneBatch075Neg40WeightUpper j) / 1600) ≤ (-196871423 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftOneBatch075Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1500 : ℝ) / 1600 = 75 / 80 by norm_num,
    show ((1500 : ℝ) + 20) / 1600 = (75 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch075Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (524892408533 / 1000000000000 : ℝ)
  | 1 => (131795258661 / 250000000000 : ℝ)
  | 2 => (264734592513 / 500000000000 : ℝ)
  | 3 => (531756790001 / 1000000000000 : ℝ)
  | 4 => (534043779411 / 1000000000000 : ℝ)
  | 5 => (107266016523 / 200000000000 : ℝ)
  | 6 => (269307814241 / 500000000000 : ℝ)
  | 7 => (540900345397 / 1000000000000 : ℝ)
  | 8 => (543184161253 / 1000000000000 : ℝ)
  | 9 => (545467003453 / 1000000000000 : ℝ)
  | 10 => (68468599863 / 125000000000 : ℝ)
  | 11 => (550029474019 / 1000000000000 : ℝ)
  | 12 => (110461790943 / 200000000000 : ℝ)
  | 13 => (554587166407 / 1000000000000 : ℝ)
  | 14 => (55686403401 / 100000000000 : ℝ)
  | 15 => (34946217621 / 62500000000 : ℝ)
  | 16 => (561413434091 / 1000000000000 : ℝ)
  | 17 => (4509486511 / 8000000000 : ℝ)
  | 18 => (565956544179 / 1000000000000 : ℝ)
  | 19 => (568225547381 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch075Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (105436206929 / 200000000000 : ℝ)
  | 1 => (529469185027 / 1000000000000 : ℝ)
  | 2 => (265878395001 / 500000000000 : ℝ)
  | 3 => (133510944853 / 250000000000 : ℝ)
  | 4 => (67041260327 / 125000000000 : ℝ)
  | 5 => (538615628483 / 1000000000000 : ℝ)
  | 6 => (270450172699 / 500000000000 : ℝ)
  | 7 => (271592080627 / 500000000000 : ℝ)
  | 8 => (272733501727 / 500000000000 : ℝ)
  | 9 => (109549759781 / 200000000000 : ℝ)
  | 10 => (27501473701 / 50000000000 : ℝ)
  | 11 => (138077238679 / 250000000000 : ℝ)
  | 12 => (69323395801 / 125000000000 : ℝ)
  | 13 => (556864034011 / 1000000000000 : ℝ)
  | 14 => (559139481937 / 1000000000000 : ℝ)
  | 15 => (140353358523 / 250000000000 : ℝ)
  | 16 => (140921453469 / 250000000000 : ℝ)
  | 17 => (28297827209 / 50000000000 : ℝ)
  | 18 => (284112773691 / 500000000000 : ℝ)
  | 19 => (11409854907 / 20000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch075Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1500 : ℝ) + (j.val : ℝ)) / 1600)
      (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch075Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch075Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1500 : ℝ) + (j.val : ℝ)) / 1600)
    (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch075Neg20WeightLower j.val) (hpThetaShiftOneBatch075Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch075Neg20WeightLower, hpThetaShiftOneBatch075Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch075Neg20_integral_bounds :
    (2122321 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (17594837 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch075Lower hpThetaJensenCellsBatch075Upper
    hpThetaShiftOneBatch075Neg20WeightLower hpThetaShiftOneBatch075Neg20WeightUpper hpThetaJensenCellsBatch075_bounds hpThetaShiftOneBatch075Neg20_weight_bounds
  have hl : (2122321 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch075Lower j * hpThetaShiftOneBatch075Neg20WeightLower j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftOneBatch075Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftOneBatch075Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch075Lower j * hpThetaShiftOneBatch075Neg20WeightUpper j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftOneBatch075Neg20WeightUpper j) / 1600) ≤ (17594837 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftOneBatch075Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1500 : ℝ) / 1600 = 75 / 80 by norm_num,
    show ((1500 : ℝ) + 20) / 1600 = (75 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch075Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch075Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch075Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch075Neg20_integral_bounds
end HodgeProofHP
