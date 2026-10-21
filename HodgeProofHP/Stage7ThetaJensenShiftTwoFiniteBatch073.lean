/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch073

/-! Exact signed weight and batch integral certificates, batch 73 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch073Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6087023037337 / 1000000000000 : ℝ)
  | 1 => (-6136949855551 / 1000000000000 : ℝ)
  | 2 => (-6187234395577 / 1000000000000 : ℝ)
  | 3 => (-6237878877217 / 1000000000000 : ℝ)
  | 4 => (-6288885532051 / 1000000000000 : ℝ)
  | 5 => (-634025660349 / 100000000000 : ℝ)
  | 6 => (-3195997173413 / 500000000000 : ℝ)
  | 7 => (-6444101029289 / 1000000000000 : ℝ)
  | 8 => (-3248289465049 / 500000000000 : ℝ)
  | 9 => (-6549430340513 / 1000000000000 : ℝ)
  | 10 => (-660265756389 / 100000000000 : ℝ)
  | 11 => (-6656262915733 / 1000000000000 : ℝ)
  | 12 => (-838781090469 / 125000000000 : ℝ)
  | 13 => (-676461732791 / 100000000000 : ℝ)
  | 14 => (-1363874216097 / 200000000000 : ℝ)
  | 15 => (-3437256173059 / 500000000000 : ℝ)
  | 16 => (-693004350187 / 100000000000 : ℝ)
  | 17 => (-21831146679 / 3125000000 : ℝ)
  | 18 => (-3521142527207 / 500000000000 : ℝ)
  | 19 => (-1774750066981 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch073Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-754681466607 / 125000000000 : ℝ)
  | 1 => (-760877879667 / 125000000000 : ℝ)
  | 2 => (-122738997111 / 20000000000 : ℝ)
  | 3 => (-773404299447 / 125000000000 : ℝ)
  | 4 => (-194933714913 / 31250000000 : ℝ)
  | 5 => (-125777710641 / 20000000000 : ℝ)
  | 6 => (-6340256603489 / 1000000000000 : ℝ)
  | 7 => (-255679773873 / 40000000000 : ℝ)
  | 8 => (-805512628661 / 125000000000 : ℝ)
  | 9 => (-6496578930097 / 1000000000000 : ℝ)
  | 10 => (-204669698141 / 31250000000 : ℝ)
  | 11 => (-6602657563889 / 1000000000000 : ℝ)
  | 12 => (-1664065728933 / 250000000000 : ℝ)
  | 13 => (-6710248723751 / 1000000000000 : ℝ)
  | 14 => (-6764617327909 / 1000000000000 : ℝ)
  | 15 => (-1704842770121 / 250000000000 : ℝ)
  | 16 => (-6874512346117 / 1000000000000 : ℝ)
  | 17 => (-6930043501869 / 1000000000000 : ℝ)
  | 18 => (-6985966937279 / 1000000000000 : ℝ)
  | 19 => (-7042285054413 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch073Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1460 : ℝ) + (j.val : ℝ)) / 1600)
      (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch073Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch073Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1460 : ℝ) + (j.val : ℝ)) / 1600)
    (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch073Neg100WeightLower j.val) (hpThetaShiftTwoBatch073Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch073Neg100WeightLower, hpThetaShiftTwoBatch073Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch073Neg100_integral_bounds :
    (-257154873 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-197991141 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch073Lower hpThetaJensenCellsBatch073Upper
    hpThetaShiftTwoBatch073Neg100WeightLower hpThetaShiftTwoBatch073Neg100WeightUpper hpThetaJensenCellsBatch073_bounds hpThetaShiftTwoBatch073Neg100_weight_bounds
  have hl : (-257154873 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch073Lower j * hpThetaShiftTwoBatch073Neg100WeightLower j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftTwoBatch073Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftTwoBatch073Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch073Lower j * hpThetaShiftTwoBatch073Neg100WeightUpper j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftTwoBatch073Neg100WeightUpper j) / 1600) ≤ (-197991141 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftTwoBatch073Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1460 : ℝ) / 1600 = 73 / 80 by norm_num,
    show ((1460 : ℝ) + 20) / 1600 = (73 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch073Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-448660638351 / 500000000000 : ℝ)
  | 1 => (-906149768581 / 1000000000000 : ℝ)
  | 2 => (-915050308023 / 1000000000000 : ℝ)
  | 3 => (-184804677419 / 200000000000 : ℝ)
  | 4 => (-933069500669 / 1000000000000 : ℝ)
  | 5 => (-471094573217 / 500000000000 : ℝ)
  | 6 => (-95138282491 / 100000000000 : ℝ)
  | 7 => (-480325519731 / 500000000000 : ℝ)
  | 8 => (-96999429631 / 100000000000 : ℝ)
  | 9 => (-489706552273 / 500000000000 : ℝ)
  | 10 => (-494453988073 / 500000000000 : ℝ)
  | 11 => (-499239712991 / 500000000000 : ℝ)
  | 12 => (-504063985919 / 500000000000 : ℝ)
  | 13 => (-127231766803 / 125000000000 : ℝ)
  | 14 => (-205531687477 / 200000000000 : ℝ)
  | 15 => (-25938535183 / 25000000000 : ℝ)
  | 16 => (-523751786897 / 500000000000 : ℝ)
  | 17 => (-1057545469349 / 1000000000000 : ℝ)
  | 18 => (-1067667629523 / 1000000000000 : ℝ)
  | 19 => (-1077870592859 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch073Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-444282171553 / 500000000000 : ℝ)
  | 1 => (-897321276701 / 1000000000000 : ℝ)
  | 2 => (-45307488429 / 50000000000 : ℝ)
  | 3 => (-457525154011 / 500000000000 : ℝ)
  | 4 => (-462011693547 / 500000000000 : ℝ)
  | 5 => (-233267375167 / 250000000000 : ℝ)
  | 6 => (-942189146433 / 1000000000000 : ℝ)
  | 7 => (-951382824909 / 1000000000000 : ℝ)
  | 8 => (-960651039461 / 1000000000000 : ℝ)
  | 9 => (-969994296309 / 1000000000000 : ℝ)
  | 10 => (-195882620909 / 200000000000 : ℝ)
  | 11 => (-197781595229 / 200000000000 : ℝ)
  | 12 => (-998479425981 / 1000000000000 : ℝ)
  | 13 => (-1008127971837 / 1000000000000 : ℝ)
  | 14 => (-1017854134423 / 1000000000000 : ℝ)
  | 15 => (-128457304673 / 125000000000 : ℝ)
  | 16 => (-1037541407319 / 1000000000000 : ℝ)
  | 17 => (-1047503573793 / 1000000000000 : ℝ)
  | 18 => (-264386367337 / 250000000000 : ℝ)
  | 19 => (-533833814761 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch073Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1460 : ℝ) + (j.val : ℝ)) / 1600)
      (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch073Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch073Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1460 : ℝ) + (j.val : ℝ)) / 1600)
    (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch073Neg65WeightLower j.val) (hpThetaShiftTwoBatch073Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch073Neg65WeightLower, hpThetaShiftTwoBatch073Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch073Neg65_integral_bounds :
    (-38455071 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-73903689 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch073Lower hpThetaJensenCellsBatch073Upper
    hpThetaShiftTwoBatch073Neg65WeightLower hpThetaShiftTwoBatch073Neg65WeightUpper hpThetaJensenCellsBatch073_bounds hpThetaShiftTwoBatch073Neg65_weight_bounds
  have hl : (-38455071 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch073Lower j * hpThetaShiftTwoBatch073Neg65WeightLower j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftTwoBatch073Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftTwoBatch073Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch073Lower j * hpThetaShiftTwoBatch073Neg65WeightUpper j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftTwoBatch073Neg65WeightUpper j) / 1600) ≤ (-73903689 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftTwoBatch073Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1460 : ℝ) / 1600 = 73 / 80 by norm_num,
    show ((1460 : ℝ) + 20) / 1600 = (73 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch073Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-60836311229 / 1000000000000 : ℝ)
  | 1 => (-6210485649 / 100000000000 : ℝ)
  | 2 => (-6338770937 / 100000000000 : ℝ)
  | 3 => (-16171246929 / 250000000000 : ℝ)
  | 4 => (-16499202533 / 250000000000 : ℝ)
  | 5 => (-33661647991 / 500000000000 : ℝ)
  | 6 => (-17166141349 / 250000000000 : ℝ)
  | 7 => (-70020739277 / 1000000000000 : ℝ)
  | 8 => (-2230998103 / 31250000000 : ℝ)
  | 9 => (-14555657581 / 200000000000 : ℝ)
  | 10 => (-4636244271 / 62500000000 : ℝ)
  | 11 => (-37798462303 / 500000000000 : ℝ)
  | 12 => (-962868269 / 12500000000 : ℝ)
  | 13 => (-1961941117 / 25000000000 : ℝ)
  | 14 => (-499635003 / 6250000000 : ℝ)
  | 15 => (-81421456119 / 1000000000000 : ℝ)
  | 16 => (-207293349 / 2500000000 : ℝ)
  | 17 => (-42214689867 / 500000000000 : ℝ)
  | 18 => (-85957706147 / 1000000000000 : ℝ)
  | 19 => (-87502449281 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch073Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-11916391299 / 200000000000 : ℝ)
  | 1 => (-15209077807 / 250000000000 : ℝ)
  | 2 => (-62104856489 / 1000000000000 : ℝ)
  | 3 => (-63387709369 / 1000000000000 : ℝ)
  | 4 => (-12936997543 / 200000000000 : ℝ)
  | 5 => (-65996810131 / 1000000000000 : ℝ)
  | 6 => (-67323295981 / 1000000000000 : ℝ)
  | 7 => (-13732913079 / 200000000000 : ℝ)
  | 8 => (-17505184819 / 250000000000 : ℝ)
  | 9 => (-14278387859 / 200000000000 : ℝ)
  | 10 => (-2274321497 / 31250000000 : ℝ)
  | 11 => (-14835981667 / 200000000000 : ℝ)
  | 12 => (-15119384921 / 200000000000 : ℝ)
  | 13 => (-77029461519 / 1000000000000 : ℝ)
  | 14 => (-78477644679 / 1000000000000 : ℝ)
  | 15 => (-79941600479 / 1000000000000 : ℝ)
  | 16 => (-40710728059 / 500000000000 : ℝ)
  | 17 => (-82917339599 / 1000000000000 : ℝ)
  | 18 => (-84429379733 / 1000000000000 : ℝ)
  | 19 => (-42978853073 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch073Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1460 : ℝ) + (j.val : ℝ)) / 1600)
      (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch073Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch073Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1460 : ℝ) + (j.val : ℝ)) / 1600)
    (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch073Neg45WeightLower j.val) (hpThetaShiftTwoBatch073Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch073Neg45WeightLower, hpThetaShiftTwoBatch073Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch073Neg45_integral_bounds :
    (-2857781 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-5439797 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch073Lower hpThetaJensenCellsBatch073Upper
    hpThetaShiftTwoBatch073Neg45WeightLower hpThetaShiftTwoBatch073Neg45WeightUpper hpThetaJensenCellsBatch073_bounds hpThetaShiftTwoBatch073Neg45_weight_bounds
  have hl : (-2857781 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch073Lower j * hpThetaShiftTwoBatch073Neg45WeightLower j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftTwoBatch073Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftTwoBatch073Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch073Lower j * hpThetaShiftTwoBatch073Neg45WeightUpper j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftTwoBatch073Neg45WeightUpper j) / 1600) ≤ (-5439797 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftTwoBatch073Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1460 : ℝ) / 1600 = 73 / 80 by norm_num,
    show ((1460 : ℝ) + 20) / 1600 = (73 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch073Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (5328281713 / 200000000000 : ℝ)
  | 1 => (1677522629 / 62500000000 : ℝ)
  | 2 => (2703992169 / 100000000000 : ℝ)
  | 3 => (13620041981 / 500000000000 : ℝ)
  | 4 => (1372042267 / 50000000000 : ℝ)
  | 5 => (13821101111 / 500000000000 : ℝ)
  | 6 => (13922075473 / 500000000000 : ℝ)
  | 7 => (14023343893 / 500000000000 : ℝ)
  | 8 => (28249808957 / 1000000000000 : ℝ)
  | 9 => (2845351061 / 100000000000 : ℝ)
  | 10 => (28657788833 / 1000000000000 : ℝ)
  | 11 => (28862639651 / 1000000000000 : ℝ)
  | 12 => (14534029513 / 500000000000 : ℝ)
  | 13 => (14637021427 / 500000000000 : ℝ)
  | 14 => (29480586967 / 1000000000000 : ℝ)
  | 15 => (14843843567 / 500000000000 : ℝ)
  | 16 => (14947669527 / 500000000000 : ℝ)
  | 17 => (30103538363 / 1000000000000 : ℝ)
  | 18 => (3031228063 / 100000000000 : ℝ)
  | 19 => (30521561357 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch073Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5368072413 / 200000000000 : ℝ)
  | 1 => (27039921691 / 1000000000000 : ℝ)
  | 2 => (27240083963 / 1000000000000 : ℝ)
  | 3 => (27440845341 / 1000000000000 : ℝ)
  | 4 => (27642202223 / 1000000000000 : ℝ)
  | 5 => (27844150947 / 1000000000000 : ℝ)
  | 6 => (28046687787 / 1000000000000 : ℝ)
  | 7 => (14124904479 / 500000000000 : ℝ)
  | 8 => (28453510611 / 1000000000000 : ℝ)
  | 9 => (14328894417 / 500000000000 : ℝ)
  | 10 => (7215659913 / 250000000000 : ℝ)
  | 11 => (29068059027 / 1000000000000 : ℝ)
  | 12 => (5854808571 / 200000000000 : ℝ)
  | 13 => (3685073371 / 125000000000 : ℝ)
  | 14 => (5937537427 / 200000000000 : ℝ)
  | 15 => (5979067811 / 200000000000 : ℝ)
  | 16 => (7525884591 / 250000000000 : ℝ)
  | 17 => (30312280631 / 1000000000000 : ℝ)
  | 18 => (15260780679 / 500000000000 : ℝ)
  | 19 => (30731375977 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch073Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1460 : ℝ) + (j.val : ℝ)) / 1600)
      (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch073Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch073Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1460 : ℝ) + (j.val : ℝ)) / 1600)
    (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch073Neg25WeightLower j.val) (hpThetaShiftTwoBatch073Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch073Neg25WeightLower, hpThetaShiftTwoBatch073Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch073Neg25_integral_bounds :
    (541751 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (2249507 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch073Lower hpThetaJensenCellsBatch073Upper
    hpThetaShiftTwoBatch073Neg25WeightLower hpThetaShiftTwoBatch073Neg25WeightUpper hpThetaJensenCellsBatch073_bounds hpThetaShiftTwoBatch073Neg25_weight_bounds
  have hl : (541751 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch073Lower j * hpThetaShiftTwoBatch073Neg25WeightLower j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftTwoBatch073Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftTwoBatch073Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch073Lower j * hpThetaShiftTwoBatch073Neg25WeightUpper j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftTwoBatch073Neg25WeightUpper j) / 1600) ≤ (2249507 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftTwoBatch073Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1460 : ℝ) / 1600 = 73 / 80 by norm_num,
    show ((1460 : ℝ) + 20) / 1600 = (73 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch073Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch073Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch073Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch073Neg25_integral_bounds
end HodgeProofHP
