/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch021

/-! Exact signed weight and batch integral certificates, batch 21 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch021Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1133267 / 15625000000 : ℝ)
  | 1 => (-37008117 / 500000000000 : ℝ)
  | 2 => (-37756853 / 500000000000 : ℝ)
  | 3 => (-77021363 / 1000000000000 : ℝ)
  | 4 => (-78539061 / 1000000000000 : ℝ)
  | 5 => (-80066651 / 1000000000000 : ℝ)
  | 6 => (-81603977 / 1000000000000 : ℝ)
  | 7 => (-83150881 / 1000000000000 : ℝ)
  | 8 => (-42353601 / 500000000000 : ℝ)
  | 9 => (-8627277 / 100000000000 : ℝ)
  | 10 => (-43923707 / 500000000000 : ℝ)
  | 11 => (-89430957 / 1000000000000 : ℝ)
  | 12 => (-91023217 / 1000000000000 : ℝ)
  | 13 => (-92624007 / 1000000000000 : ℝ)
  | 14 => (-94233137 / 1000000000000 : ℝ)
  | 15 => (-9585041 / 100000000000 : ℝ)
  | 16 => (-155961 / 1600000000 : ℝ)
  | 17 => (-3097143 / 31250000000 : ℝ)
  | 18 => (-100749053 / 1000000000000 : ℝ)
  | 19 => (-102396839 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch021Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-17763101 / 250000000000 : ℝ)
  | 1 => (-72529087 / 1000000000000 : ℝ)
  | 2 => (-74016233 / 1000000000000 : ℝ)
  | 3 => (-15102741 / 200000000000 : ℝ)
  | 4 => (-38510681 / 500000000000 : ℝ)
  | 5 => (-3926953 / 50000000000 : ℝ)
  | 6 => (-1601333 / 20000000000 : ℝ)
  | 7 => (-10200497 / 125000000000 : ℝ)
  | 8 => (-519693 / 6250000000 : ℝ)
  | 9 => (-84707201 / 1000000000000 : ℝ)
  | 10 => (-86272769 / 1000000000000 : ℝ)
  | 11 => (-87847413 / 1000000000000 : ℝ)
  | 12 => (-22357739 / 250000000000 : ℝ)
  | 13 => (-5688951 / 62500000000 : ℝ)
  | 14 => (-46312003 / 500000000000 : ℝ)
  | 15 => (-5889571 / 62500000000 : ℝ)
  | 16 => (-95850409 / 1000000000000 : ℝ)
  | 17 => (-12184453 / 125000000000 : ℝ)
  | 18 => (-3964343 / 40000000000 : ℝ)
  | 19 => (-25187263 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch021Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((420 : ℝ) + (j.val : ℝ)) / 1600)
      (((420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch021Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch021Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((420 : ℝ) + (j.val : ℝ)) / 1600)
    (((420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch021Neg100WeightLower j.val) (hpThetaShiftTwoBatch021Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch021Neg100WeightLower, hpThetaShiftTwoBatch021Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch021Neg100_integral_bounds :
    (-966192623 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-234218459 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch021Lower hpThetaJensenCellsBatch021Upper
    hpThetaShiftTwoBatch021Neg100WeightLower hpThetaShiftTwoBatch021Neg100WeightUpper hpThetaJensenCellsBatch021_bounds hpThetaShiftTwoBatch021Neg100_weight_bounds
  have hl : (-966192623 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch021Lower j * hpThetaShiftTwoBatch021Neg100WeightLower j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftTwoBatch021Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftTwoBatch021Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch021Lower j * hpThetaShiftTwoBatch021Neg100WeightUpper j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftTwoBatch021Neg100WeightUpper j) / 1600) ≤ (-234218459 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftTwoBatch021Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (420 : ℝ) / 1600 = 21 / 80 by norm_num,
    show ((420 : ℝ) + 20) / 1600 = (21 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch021Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (19067461 / 1000000000000 : ℝ)
  | 1 => (9059709 / 500000000000 : ℝ)
  | 2 => (17154477 / 1000000000000 : ℝ)
  | 3 => (16172543 / 1000000000000 : ℝ)
  | 4 => (189669 / 12500000000 : ℝ)
  | 5 => (2831463 / 200000000000 : ℝ)
  | 6 => (3280959 / 250000000000 : ℝ)
  | 7 => (12072991 / 1000000000000 : ℝ)
  | 8 => (1100469 / 100000000000 : ℝ)
  | 9 => (2479711 / 250000000000 : ℝ)
  | 10 => (4407683 / 500000000000 : ℝ)
  | 11 => (769417 / 100000000000 : ℝ)
  | 12 => (6555171 / 1000000000000 : ℝ)
  | 13 => (1079657 / 200000000000 : ℝ)
  | 14 => (4223431 / 1000000000000 : ℝ)
  | 15 => (3030527 / 1000000000000 : ℝ)
  | 16 => (363899 / 200000000000 : ℝ)
  | 17 => (36891 / 62500000000 : ℝ)
  | 18 => (-131453 / 200000000000 : ℝ)
  | 19 => (-961571 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch021Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3999741 / 200000000000 : ℝ)
  | 1 => (9533731 / 500000000000 : ℝ)
  | 2 => (18119419 / 1000000000000 : ℝ)
  | 3 => (8577239 / 500000000000 : ℝ)
  | 4 => (31587 / 1953125000 : ℝ)
  | 5 => (15173521 / 1000000000000 : ℝ)
  | 6 => (3539329 / 250000000000 : ℝ)
  | 7 => (13123837 / 1000000000000 : ℝ)
  | 8 => (377281 / 31250000000 : ℝ)
  | 9 => (11004691 / 1000000000000 : ℝ)
  | 10 => (1983769 / 200000000000 : ℝ)
  | 11 => (8815367 / 1000000000000 : ℝ)
  | 12 => (7694171 / 1000000000000 : ℝ)
  | 13 => (1638793 / 250000000000 : ℝ)
  | 14 => (2699143 / 500000000000 : ℝ)
  | 15 => (527929 / 125000000000 : ℝ)
  | 16 => (5919 / 1953125000 : ℝ)
  | 17 => (227437 / 125000000000 : ℝ)
  | 18 => (590257 / 1000000000000 : ℝ)
  | 19 => (-41079 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch021Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((420 : ℝ) + (j.val : ℝ)) / 1600)
      (((420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch021Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch021Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((420 : ℝ) + (j.val : ℝ)) / 1600)
    (((420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch021Neg65WeightLower j.val) (hpThetaShiftTwoBatch021Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch021Neg65WeightLower, hpThetaShiftTwoBatch021Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch021Neg65_integral_bounds :
    (20170531 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (7143887 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch021Lower hpThetaJensenCellsBatch021Upper
    hpThetaShiftTwoBatch021Neg65WeightLower hpThetaShiftTwoBatch021Neg65WeightUpper hpThetaJensenCellsBatch021_bounds hpThetaShiftTwoBatch021Neg65_weight_bounds
  have hl : (20170531 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch021Lower j * hpThetaShiftTwoBatch021Neg65WeightLower j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftTwoBatch021Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftTwoBatch021Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch021Lower j * hpThetaShiftTwoBatch021Neg65WeightUpper j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftTwoBatch021Neg65WeightUpper j) / 1600) ≤ (7143887 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftTwoBatch021Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (420 : ℝ) / 1600 = 21 / 80 by norm_num,
    show ((420 : ℝ) + 20) / 1600 = (21 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch021Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (26097503 / 250000000000 : ℝ)
  | 1 => (104323087 / 1000000000000 : ℝ)
  | 2 => (20848737 / 200000000000 : ℝ)
  | 3 => (104151661 / 1000000000000 : ℝ)
  | 4 => (13005859 / 125000000000 : ℝ)
  | 5 => (103929171 / 1000000000000 : ℝ)
  | 6 => (103798413 / 1000000000000 : ℝ)
  | 7 => (51827227 / 500000000000 : ℝ)
  | 8 => (103497147 / 1000000000000 : ℝ)
  | 9 => (51663173 / 500000000000 : ℝ)
  | 10 => (51570953 / 500000000000 : ℝ)
  | 11 => (51471839 / 500000000000 : ℝ)
  | 12 => (51365759 / 500000000000 : ℝ)
  | 13 => (102505279 / 1000000000000 : ℝ)
  | 14 => (25566203 / 250000000000 : ℝ)
  | 15 => (25502493 / 250000000000 : ℝ)
  | 16 => (101740611 / 1000000000000 : ℝ)
  | 17 => (50728291 / 500000000000 : ℝ)
  | 18 => (101157737 / 1000000000000 : ℝ)
  | 19 => (100843929 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch021Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (52222303 / 500000000000 : ℝ)
  | 1 => (104390013 / 1000000000000 : ℝ)
  | 2 => (6520193 / 62500000000 : ℝ)
  | 3 => (52121843 / 500000000000 : ℝ)
  | 4 => (52075831 / 500000000000 : ℝ)
  | 5 => (104046873 / 1000000000000 : ℝ)
  | 6 => (25982293 / 250000000000 : ℝ)
  | 7 => (51899207 / 500000000000 : ℝ)
  | 8 => (20730891 / 200000000000 : ℝ)
  | 9 => (25874287 / 250000000000 : ℝ)
  | 10 => (103326347 / 1000000000000 : ℝ)
  | 11 => (103141907 / 1000000000000 : ℝ)
  | 12 => (102943679 / 1000000000000 : ℝ)
  | 13 => (102731519 / 1000000000000 : ℝ)
  | 14 => (320329 / 3125000000 : ℝ)
  | 15 => (102264813 / 1000000000000 : ℝ)
  | 16 => (102009973 / 1000000000000 : ℝ)
  | 17 => (25435153 / 250000000000 : ℝ)
  | 18 => (101456583 / 1000000000000 : ℝ)
  | 19 => (50578869 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch021Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((420 : ℝ) + (j.val : ℝ)) / 1600)
      (((420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch021Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch021Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((420 : ℝ) + (j.val : ℝ)) / 1600)
    (((420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch021Neg45WeightLower j.val) (hpThetaShiftTwoBatch021Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch021Neg45WeightLower, hpThetaShiftTwoBatch021Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch021Neg45_integral_bounds :
    (564722649 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (572902179 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch021Lower hpThetaJensenCellsBatch021Upper
    hpThetaShiftTwoBatch021Neg45WeightLower hpThetaShiftTwoBatch021Neg45WeightUpper hpThetaJensenCellsBatch021_bounds hpThetaShiftTwoBatch021Neg45_weight_bounds
  have hl : (564722649 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch021Lower j * hpThetaShiftTwoBatch021Neg45WeightLower j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftTwoBatch021Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftTwoBatch021Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch021Lower j * hpThetaShiftTwoBatch021Neg45WeightUpper j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftTwoBatch021Neg45WeightUpper j) / 1600) ≤ (572902179 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftTwoBatch021Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (420 : ℝ) / 1600 = 21 / 80 by norm_num,
    show ((420 : ℝ) + 20) / 1600 = (21 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch021Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (215548497 / 1000000000000 : ℝ)
  | 1 => (108427809 / 500000000000 : ℝ)
  | 2 => (218162361 / 1000000000000 : ℝ)
  | 3 => (54867157 / 250000000000 : ℝ)
  | 4 => (220774319 / 1000000000000 : ℝ)
  | 5 => (27759917 / 125000000000 : ℝ)
  | 6 => (223383577 / 1000000000000 : ℝ)
  | 7 => (224686941 / 1000000000000 : ℝ)
  | 8 => (225989327 / 1000000000000 : ℝ)
  | 9 => (22729063 / 100000000000 : ℝ)
  | 10 => (57147687 / 250000000000 : ℝ)
  | 11 => (28736197 / 125000000000 : ℝ)
  | 12 => (231187009 / 1000000000000 : ℝ)
  | 13 => (232482939 / 1000000000000 : ℝ)
  | 14 => (11688863 / 50000000000 : ℝ)
  | 15 => (29383733 / 125000000000 : ℝ)
  | 16 => (236360643 / 1000000000000 : ℝ)
  | 17 => (118824743 / 500000000000 : ℝ)
  | 18 => (238936283 / 1000000000000 : ℝ)
  | 19 => (240220923 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch021Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (216855619 / 1000000000000 : ℝ)
  | 1 => (109081181 / 500000000000 : ℝ)
  | 2 => (219468629 / 1000000000000 : ℝ)
  | 3 => (2759679 / 12500000000 : ℝ)
  | 4 => (222079337 / 1000000000000 : ℝ)
  | 5 => (111691789 / 500000000000 : ℝ)
  | 6 => (112343471 / 500000000000 : ℝ)
  | 7 => (14124333 / 62500000000 : ℝ)
  | 8 => (227290631 / 1000000000000 : ℝ)
  | 9 => (228590749 / 1000000000000 : ℝ)
  | 10 => (229889577 / 1000000000000 : ℝ)
  | 11 => (23118701 / 100000000000 : ℝ)
  | 12 => (11624147 / 50000000000 : ℝ)
  | 13 => (233777261 / 1000000000000 : ℝ)
  | 14 => (47013973 / 200000000000 : ℝ)
  | 15 => (59090161 / 250000000000 : ℝ)
  | 16 => (237649487 / 1000000000000 : ℝ)
  | 17 => (59734071 / 250000000000 : ℝ)
  | 18 => (60055231 / 250000000000 : ℝ)
  | 19 => (48300659 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch021Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((420 : ℝ) + (j.val : ℝ)) / 1600)
      (((420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch021Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch021Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((420 : ℝ) + (j.val : ℝ)) / 1600)
    (((420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch021Neg25WeightLower j.val) (hpThetaShiftTwoBatch021Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch021Neg25WeightLower, hpThetaShiftTwoBatch021Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch021Neg25_integral_bounds :
    (2496928351 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (2543127479 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch021Lower hpThetaJensenCellsBatch021Upper
    hpThetaShiftTwoBatch021Neg25WeightLower hpThetaShiftTwoBatch021Neg25WeightUpper hpThetaJensenCellsBatch021_bounds hpThetaShiftTwoBatch021Neg25_weight_bounds
  have hl : (2496928351 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch021Lower j * hpThetaShiftTwoBatch021Neg25WeightLower j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftTwoBatch021Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftTwoBatch021Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch021Lower j * hpThetaShiftTwoBatch021Neg25WeightUpper j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftTwoBatch021Neg25WeightUpper j) / 1600) ≤ (2543127479 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftTwoBatch021Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (420 : ℝ) / 1600 = 21 / 80 by norm_num,
    show ((420 : ℝ) + 20) / 1600 = (21 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch021Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch021Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch021Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch021Neg25_integral_bounds
end HodgeProofHP
