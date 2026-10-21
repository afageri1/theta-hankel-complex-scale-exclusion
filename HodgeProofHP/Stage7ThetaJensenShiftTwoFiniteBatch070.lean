/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch070

/-! Exact signed weight and batch integral certificates, batch 70 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch070Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3668723012233 / 1000000000000 : ℝ)
  | 1 => (-925208288831 / 250000000000 : ℝ)
  | 2 => (-3733187511359 / 1000000000000 : ℝ)
  | 3 => (-3765787682559 / 1000000000000 : ℝ)
  | 4 => (-1899317640053 / 500000000000 : ℝ)
  | 5 => (-3831731924181 / 1000000000000 : ℝ)
  | 6 => (-966269811003 / 250000000000 : ℝ)
  | 7 => (-3898678877913 / 1000000000000 : ℝ)
  | 8 => (-1966266236663 / 500000000000 : ℝ)
  | 9 => (-3966641686863 / 1000000000000 : ℝ)
  | 10 => (-125031505761 / 31250000000 : ℝ)
  | 11 => (-2017816820439 / 500000000000 : ℝ)
  | 12 => (-162820789633 / 40000000000 : ℝ)
  | 13 => (-4105668177919 / 1000000000000 : ℝ)
  | 14 => (-4141080655277 / 1000000000000 : ℝ)
  | 15 => (-2088379442721 / 500000000000 : ℝ)
  | 16 => (-4212704590433 / 1000000000000 : ℝ)
  | 17 => (-1062229875447 / 250000000000 : ℝ)
  | 18 => (-1071351340151 / 250000000000 : ℝ)
  | 19 => (-4322163917587 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch070Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3636855488781 / 1000000000000 : ℝ)
  | 1 => (-458590376529 / 125000000000 : ℝ)
  | 2 => (-3700833155323 / 1000000000000 : ℝ)
  | 3 => (-1866593755679 / 500000000000 : ℝ)
  | 4 => (-1882893841279 / 500000000000 : ℝ)
  | 5 => (-759727056021 / 200000000000 : ℝ)
  | 6 => (-191586596209 / 50000000000 : ℝ)
  | 7 => (-3865079244011 / 1000000000000 : ℝ)
  | 8 => (-487334859739 / 125000000000 : ℝ)
  | 9 => (-157301298933 / 40000000000 : ℝ)
  | 10 => (-1983320843431 / 500000000000 : ℝ)
  | 11 => (-4001008184351 / 1000000000000 : ℝ)
  | 12 => (-4035633640877 / 1000000000000 : ℝ)
  | 13 => (-508814967603 / 125000000000 : ℝ)
  | 14 => (-2052834088959 / 500000000000 : ℝ)
  | 15 => (-1035270163819 / 250000000000 : ℝ)
  | 16 => (-4176758885441 / 1000000000000 : ℝ)
  | 17 => (-131647018451 / 31250000000 : ℝ)
  | 18 => (-4248919501787 / 1000000000000 : ℝ)
  | 19 => (-4285405360603 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch070Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1400 : ℝ) + (j.val : ℝ)) / 1600)
      (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch070Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch070Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1400 : ℝ) + (j.val : ℝ)) / 1600)
    (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch070Neg100WeightLower j.val) (hpThetaShiftTwoBatch070Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch070Neg100WeightLower, hpThetaShiftTwoBatch070Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch070Neg100_integral_bounds :
    (-2172237803 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-2093185861 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch070Lower hpThetaJensenCellsBatch070Upper
    hpThetaShiftTwoBatch070Neg100WeightLower hpThetaShiftTwoBatch070Neg100WeightUpper hpThetaJensenCellsBatch070_bounds hpThetaShiftTwoBatch070Neg100_weight_bounds
  have hl : (-2172237803 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch070Lower j * hpThetaShiftTwoBatch070Neg100WeightLower j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftTwoBatch070Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftTwoBatch070Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch070Lower j * hpThetaShiftTwoBatch070Neg100WeightUpper j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftTwoBatch070Neg100WeightUpper j) / 1600) ≤ (-2093185861 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftTwoBatch070Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1400 : ℝ) / 1600 = 70 / 80 by norm_num,
    show ((1400 : ℝ) + 20) / 1600 = (70 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch070Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-241211373041 / 500000000000 : ℝ)
  | 1 => (-121932572663 / 250000000000 : ℝ)
  | 2 => (-98617004177 / 200000000000 : ℝ)
  | 3 => (-249243641449 / 500000000000 : ℝ)
  | 4 => (-50393742491 / 100000000000 : ℝ)
  | 5 => (-509435797247 / 1000000000000 : ℝ)
  | 6 => (-12874568809 / 25000000000 : ℝ)
  | 7 => (-520578644827 / 1000000000000 : ℝ)
  | 8 => (-131555957843 / 250000000000 : ℝ)
  | 9 => (-531918670867 / 1000000000000 : ℝ)
  | 10 => (-537663524351 / 1000000000000 : ℝ)
  | 11 => (-271729377517 / 500000000000 : ℝ)
  | 12 => (-68663091039 / 125000000000 : ℝ)
  | 13 => (-8675028309 / 15625000000 : ℝ)
  | 14 => (-561150375223 / 1000000000000 : ℝ)
  | 15 => (-283575395333 / 500000000000 : ℝ)
  | 16 => (-573203432347 / 1000000000000 : ℝ)
  | 17 => (-289654338373 / 500000000000 : ℝ)
  | 18 => (-292733451297 / 500000000000 : ℝ)
  | 19 => (-295839245441 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch070Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-59645255393 / 125000000000 : ℝ)
  | 1 => (-482422746081 / 1000000000000 : ℝ)
  | 2 => (-487730290651 / 1000000000000 : ℝ)
  | 3 => (-123271255221 / 250000000000 : ℝ)
  | 4 => (-498487282897 / 1000000000000 : ℝ)
  | 5 => (-503937424909 / 1000000000000 : ℝ)
  | 6 => (-254717898623 / 500000000000 : ℝ)
  | 7 => (-514982752359 / 1000000000000 : ℝ)
  | 8 => (-260289322413 / 500000000000 : ℝ)
  | 9 => (-526223831371 / 1000000000000 : ℝ)
  | 10 => (-265959335433 / 500000000000 : ℝ)
  | 11 => (-10753270487 / 20000000000 : ℝ)
  | 12 => (-543458755033 / 1000000000000 : ℝ)
  | 13 => (-549304728311 / 1000000000000 : ℝ)
  | 14 => (-22208072471 / 40000000000 : ℝ)
  | 15 => (-280575187611 / 500000000000 : ℝ)
  | 16 => (-113430158133 / 200000000000 : ℝ)
  | 17 => (-286601716173 / 500000000000 : ℝ)
  | 18 => (-115861735349 / 200000000000 : ℝ)
  | 19 => (-585466902593 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch070Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1400 : ℝ) + (j.val : ℝ)) / 1600)
      (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch070Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch070Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1400 : ℝ) + (j.val : ℝ)) / 1600)
    (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch070Neg65WeightLower j.val) (hpThetaShiftTwoBatch070Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch070Neg65WeightLower, hpThetaShiftTwoBatch070Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch070Neg65_integral_bounds :
    (-11653339 / 40000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-14006719 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch070Lower hpThetaJensenCellsBatch070Upper
    hpThetaShiftTwoBatch070Neg65WeightLower hpThetaShiftTwoBatch070Neg65WeightUpper hpThetaJensenCellsBatch070_bounds hpThetaShiftTwoBatch070Neg65_weight_bounds
  have hl : (-11653339 / 40000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch070Lower j * hpThetaShiftTwoBatch070Neg65WeightLower j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftTwoBatch070Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftTwoBatch070Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch070Lower j * hpThetaShiftTwoBatch070Neg65WeightUpper j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftTwoBatch070Neg65WeightUpper j) / 1600) ≤ (-14006719 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftTwoBatch070Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1400 : ℝ) / 1600 = 70 / 80 by norm_num,
    show ((1400 : ℝ) + 20) / 1600 = (70 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch070Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1374561257 / 200000000000 : ℝ)
  | 1 => (-3736039131 / 500000000000 : ℝ)
  | 2 => (-4039918349 / 500000000000 : ℝ)
  | 3 => (-4348080241 / 500000000000 : ℝ)
  | 4 => (-2330282263 / 250000000000 : ℝ)
  | 5 => (-1990964481 / 200000000000 : ℝ)
  | 6 => (-5298660547 / 500000000000 : ℝ)
  | 7 => (-2812176559 / 250000000000 : ℝ)
  | 8 => (-1488632439 / 125000000000 : ℝ)
  | 9 => (-12578463169 / 1000000000000 : ℝ)
  | 10 => (-13257000029 / 1000000000000 : ℝ)
  | 11 => (-3486188371 / 250000000000 : ℝ)
  | 12 => (-2928361501 / 200000000000 : ℝ)
  | 13 => (-3837061661 / 250000000000 : ℝ)
  | 14 => (-3212831207 / 200000000000 : ℝ)
  | 15 => (-83948107 / 5000000000 : ℝ)
  | 16 => (-2190591131 / 125000000000 : ℝ)
  | 17 => (-3653913177 / 200000000000 : ℝ)
  | 18 => (-19024219409 / 1000000000000 : ℝ)
  | 19 => (-494719443 / 25000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch070Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6281942429 / 1000000000000 : ℝ)
  | 1 => (-1718201571 / 250000000000 : ℝ)
  | 2 => (-7472078261 / 1000000000000 : ℝ)
  | 3 => (-8079836697 / 1000000000000 : ℝ)
  | 4 => (-8696160481 / 1000000000000 : ℝ)
  | 5 => (-9321129051 / 1000000000000 : ℝ)
  | 6 => (-2488705601 / 250000000000 : ℝ)
  | 7 => (-10597321093 / 1000000000000 : ℝ)
  | 8 => (-2249741247 / 200000000000 : ℝ)
  | 9 => (-11909059511 / 1000000000000 : ℝ)
  | 10 => (-196538487 / 15625000000 : ℝ)
  | 11 => (-3314250007 / 250000000000 : ℝ)
  | 12 => (-13944753483 / 1000000000000 : ℝ)
  | 13 => (-915112969 / 62500000000 : ℝ)
  | 14 => (-15348246643 / 1000000000000 : ℝ)
  | 15 => (-8032078017 / 500000000000 : ℝ)
  | 16 => (-16789621399 / 1000000000000 : ℝ)
  | 17 => (-17524729047 / 1000000000000 : ℝ)
  | 18 => (-4567391471 / 250000000000 : ℝ)
  | 19 => (-1189013713 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch070Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1400 : ℝ) + (j.val : ℝ)) / 1600)
      (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch070Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch070Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1400 : ℝ) + (j.val : ℝ)) / 1600)
    (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch070Neg45WeightLower j.val) (hpThetaShiftTwoBatch070Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch070Neg45WeightLower, hpThetaShiftTwoBatch070Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch070Neg45_integral_bounds :
    (-6913663 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-6363189 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch070Lower hpThetaJensenCellsBatch070Upper
    hpThetaShiftTwoBatch070Neg45WeightLower hpThetaShiftTwoBatch070Neg45WeightUpper hpThetaJensenCellsBatch070_bounds hpThetaShiftTwoBatch070Neg45_weight_bounds
  have hl : (-6913663 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch070Lower j * hpThetaShiftTwoBatch070Neg45WeightLower j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftTwoBatch070Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftTwoBatch070Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch070Lower j * hpThetaShiftTwoBatch070Neg45WeightUpper j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftTwoBatch070Neg45WeightUpper j) / 1600) ≤ (-6363189 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftTwoBatch070Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1400 : ℝ) / 1600 = 70 / 80 by norm_num,
    show ((1400 : ℝ) + 20) / 1600 = (70 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch070Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (15912408851 / 1000000000000 : ℝ)
  | 1 => (3214130613 / 200000000000 : ℝ)
  | 2 => (4057404411 / 250000000000 : ℝ)
  | 3 => (16389301983 / 1000000000000 : ℝ)
  | 4 => (16549705441 / 1000000000000 : ℝ)
  | 5 => (835541367 / 50000000000 : ℝ)
  | 6 => (4218166741 / 250000000000 : ℝ)
  | 7 => (8517611779 / 500000000000 : ℝ)
  | 8 => (1719849633 / 100000000000 : ℝ)
  | 9 => (8681242223 / 500000000000 : ℝ)
  | 10 => (4381796759 / 250000000000 : ℝ)
  | 11 => (17692603189 / 1000000000000 : ℝ)
  | 12 => (8929365977 / 500000000000 : ℝ)
  | 13 => (901278617 / 50000000000 : ℝ)
  | 14 => (4548280829 / 250000000000 : ℝ)
  | 15 => (143448311 / 7812500000 : ℝ)
  | 16 => (289536761 / 15625000000 : ℝ)
  | 17 => (18700028847 / 1000000000000 : ℝ)
  | 18 => (117940069 / 6250000000 : ℝ)
  | 19 => (19041498043 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch070Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (8035326533 / 500000000000 : ℝ)
  | 1 => (3245923529 / 200000000000 : ℝ)
  | 2 => (512165687 / 31250000000 : ℝ)
  | 3 => (8274852721 / 500000000000 : ℝ)
  | 4 => (16710827341 / 1000000000000 : ℝ)
  | 5 => (3374533393 / 200000000000 : ℝ)
  | 6 => (17035223559 / 1000000000000 : ℝ)
  | 7 => (17198496331 / 1000000000000 : ℝ)
  | 8 => (17362484447 / 1000000000000 : ℝ)
  | 9 => (17527187037 / 1000000000000 : ℝ)
  | 10 => (1769260319 / 100000000000 : ℝ)
  | 11 => (3571746391 / 200000000000 : ℝ)
  | 12 => (18025572341 / 1000000000000 : ℝ)
  | 13 => (18193123317 / 1000000000000 : ℝ)
  | 14 => (18361383809 / 1000000000000 : ℝ)
  | 15 => (3706070541 / 200000000000 : ℝ)
  | 16 => (1168751803 / 62500000000 : ℝ)
  | 17 => (18870411041 / 1000000000000 : ℝ)
  | 18 => (4760374511 / 250000000000 : ℝ)
  | 19 => (9606644287 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch070Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1400 : ℝ) + (j.val : ℝ)) / 1600)
      (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch070Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch070Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1400 : ℝ) + (j.val : ℝ)) / 1600)
    (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch070Neg25WeightLower j.val) (hpThetaShiftTwoBatch070Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch070Neg25WeightLower, hpThetaShiftTwoBatch070Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch070Neg25_integral_bounds :
    (9236719 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (4796649 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch070Lower hpThetaJensenCellsBatch070Upper
    hpThetaShiftTwoBatch070Neg25WeightLower hpThetaShiftTwoBatch070Neg25WeightUpper hpThetaJensenCellsBatch070_bounds hpThetaShiftTwoBatch070Neg25_weight_bounds
  have hl : (9236719 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch070Lower j * hpThetaShiftTwoBatch070Neg25WeightLower j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftTwoBatch070Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftTwoBatch070Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch070Lower j * hpThetaShiftTwoBatch070Neg25WeightUpper j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftTwoBatch070Neg25WeightUpper j) / 1600) ≤ (4796649 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftTwoBatch070Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1400 : ℝ) / 1600 = 70 / 80 by norm_num,
    show ((1400 : ℝ) + 20) / 1600 = (70 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch070Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch070Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch070Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch070Neg25_integral_bounds
end HodgeProofHP
