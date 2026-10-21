/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch078

/-! Exact signed weight and batch integral certificates, batch 78 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch078Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2651947998779 / 200000000000 : ℝ)
  | 1 => (-834909516551 / 62500000000 : ℝ)
  | 2 => (-13458011812947 / 1000000000000 : ℝ)
  | 3 => (-3389530582171 / 250000000000 : ℝ)
  | 4 => (-6829443760243 / 500000000000 : ℝ)
  | 5 => (-275206222299 / 20000000000 : ℝ)
  | 6 => (-13862396856881 / 1000000000000 : ℝ)
  | 7 => (-218205445459 / 15625000000 : ℝ)
  | 8 => (-14068569853889 / 1000000000000 : ℝ)
  | 9 => (-14172664690317 / 1000000000000 : ℝ)
  | 10 => (-2855487367413 / 200000000000 : ℝ)
  | 11 => (-1438289013113 / 100000000000 : ℝ)
  | 12 => (-7244514214087 / 500000000000 : ℝ)
  | 13 => (-14595855602601 / 1000000000000 : ℝ)
  | 14 => (-14703375547633 / 1000000000000 : ℝ)
  | 15 => (-14811592175389 / 1000000000000 : ℝ)
  | 16 => (-14920509416959 / 1000000000000 : ℝ)
  | 17 => (-7515065611243 / 500000000000 : ℝ)
  | 18 => (-378511539031 / 25000000000 : ℝ)
  | 19 => (-238304756589 / 15625000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch078Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-411299103993 / 31250000000 : ℝ)
  | 1 => (-6629869996947 / 500000000000 : ℝ)
  | 2 => (-2671710452963 / 200000000000 : ℝ)
  | 3 => (-6729005906473 / 500000000000 : ℝ)
  | 4 => (-13558122328683 / 1000000000000 : ℝ)
  | 5 => (-2731777504097 / 200000000000 : ℝ)
  | 6 => (-13760311114949 / 1000000000000 : ℝ)
  | 7 => (-173279960711 / 12500000000 : ℝ)
  | 8 => (-4468847523 / 320000000 : ℝ)
  | 9 => (-219821403967 / 15625000000 : ℝ)
  | 10 => (-3543166172579 / 250000000000 : ℝ)
  | 11 => (-1784679604633 / 125000000000 : ℝ)
  | 12 => (-14382890131129 / 1000000000000 : ℝ)
  | 13 => (-14489028428173 / 1000000000000 : ℝ)
  | 14 => (-72979278013 / 5000000000 : ℝ)
  | 15 => (-918960971727 / 62500000000 : ℝ)
  | 16 => (-3702898043847 / 250000000000 : ℝ)
  | 17 => (-7460254708479 / 500000000000 : ℝ)
  | 18 => (-3006026244497 / 200000000000 : ℝ)
  | 19 => (-15140461561239 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch078Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1560 : ℝ) + (j.val : ℝ)) / 1600)
      (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch078Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch078Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1560 : ℝ) + (j.val : ℝ)) / 1600)
    (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch078Neg100WeightLower j.val) (hpThetaShiftTwoBatch078Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch078Neg100WeightLower, hpThetaShiftTwoBatch078Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch078Neg100_integral_bounds :
    (-43182949 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-207258433 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch078Lower hpThetaJensenCellsBatch078Upper
    hpThetaShiftTwoBatch078Neg100WeightLower hpThetaShiftTwoBatch078Neg100WeightUpper hpThetaJensenCellsBatch078_bounds hpThetaShiftTwoBatch078Neg100_weight_bounds
  have hl : (-43182949 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch078Lower j * hpThetaShiftTwoBatch078Neg100WeightLower j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftTwoBatch078Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftTwoBatch078Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch078Lower j * hpThetaShiftTwoBatch078Neg100WeightUpper j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftTwoBatch078Neg100WeightUpper j) / 1600) ≤ (-207258433 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftTwoBatch078Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1560 : ℝ) / 1600 = 78 / 80 by norm_num,
    show ((1560 : ℝ) + 20) / 1600 = (78 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch078Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2228422586839 / 1000000000000 : ℝ)
  | 1 => (-449480117631 / 200000000000 : ℝ)
  | 2 => (-2266516061201 / 1000000000000 : ℝ)
  | 3 => (-1142884926159 / 500000000000 : ℝ)
  | 4 => (-1152581406121 / 500000000000 : ℝ)
  | 5 => (-58117394903 / 25000000000 : ℝ)
  | 6 => (-2344369663531 / 1000000000000 : ℝ)
  | 7 => (-2364185278503 / 1000000000000 : ℝ)
  | 8 => (-2384143509533 / 1000000000000 : ℝ)
  | 9 => (-1202122614803 / 500000000000 : ℝ)
  | 10 => (-303061414527 / 125000000000 : ℝ)
  | 11 => (-2444882651383 / 1000000000000 : ℝ)
  | 12 => (-1232710060837 / 500000000000 : ℝ)
  | 13 => (-124305230911 / 50000000000 : ℝ)
  | 14 => (-125346851837 / 50000000000 : ℝ)
  | 15 => (-505583655511 / 200000000000 : ℝ)
  | 16 => (-2549049245613 / 1000000000000 : ℝ)
  | 17 => (-1285165425253 / 500000000000 : ℝ)
  | 18 => (-2591764006487 / 1000000000000 : ℝ)
  | 19 => (-2613349632499 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch078Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2209581215283 / 1000000000000 : ℝ)
  | 1 => (-1114211293419 / 500000000000 : ℝ)
  | 2 => (-1123700294077 / 500000000000 : ℝ)
  | 3 => (-5666290153 / 2500000000 : ℝ)
  | 4 => (-2285769852317 / 1000000000000 : ℝ)
  | 5 => (-2305162812241 / 1000000000000 : ℝ)
  | 6 => (-2324695796119 / 1000000000000 : ℝ)
  | 7 => (-234436966353 / 100000000000 : ℝ)
  | 8 => (-1182092639251 / 500000000000 : ℝ)
  | 9 => (-596035877383 / 250000000000 : ℝ)
  | 10 => (-480849045921 / 200000000000 : ℝ)
  | 11 => (-484898263243 / 200000000000 : ℝ)
  | 12 => (-1222441325691 / 500000000000 : ℝ)
  | 13 => (-2465420121673 / 1000000000000 : ℝ)
  | 14 => (-2486104618219 / 1000000000000 : ℝ)
  | 15 => (-2506937036739 / 1000000000000 : ℝ)
  | 16 => (-1263959138777 / 500000000000 : ℝ)
  | 17 => (-637262311403 / 250000000000 : ℝ)
  | 18 => (-514066170101 / 200000000000 : ℝ)
  | 19 => (-1295882003243 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch078Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1560 : ℝ) + (j.val : ℝ)) / 1600)
      (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch078Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch078Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1560 : ℝ) + (j.val : ℝ)) / 1600)
    (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch078Neg65WeightLower j.val) (hpThetaShiftTwoBatch078Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch078Neg65WeightLower, hpThetaShiftTwoBatch078Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch078Neg65_integral_bounds :
    (-572231 / 15625000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-35118483 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch078Lower hpThetaJensenCellsBatch078Upper
    hpThetaShiftTwoBatch078Neg65WeightLower hpThetaShiftTwoBatch078Neg65WeightUpper hpThetaJensenCellsBatch078_bounds hpThetaShiftTwoBatch078Neg65_weight_bounds
  have hl : (-572231 / 15625000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch078Lower j * hpThetaShiftTwoBatch078Neg65WeightLower j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftTwoBatch078Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftTwoBatch078Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch078Lower j * hpThetaShiftTwoBatch078Neg65WeightUpper j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftTwoBatch078Neg65WeightUpper j) / 1600) ≤ (-35118483 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftTwoBatch078Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1560 : ℝ) / 1600 = 78 / 80 by norm_num,
    show ((1560 : ℝ) + 20) / 1600 = (78 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch078Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-280850618727 / 1000000000000 : ℝ)
  | 1 => (-142136080389 / 500000000000 : ℝ)
  | 2 => (-287724234757 / 1000000000000 : ℝ)
  | 3 => (-145603528047 / 500000000000 : ℝ)
  | 4 => (-36840105181 / 125000000000 : ℝ)
  | 5 => (-298265808711 / 1000000000000 : ℝ)
  | 6 => (-60368435403 / 200000000000 : ℝ)
  | 7 => (-305450166737 / 1000000000000 : ℝ)
  | 8 => (-154544999753 / 500000000000 : ℝ)
  | 9 => (-9773809319 / 31250000000 : ℝ)
  | 10 => (-316466086991 / 1000000000000 : ℝ)
  | 11 => (-320202791273 / 1000000000000 : ℝ)
  | 12 => (-323972237743 / 1000000000000 : ℝ)
  | 13 => (-327774654373 / 1000000000000 : ℝ)
  | 14 => (-16580513521 / 50000000000 : ℝ)
  | 15 => (-335479316433 / 1000000000000 : ℝ)
  | 16 => (-339382024259 / 1000000000000 : ℝ)
  | 17 => (-343318627047 / 1000000000000 : ℝ)
  | 18 => (-173644679629 / 500000000000 : ℝ)
  | 19 => (-175647228333 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch078Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-277459394397 / 1000000000000 : ℝ)
  | 1 => (-140425309363 / 500000000000 : ℝ)
  | 2 => (-284272160777 / 1000000000000 : ℝ)
  | 3 => (-71931058689 / 250000000000 : ℝ)
  | 4 => (-291207056093 / 1000000000000 : ℝ)
  | 5 => (-294720841447 / 1000000000000 : ℝ)
  | 6 => (-29826580871 / 100000000000 : ℝ)
  | 7 => (-150921088507 / 500000000000 : ℝ)
  | 8 => (-19090635421 / 62500000000 : ℝ)
  | 9 => (-61817999901 / 200000000000 : ℝ)
  | 10 => (-312761898207 / 1000000000000 : ℝ)
  | 11 => (-31646608699 / 100000000000 : ℝ)
  | 12 => (-40025348909 / 125000000000 : ℝ)
  | 13 => (-161986118871 / 500000000000 : ℝ)
  | 14 => (-81943663593 / 250000000000 : ℝ)
  | 15 => (-331610270419 / 1000000000000 : ℝ)
  | 16 => (-20967457277 / 62500000000 : ℝ)
  | 17 => (-169691012129 / 500000000000 : ℝ)
  | 18 => (-171659313523 / 500000000000 : ℝ)
  | 19 => (-347289359257 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch078Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1560 : ℝ) + (j.val : ℝ)) / 1600)
      (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch078Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch078Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1560 : ℝ) + (j.val : ℝ)) / 1600)
    (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch078Neg45WeightLower j.val) (hpThetaShiftTwoBatch078Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch078Neg45WeightLower, hpThetaShiftTwoBatch078Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch078Neg45_integral_bounds :
    (-4762227 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-4551023 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch078Lower hpThetaJensenCellsBatch078Upper
    hpThetaShiftTwoBatch078Neg45WeightLower hpThetaShiftTwoBatch078Neg45WeightUpper hpThetaJensenCellsBatch078_bounds hpThetaShiftTwoBatch078Neg45_weight_bounds
  have hl : (-4762227 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch078Lower j * hpThetaShiftTwoBatch078Neg45WeightLower j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftTwoBatch078Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftTwoBatch078Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch078Lower j * hpThetaShiftTwoBatch078Neg45WeightUpper j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftTwoBatch078Neg45WeightUpper j) / 1600) ≤ (-4551023 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftTwoBatch078Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1560 : ℝ) / 1600 = 78 / 80 by norm_num,
    show ((1560 : ℝ) + 20) / 1600 = (78 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch078Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (24351035759 / 500000000000 : ℝ)
  | 1 => (4893276131 / 100000000000 : ℝ)
  | 2 => (9832666069 / 200000000000 : ℝ)
  | 3 => (9878753309 / 200000000000 : ℝ)
  | 4 => (12406014429 / 250000000000 : ℝ)
  | 5 => (12463547887 / 250000000000 : ℝ)
  | 6 => (5008415561 / 100000000000 : ℝ)
  | 7 => (50313937357 / 1000000000000 : ℝ)
  | 8 => (50543524119 / 1000000000000 : ℝ)
  | 9 => (6346612889 / 125000000000 : ℝ)
  | 10 => (25501030713 / 500000000000 : ℝ)
  | 11 => (3201936627 / 62500000000 : ℝ)
  | 12 => (51459663779 / 1000000000000 : ℝ)
  | 13 => (3230505087 / 62500000000 : ℝ)
  | 14 => (51916225473 / 1000000000000 : ℝ)
  | 15 => (52144082499 / 1000000000000 : ℝ)
  | 16 => (6546454853 / 125000000000 : ℝ)
  | 17 => (1643715021 / 31250000000 : ℝ)
  | 18 => (10565158829 / 200000000000 : ℝ)
  | 19 => (26526182607 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch078Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (48932761311 / 1000000000000 : ℝ)
  | 1 => (24581665173 / 500000000000 : ℝ)
  | 2 => (24696883273 / 500000000000 : ℝ)
  | 3 => (49624057717 / 1000000000000 : ℝ)
  | 4 => (49854191549 / 1000000000000 : ℝ)
  | 5 => (50084155611 / 1000000000000 : ℝ)
  | 6 => (25156968679 / 500000000000 : ℝ)
  | 7 => (1263588103 / 25000000000 : ℝ)
  | 8 => (50772903113 / 1000000000000 : ℝ)
  | 9 => (51002061427 / 1000000000000 : ℝ)
  | 10 => (51230986033 / 1000000000000 : ℝ)
  | 11 => (2572983189 / 50000000000 : ℝ)
  | 12 => (51688081393 / 1000000000000 : ℝ)
  | 13 => (25958112737 / 500000000000 : ℝ)
  | 14 => (20857633 / 400000000 : ℝ)
  | 15 => (2094865553 / 40000000000 : ℝ)
  | 16 => (52598880673 / 1000000000000 : ℝ)
  | 17 => (26412897073 / 500000000000 : ℝ)
  | 18 => (10610473043 / 200000000000 : ℝ)
  | 19 => (26639289863 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch078Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1560 : ℝ) + (j.val : ℝ)) / 1600)
      (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch078Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch078Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1560 : ℝ) + (j.val : ℝ)) / 1600)
    (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch078Neg25WeightLower j.val) (hpThetaShiftTwoBatch078Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch078Neg25WeightLower, hpThetaShiftTwoBatch078Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch078Neg25_integral_bounds :
    (46753 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (38853 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch078Lower hpThetaJensenCellsBatch078Upper
    hpThetaShiftTwoBatch078Neg25WeightLower hpThetaShiftTwoBatch078Neg25WeightUpper hpThetaJensenCellsBatch078_bounds hpThetaShiftTwoBatch078Neg25_weight_bounds
  have hl : (46753 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch078Lower j * hpThetaShiftTwoBatch078Neg25WeightLower j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftTwoBatch078Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftTwoBatch078Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch078Lower j * hpThetaShiftTwoBatch078Neg25WeightUpper j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftTwoBatch078Neg25WeightUpper j) / 1600) ≤ (38853 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftTwoBatch078Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1560 : ℝ) / 1600 = 78 / 80 by norm_num,
    show ((1560 : ℝ) + 20) / 1600 = (78 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch078Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch078Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch078Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch078Neg25_integral_bounds
end HodgeProofHP
