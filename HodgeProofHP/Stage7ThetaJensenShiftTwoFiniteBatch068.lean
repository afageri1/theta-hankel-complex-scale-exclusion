/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch068

/-! Exact signed weight and batch integral certificates, batch 68 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch068Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2567239859249 / 1000000000000 : ℝ)
  | 1 => (-2590797453923 / 1000000000000 : ℝ)
  | 2 => (-104581682297 / 40000000000 : ℝ)
  | 3 => (-2638474946201 / 1000000000000 : ℝ)
  | 4 => (-1331298702053 / 500000000000 : ℝ)
  | 5 => (-67172768061 / 25000000000 : ℝ)
  | 6 => (-2711416199979 / 1000000000000 : ℝ)
  | 7 => (-1368057571509 / 500000000000 : ℝ)
  | 8 => (-2761008865403 / 1000000000000 : ℝ)
  | 9 => (-348262336071 / 125000000000 : ℝ)
  | 10 => (-351423242697 / 125000000000 : ℝ)
  | 11 => (-2836871961147 / 1000000000000 : ℝ)
  | 12 => (-357819761463 / 125000000000 : ℝ)
  | 13 => (-577689137081 / 200000000000 : ℝ)
  | 14 => (-2914536102181 / 1000000000000 : ℝ)
  | 15 => (-1470415354887 / 500000000000 : ℝ)
  | 16 => (-118693235351 / 40000000000 : ℝ)
  | 17 => (-2994038007661 / 1000000000000 : ℝ)
  | 18 => (-3020953472831 / 1000000000000 : ℝ)
  | 19 => (-381009834831 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch068Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-317983500541 / 125000000000 : ℝ)
  | 1 => (-160452491203 / 62500000000 : ℝ)
  | 2 => (-1295398726961 / 500000000000 : ℝ)
  | 3 => (-163408878589 / 62500000000 : ℝ)
  | 4 => (-13192374731 / 5000000000 : ℝ)
  | 5 => (-532519480821 / 200000000000 : ℝ)
  | 6 => (-2686910722439 / 1000000000000 : ℝ)
  | 7 => (-1355708099989 / 500000000000 : ℝ)
  | 8 => (-2736115143017 / 1000000000000 : ℝ)
  | 9 => (-1380504432701 / 500000000000 : ℝ)
  | 10 => (-2786098688567 / 1000000000000 : ℝ)
  | 11 => (-112455437663 / 40000000000 : ℝ)
  | 12 => (-1418435980573 / 500000000000 : ℝ)
  | 13 => (-2862558091703 / 1000000000000 : ℝ)
  | 14 => (-722111421351 / 250000000000 : ℝ)
  | 15 => (-145726805109 / 50000000000 : ℝ)
  | 16 => (-2940830709773 / 1000000000000 : ℝ)
  | 17 => (-1483665441887 / 500000000000 : ℝ)
  | 18 => (-149701900383 / 50000000000 : ℝ)
  | 19 => (-302095347283 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch068Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1360 : ℝ) + (j.val : ℝ)) / 1600)
      (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch068Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch068Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1360 : ℝ) + (j.val : ℝ)) / 1600)
    (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch068Neg100WeightLower j.val) (hpThetaShiftTwoBatch068Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch068Neg100WeightLower, hpThetaShiftTwoBatch068Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch068Neg100_integral_bounds :
    (-206948667 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-1596456377 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch068Lower hpThetaJensenCellsBatch068Upper
    hpThetaShiftTwoBatch068Neg100WeightLower hpThetaShiftTwoBatch068Neg100WeightUpper hpThetaJensenCellsBatch068_bounds hpThetaShiftTwoBatch068Neg100_weight_bounds
  have hl : (-206948667 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch068Lower j * hpThetaShiftTwoBatch068Neg100WeightLower j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftTwoBatch068Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftTwoBatch068Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch068Lower j * hpThetaShiftTwoBatch068Neg100WeightUpper j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftTwoBatch068Neg100WeightUpper j) / 1600) ≤ (-1596456377 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftTwoBatch068Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1360 : ℝ) / 1600 = 68 / 80 by norm_num,
    show ((1360 : ℝ) + 20) / 1600 = (68 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch068Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6101758189 / 20000000000 : ℝ)
  | 1 => (-154384491047 / 500000000000 : ℝ)
  | 2 => (-78121250681 / 250000000000 : ℝ)
  | 3 => (-7905906039 / 25000000000 : ℝ)
  | 4 => (-320022970539 / 1000000000000 : ℝ)
  | 5 => (-8096136583 / 25000000000 : ℝ)
  | 6 => (-10240749853 / 31250000000 : ℝ)
  | 7 => (-331598843601 / 1000000000000 : ℝ)
  | 8 => (-335530287121 / 1000000000000 : ℝ)
  | 9 => (-678997213 / 2000000000 : ℝ)
  | 10 => (-42938010519 / 125000000000 : ℝ)
  | 11 => (-347547004269 / 1000000000000 : ℝ)
  | 12 => (-351627652829 / 1000000000000 : ℝ)
  | 13 => (-44468289701 / 125000000000 : ℝ)
  | 14 => (-71980657637 / 200000000000 : ℝ)
  | 15 => (-182049427979 / 500000000000 : ℝ)
  | 16 => (-368333314143 / 1000000000000 : ℝ)
  | 17 => (-186303478897 / 500000000000 : ℝ)
  | 18 => (-376920083807 / 1000000000000 : ℝ)
  | 19 => (-23829561933 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch068Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-301441516277 / 1000000000000 : ℝ)
  | 1 => (-305087909449 / 1000000000000 : ℝ)
  | 2 => (-308768982093 / 1000000000000 : ℝ)
  | 3 => (-312485002723 / 1000000000000 : ℝ)
  | 4 => (-316236241559 / 1000000000000 : ℝ)
  | 5 => (-160011485269 / 500000000000 : ℝ)
  | 6 => (-323845463319 / 1000000000000 : ℝ)
  | 7 => (-65540799059 / 200000000000 : ℝ)
  | 8 => (-828997109 / 2500000000 : ℝ)
  | 9 => (-4194128589 / 12500000000 : ℝ)
  | 10 => (-339498606499 / 1000000000000 : ℝ)
  | 11 => (-343504084151 / 1000000000000 : ℝ)
  | 12 => (-86886751067 / 250000000000 : ℝ)
  | 13 => (-87906913207 / 250000000000 : ℝ)
  | 14 => (-355746317607 / 1000000000000 : ℝ)
  | 15 => (-44987911023 / 125000000000 : ℝ)
  | 16 => (-364098855957 / 1000000000000 : ℝ)
  | 17 => (-184166657071 / 500000000000 : ℝ)
  | 18 => (-372606957793 / 1000000000000 : ℝ)
  | 19 => (-188460041903 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch068Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1360 : ℝ) + (j.val : ℝ)) / 1600)
      (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch068Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch068Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1360 : ℝ) + (j.val : ℝ)) / 1600)
    (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch068Neg65WeightLower j.val) (hpThetaShiftTwoBatch068Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch068Neg65WeightLower, hpThetaShiftTwoBatch068Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch068Neg65_integral_bounds :
    (-403603977 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-38813461 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch068Lower hpThetaJensenCellsBatch068Upper
    hpThetaShiftTwoBatch068Neg65WeightLower hpThetaShiftTwoBatch068Neg65WeightUpper hpThetaJensenCellsBatch068_bounds hpThetaShiftTwoBatch068Neg65_weight_bounds
  have hl : (-403603977 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch068Lower j * hpThetaShiftTwoBatch068Neg65WeightLower j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftTwoBatch068Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftTwoBatch068Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch068Lower j * hpThetaShiftTwoBatch068Neg65WeightUpper j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftTwoBatch068Neg65WeightUpper j) / 1600) ≤ (-38813461 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftTwoBatch068Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1360 : ℝ) / 1600 = 68 / 80 by norm_num,
    show ((1360 : ℝ) + 20) / 1600 = (68 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch068Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (5489885607 / 500000000000 : ℝ)
  | 1 => (2132251187 / 200000000000 : ℝ)
  | 2 => (10336989599 / 1000000000000 : ℝ)
  | 3 => (5003456547 / 500000000000 : ℝ)
  | 4 => (1934193373 / 200000000000 : ℝ)
  | 5 => (4664545457 / 500000000000 : ℝ)
  | 6 => (4490612397 / 500000000000 : ℝ)
  | 7 => (1078413451 / 125000000000 : ℝ)
  | 8 => (826727801 / 100000000000 : ℝ)
  | 9 => (1580214839 / 200000000000 : ℝ)
  | 10 => (470539619 / 62500000000 : ℝ)
  | 11 => (446868401 / 62500000000 : ℝ)
  | 12 => (1691198137 / 250000000000 : ℝ)
  | 13 => (6373264651 / 1000000000000 : ℝ)
  | 14 => (5975246609 / 1000000000000 : ℝ)
  | 15 => (1392668459 / 250000000000 : ℝ)
  | 16 => (5159481271 / 1000000000000 : ℝ)
  | 17 => (2370801689 / 500000000000 : ℝ)
  | 18 => (67452721 / 15625000000 : ℝ)
  | 19 => (3885527071 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch068Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (11292594111 / 1000000000000 : ℝ)
  | 1 => (2195954243 / 200000000000 : ℝ)
  | 2 => (41645531 / 3906250000 : ℝ)
  | 3 => (12921237 / 1250000000 : ℝ)
  | 4 => (2001382619 / 200000000000 : ℝ)
  | 5 => (4835483433 / 500000000000 : ℝ)
  | 6 => (1865818183 / 200000000000 : ℝ)
  | 7 => (1796244959 / 200000000000 : ℝ)
  | 8 => (8627307609 / 1000000000000 : ℝ)
  | 9 => (8267278011 / 1000000000000 : ℝ)
  | 10 => (1975268549 / 250000000000 : ℝ)
  | 11 => (1505726781 / 200000000000 : ℝ)
  | 12 => (7149894417 / 1000000000000 : ℝ)
  | 13 => (6764792549 / 1000000000000 : ℝ)
  | 14 => (1593316163 / 250000000000 : ℝ)
  | 15 => (597524661 / 100000000000 : ℝ)
  | 16 => (5570673837 / 1000000000000 : ℝ)
  | 17 => (644935159 / 125000000000 : ℝ)
  | 18 => (4741603379 / 1000000000000 : ℝ)
  | 19 => (863394829 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch068Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1360 : ℝ) + (j.val : ℝ)) / 1600)
      (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch068Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch068Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1360 : ℝ) + (j.val : ℝ)) / 1600)
    (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch068Neg45WeightLower j.val) (hpThetaShiftTwoBatch068Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch068Neg45WeightLower, hpThetaShiftTwoBatch068Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch068Neg45_integral_bounds :
    (9070809 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (9757131 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch068Lower hpThetaJensenCellsBatch068Upper
    hpThetaShiftTwoBatch068Neg45WeightLower hpThetaShiftTwoBatch068Neg45WeightUpper hpThetaJensenCellsBatch068_bounds hpThetaShiftTwoBatch068Neg45_weight_bounds
  have hl : (9070809 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch068Lower j * hpThetaShiftTwoBatch068Neg45WeightLower j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftTwoBatch068Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftTwoBatch068Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch068Lower j * hpThetaShiftTwoBatch068Neg45WeightUpper j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftTwoBatch068Neg45WeightUpper j) / 1600) ≤ (9757131 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftTwoBatch068Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1360 : ℝ) / 1600 = 68 / 80 by norm_num,
    show ((1360 : ℝ) + 20) / 1600 = (68 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch068Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (127200131 / 12500000000 : ℝ)
  | 1 => (2061066889 / 200000000000 : ℝ)
  | 2 => (10435375909 / 1000000000000 : ℝ)
  | 3 => (10566135511 / 1000000000000 : ℝ)
  | 4 => (10697613863 / 1000000000000 : ℝ)
  | 5 => (338431611 / 31250000000 : ℝ)
  | 6 => (5481364569 / 500000000000 : ℝ)
  | 7 => (2219273431 / 200000000000 : ℝ)
  | 8 => (1123072611 / 100000000000 : ℝ)
  | 9 => (2273161297 / 200000000000 : ℝ)
  | 10 => (5750804367 / 500000000000 : ℝ)
  | 11 => (11638133281 / 1000000000000 : ℝ)
  | 12 => (5887690263 / 500000000000 : ℝ)
  | 13 => (11913350839 / 1000000000000 : ℝ)
  | 14 => (6026022281 / 500000000000 : ℝ)
  | 15 => (1219146201 / 100000000000 : ℝ)
  | 16 => (12331603467 / 1000000000000 : ℝ)
  | 17 => (12472469189 / 1000000000000 : ℝ)
  | 18 => (12614059403 / 1000000000000 : ℝ)
  | 19 => (2551274861 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch068Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5152667223 / 500000000000 : ℝ)
  | 1 => (1043537591 / 100000000000 : ℝ)
  | 2 => (1320766939 / 125000000000 : ℝ)
  | 3 => (1337201733 / 125000000000 : ℝ)
  | 4 => (10829811553 / 1000000000000 : ℝ)
  | 5 => (10962729139 / 1000000000000 : ℝ)
  | 6 => (2774091789 / 250000000000 : ℝ)
  | 7 => (11230726111 / 1000000000000 : ℝ)
  | 8 => (5682903243 / 500000000000 : ℝ)
  | 9 => (2300321747 / 200000000000 : ℝ)
  | 10 => (5819066641 / 500000000000 : ℝ)
  | 11 => (11775380527 / 1000000000000 : ℝ)
  | 12 => (297833771 / 25000000000 : ℝ)
  | 13 => (12052044563 / 1000000000000 : ℝ)
  | 14 => (12191462011 / 1000000000000 : ℝ)
  | 15 => (3082900867 / 250000000000 : ℝ)
  | 16 => (1247246919 / 100000000000 : ℝ)
  | 17 => (3153514851 / 250000000000 : ℝ)
  | 18 => (6378187153 / 500000000000 : ℝ)
  | 19 => (806213379 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch068Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1360 : ℝ) + (j.val : ℝ)) / 1600)
      (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch068Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch068Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1360 : ℝ) + (j.val : ℝ)) / 1600)
    (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch068Neg25WeightLower j.val) (hpThetaShiftTwoBatch068Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch068Neg25WeightLower, hpThetaShiftTwoBatch068Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch068Neg25_integral_bounds :
    (65687 / 5000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (2732533 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch068Lower hpThetaJensenCellsBatch068Upper
    hpThetaShiftTwoBatch068Neg25WeightLower hpThetaShiftTwoBatch068Neg25WeightUpper hpThetaJensenCellsBatch068_bounds hpThetaShiftTwoBatch068Neg25_weight_bounds
  have hl : (65687 / 5000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch068Lower j * hpThetaShiftTwoBatch068Neg25WeightLower j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftTwoBatch068Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftTwoBatch068Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch068Lower j * hpThetaShiftTwoBatch068Neg25WeightUpper j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftTwoBatch068Neg25WeightUpper j) / 1600) ≤ (2732533 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftTwoBatch068Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1360 : ℝ) / 1600 = 68 / 80 by norm_num,
    show ((1360 : ℝ) + 20) / 1600 = (68 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch068Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch068Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch068Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch068Neg25_integral_bounds
end HodgeProofHP
