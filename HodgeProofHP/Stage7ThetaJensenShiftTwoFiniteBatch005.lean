/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch005

/-! Exact signed weight and batch integral certificates, batch 5 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch005Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1126681 / 1000000000000 : ℝ)
  | 1 => (584743 / 500000000000 : ℝ)
  | 2 => (1213407 / 1000000000000 : ℝ)
  | 3 => (1258457 / 1000000000000 : ℝ)
  | 4 => (26093 / 20000000000 : ℝ)
  | 5 => (169 / 125000000 : ℝ)
  | 6 => (1400519 / 1000000000000 : ℝ)
  | 7 => (1450221 / 1000000000000 : ℝ)
  | 8 => (1501119 / 1000000000000 : ℝ)
  | 9 => (194153 / 125000000000 : ℝ)
  | 10 => (32131 / 20000000000 : ℝ)
  | 11 => (1661109 / 1000000000000 : ℝ)
  | 12 => (1716911 / 1000000000000 : ℝ)
  | 13 => (177397 / 100000000000 : ℝ)
  | 14 => (229037 / 125000000000 : ℝ)
  | 15 => (18919 / 10000000000 : ℝ)
  | 16 => (1952793 / 1000000000000 : ℝ)
  | 17 => (1007493 / 500000000000 : ℝ)
  | 18 => (2078489 / 1000000000000 : ℝ)
  | 19 => (2143311 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch005Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1169487 / 1000000000000 : ℝ)
  | 1 => (37919 / 31250000000 : ℝ)
  | 2 => (629229 / 500000000000 : ℝ)
  | 3 => (1304651 / 1000000000000 : ℝ)
  | 4 => (1352001 / 1000000000000 : ℝ)
  | 5 => (35013 / 25000000000 : ℝ)
  | 6 => (725111 / 500000000000 : ℝ)
  | 7 => (4691 / 3125000000 : ℝ)
  | 8 => (62129 / 40000000000 : ℝ)
  | 9 => (1606551 / 1000000000000 : ℝ)
  | 10 => (166111 / 100000000000 : ℝ)
  | 11 => (107307 / 62500000000 : ℝ)
  | 12 => (1773971 / 1000000000000 : ℝ)
  | 13 => (1832297 / 1000000000000 : ℝ)
  | 14 => (1891901 / 1000000000000 : ℝ)
  | 15 => (976397 / 500000000000 : ℝ)
  | 16 => (2014987 / 1000000000000 : ℝ)
  | 17 => (207849 / 100000000000 : ℝ)
  | 18 => (133957 / 62500000000 : ℝ)
  | 19 => (276183 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch005Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((100 : ℝ) + (j.val : ℝ)) / 1600)
      (((100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch005Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch005Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((100 : ℝ) + (j.val : ℝ)) / 1600)
    (((100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch005Neg100WeightLower j.val) (hpThetaShiftTwoBatch005Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch005Neg100WeightLower, hpThetaShiftTwoBatch005Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch005Neg100_integral_bounds :
    (33995121 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (35528937 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch005Lower hpThetaJensenCellsBatch005Upper
    hpThetaShiftTwoBatch005Neg100WeightLower hpThetaShiftTwoBatch005Neg100WeightUpper hpThetaJensenCellsBatch005_bounds hpThetaShiftTwoBatch005Neg100_weight_bounds
  have hl : (33995121 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch005Lower j * hpThetaShiftTwoBatch005Neg100WeightLower j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftTwoBatch005Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftTwoBatch005Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch005Lower j * hpThetaShiftTwoBatch005Neg100WeightUpper j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftTwoBatch005Neg100WeightUpper j) / 1600) ≤ (35528937 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftTwoBatch005Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (100 : ℝ) / 1600 = 5 / 80 by norm_num,
    show ((100 : ℝ) + 20) / 1600 = (5 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch005Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (147057 / 125000000000 : ℝ)
  | 1 => (1222273 / 1000000000000 : ℝ)
  | 2 => (634677 / 500000000000 : ℝ)
  | 3 => (1317719 / 1000000000000 : ℝ)
  | 4 => (341847 / 250000000000 : ℝ)
  | 5 => (1418379 / 1000000000000 : ℝ)
  | 6 => (1470713 / 1000000000000 : ℝ)
  | 7 => (190551 / 125000000000 : ℝ)
  | 8 => (1579483 / 1000000000000 : ℝ)
  | 9 => (1635959 / 1000000000000 : ℝ)
  | 10 => (846927 / 500000000000 : ℝ)
  | 11 => (1753187 / 1000000000000 : ℝ)
  | 12 => (1813977 / 1000000000000 : ℝ)
  | 13 => (1876243 / 1000000000000 : ℝ)
  | 14 => (485001 / 250000000000 : ℝ)
  | 15 => (2005279 / 1000000000000 : ℝ)
  | 16 => (1036043 / 500000000000 : ℝ)
  | 17 => (2140443 / 1000000000000 : ℝ)
  | 18 => (221037 / 100000000000 : ℝ)
  | 19 => (456377 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch005Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (611137 / 500000000000 : ℝ)
  | 1 => (253871 / 200000000000 : ℝ)
  | 2 => (32943 / 25000000000 : ℝ)
  | 3 => (1367389 / 1000000000000 : ℝ)
  | 4 => (70919 / 50000000000 : ℝ)
  | 5 => (735357 / 500000000000 : ℝ)
  | 6 => (1524409 / 1000000000000 : ℝ)
  | 7 => (394871 / 250000000000 : ℝ)
  | 8 => (40899 / 25000000000 : ℝ)
  | 9 => (338771 / 200000000000 : ℝ)
  | 10 => (438297 / 250000000000 : ℝ)
  | 11 => (906989 / 500000000000 : ℝ)
  | 12 => (469061 / 250000000000 : ℝ)
  | 13 => (388001 / 200000000000 : ℝ)
  | 14 => (12533 / 6250000000 : ℝ)
  | 15 => (2072087 / 1000000000000 : ℝ)
  | 16 => (535111 / 250000000000 : ℝ)
  | 17 => (2210371 / 1000000000000 : ℝ)
  | 18 => (1140943 / 500000000000 : ℝ)
  | 19 => (1177503 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch005Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((100 : ℝ) + (j.val : ℝ)) / 1600)
      (((100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch005Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch005Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((100 : ℝ) + (j.val : ℝ)) / 1600)
    (((100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch005Neg65WeightLower j.val) (hpThetaShiftTwoBatch005Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch005Neg65WeightLower, hpThetaShiftTwoBatch005Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch005Neg65_integral_bounds :
    (35871609 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (293193 / 7812500000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch005Lower hpThetaJensenCellsBatch005Upper
    hpThetaShiftTwoBatch005Neg65WeightLower hpThetaShiftTwoBatch005Neg65WeightUpper hpThetaJensenCellsBatch005_bounds hpThetaShiftTwoBatch005Neg65_weight_bounds
  have hl : (35871609 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch005Lower j * hpThetaShiftTwoBatch005Neg65WeightLower j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftTwoBatch005Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftTwoBatch005Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch005Lower j * hpThetaShiftTwoBatch005Neg65WeightUpper j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftTwoBatch005Neg65WeightUpper j) / 1600) ≤ (293193 / 7812500000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftTwoBatch005Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (100 : ℝ) / 1600 = 5 / 80 by norm_num,
    show ((100 : ℝ) + 20) / 1600 = (5 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch005Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1205349 / 1000000000000 : ℝ)
  | 1 => (313231 / 250000000000 : ℝ)
  | 2 => (1301851 / 1000000000000 : ℝ)
  | 3 => (1352153 / 1000000000000 : ℝ)
  | 4 => (701927 / 500000000000 : ℝ)
  | 5 => (58279 / 40000000000 : ℝ)
  | 6 => (75577 / 50000000000 : ℝ)
  | 7 => (391893 / 250000000000 : ℝ)
  | 8 => (325019 / 200000000000 : ℝ)
  | 9 => (1684131 / 1000000000000 : ℝ)
  | 10 => (27261 / 15625000000 : ℝ)
  | 11 => (1806837 / 1000000000000 : ℝ)
  | 12 => (935277 / 500000000000 : ℝ)
  | 13 => (1935877 / 1000000000000 : ℝ)
  | 14 => (2002831 / 1000000000000 : ℝ)
  | 15 => (1035719 / 500000000000 : ℝ)
  | 16 => (1070861 / 500000000000 : ℝ)
  | 17 => (1106853 / 500000000000 : ℝ)
  | 18 => (1143707 / 500000000000 : ℝ)
  | 19 => (2362869 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch005Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (50117 / 40000000000 : ℝ)
  | 1 => (325463 / 250000000000 : ℝ)
  | 2 => (676077 / 500000000000 : ℝ)
  | 3 => (280771 / 200000000000 : ℝ)
  | 4 => (91061 / 62500000000 : ℝ)
  | 5 => (1511541 / 1000000000000 : ℝ)
  | 6 => (1567573 / 1000000000000 : ℝ)
  | 7 => (203137 / 125000000000 : ℝ)
  | 8 => (421033 / 250000000000 : ℝ)
  | 9 => (348941 / 200000000000 : ℝ)
  | 10 => (903419 / 500000000000 : ℝ)
  | 11 => (374111 / 200000000000 : ℝ)
  | 12 => (967939 / 500000000000 : ℝ)
  | 13 => (125177 / 62500000000 : ℝ)
  | 14 => (2071439 / 1000000000000 : ℝ)
  | 15 => (2141723 / 1000000000000 : ℝ)
  | 16 => (2213707 / 1000000000000 : ℝ)
  | 17 => (457483 / 200000000000 : ℝ)
  | 18 => (236287 / 100000000000 : ℝ)
  | 19 => (2440097 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch005Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((100 : ℝ) + (j.val : ℝ)) / 1600)
      (((100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch005Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch005Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((100 : ℝ) + (j.val : ℝ)) / 1600)
    (((100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch005Neg45WeightLower j.val) (hpThetaShiftTwoBatch005Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch005Neg45WeightLower, hpThetaShiftTwoBatch005Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch005Neg45_integral_bounds :
    (36965117 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (38694471 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch005Lower hpThetaJensenCellsBatch005Upper
    hpThetaShiftTwoBatch005Neg45WeightLower hpThetaShiftTwoBatch005Neg45WeightUpper hpThetaJensenCellsBatch005_bounds hpThetaShiftTwoBatch005Neg45_weight_bounds
  have hl : (36965117 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch005Lower j * hpThetaShiftTwoBatch005Neg45WeightLower j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftTwoBatch005Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftTwoBatch005Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch005Lower j * hpThetaShiftTwoBatch005Neg45WeightUpper j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftTwoBatch005Neg45WeightUpper j) / 1600) ≤ (38694471 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftTwoBatch005Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (100 : ℝ) / 1600 = 5 / 80 by norm_num,
    show ((100 : ℝ) + 20) / 1600 = (5 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch005Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (308643 / 250000000000 : ℝ)
  | 1 => (320983 / 250000000000 : ℝ)
  | 2 => (667367 / 500000000000 : ℝ)
  | 3 => (277401 / 200000000000 : ℝ)
  | 4 => (144077 / 100000000000 : ℝ)
  | 5 => (187007 / 125000000000 : ℝ)
  | 6 => (1552891 / 1000000000000 : ℝ)
  | 7 => (805651 / 500000000000 : ℝ)
  | 8 => (334263 / 200000000000 : ℝ)
  | 9 => (866479 / 500000000000 : ℝ)
  | 10 => (1796259 / 1000000000000 : ℝ)
  | 11 => (372249 / 200000000000 : ℝ)
  | 12 => (240993 / 125000000000 : ℝ)
  | 13 => (62387 / 31250000000 : ℝ)
  | 14 => (1033297 / 500000000000 : ℝ)
  | 15 => (2138601 / 1000000000000 : ℝ)
  | 16 => (1106217 / 500000000000 : ℝ)
  | 17 => (2288121 / 1000000000000 : ℝ)
  | 18 => (2365691 / 1000000000000 : ℝ)
  | 19 => (2445173 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch005Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1283933 / 1000000000000 : ℝ)
  | 1 => (266947 / 200000000000 : ℝ)
  | 2 => (693503 / 500000000000 : ℝ)
  | 3 => (1440771 / 1000000000000 : ℝ)
  | 4 => (1496057 / 1000000000000 : ℝ)
  | 5 => (388223 / 250000000000 : ℝ)
  | 6 => (1611303 / 1000000000000 : ℝ)
  | 7 => (417829 / 250000000000 : ℝ)
  | 8 => (1732959 / 1000000000000 : ℝ)
  | 9 => (89813 / 50000000000 : ℝ)
  | 10 => (930623 / 500000000000 : ℝ)
  | 11 => (385589 / 200000000000 : ℝ)
  | 12 => (399277 / 200000000000 : ℝ)
  | 13 => (413319 / 200000000000 : ℝ)
  | 14 => (1069301 / 500000000000 : ℝ)
  | 15 => (442487 / 200000000000 : ℝ)
  | 16 => (1144061 / 500000000000 : ℝ)
  | 17 => (591423 / 250000000000 : ℝ)
  | 18 => (1222587 / 500000000000 : ℝ)
  | 19 => (2526597 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch005Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((100 : ℝ) + (j.val : ℝ)) / 1600)
      (((100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch005Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch005Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((100 : ℝ) + (j.val : ℝ)) / 1600)
    (((100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch005Neg25WeightLower j.val) (hpThetaShiftTwoBatch005Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch005Neg25WeightLower, hpThetaShiftTwoBatch005Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch005Neg25_integral_bounds :
    (3807417 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (39877111 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch005Lower hpThetaJensenCellsBatch005Upper
    hpThetaShiftTwoBatch005Neg25WeightLower hpThetaShiftTwoBatch005Neg25WeightUpper hpThetaJensenCellsBatch005_bounds hpThetaShiftTwoBatch005Neg25_weight_bounds
  have hl : (3807417 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch005Lower j * hpThetaShiftTwoBatch005Neg25WeightLower j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftTwoBatch005Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftTwoBatch005Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch005Lower j * hpThetaShiftTwoBatch005Neg25WeightUpper j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftTwoBatch005Neg25WeightUpper j) / 1600) ≤ (39877111 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftTwoBatch005Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (100 : ℝ) / 1600 = 5 / 80 by norm_num,
    show ((100 : ℝ) + 20) / 1600 = (5 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch005Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch005Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch005Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch005Neg25_integral_bounds
end HodgeProofHP
