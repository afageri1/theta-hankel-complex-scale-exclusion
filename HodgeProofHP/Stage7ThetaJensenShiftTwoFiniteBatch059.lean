/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch059

/-! Exact signed weight and batch integral certificates, batch 59 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch059Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-196823708581 / 500000000000 : ℝ)
  | 1 => (-39842539901 / 100000000000 : ℝ)
  | 2 => (-201625765879 / 500000000000 : ℝ)
  | 3 => (-81625244343 / 200000000000 : ℝ)
  | 4 => (-82609975611 / 200000000000 : ℝ)
  | 5 => (-104505728207 / 250000000000 : ℝ)
  | 6 => (-423045740977 / 1000000000000 : ℝ)
  | 7 => (-428118780359 / 1000000000000 : ℝ)
  | 8 => (-433242451761 / 1000000000000 : ℝ)
  | 9 => (-438417178911 / 1000000000000 : ℝ)
  | 10 => (-55455423563 / 125000000000 : ℝ)
  | 11 => (-112230377553 / 250000000000 : ℝ)
  | 12 => (-221802723 / 488281250 : ℝ)
  | 13 => (-459635223663 / 1000000000000 : ℝ)
  | 14 => (-116267922451 / 250000000000 : ℝ)
  | 15 => (-470561816891 / 1000000000000 : ℝ)
  | 16 => (-476106049751 / 1000000000000 : ℝ)
  | 17 => (-481704836299 / 1000000000000 : ℝ)
  | 18 => (-487358627549 / 1000000000000 : ℝ)
  | 19 => (-246533938817 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch059Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-388917182749 / 1000000000000 : ℝ)
  | 1 => (-393647417161 / 1000000000000 : ℝ)
  | 2 => (-398425399009 / 1000000000000 : ℝ)
  | 3 => (-403251531757 / 1000000000000 : ℝ)
  | 4 => (-204063110857 / 500000000000 : ℝ)
  | 5 => (-206524939027 / 500000000000 : ℝ)
  | 6 => (-418022912827 / 1000000000000 : ℝ)
  | 7 => (-26440358811 / 62500000000 : ℝ)
  | 8 => (-214059390179 / 500000000000 : ℝ)
  | 9 => (-5415530647 / 12500000000 : ℝ)
  | 10 => (-43841717891 / 100000000000 : ℝ)
  | 11 => (-443643388503 / 1000000000000 : ℝ)
  | 12 => (-448921510211 / 1000000000000 : ℝ)
  | 13 => (-454251976703 / 1000000000000 : ℝ)
  | 14 => (-229817611831 / 500000000000 : ℝ)
  | 15 => (-465071689803 / 1000000000000 : ℝ)
  | 16 => (-47056181689 / 100000000000 : ℝ)
  | 17 => (-1904424199 / 4000000000 : ℝ)
  | 18 => (-240852418149 / 500000000000 : ℝ)
  | 19 => (-121839656887 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch059Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1180 : ℝ) + (j.val : ℝ)) / 1600)
      (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch059Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch059Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1180 : ℝ) + (j.val : ℝ)) / 1600)
    (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch059Neg100WeightLower j.val) (hpThetaShiftTwoBatch059Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch059Neg100WeightLower, hpThetaShiftTwoBatch059Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch059Neg100_integral_bounds :
    (-10215155459 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-4932672093 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch059Lower hpThetaJensenCellsBatch059Upper
    hpThetaShiftTwoBatch059Neg100WeightLower hpThetaShiftTwoBatch059Neg100WeightUpper hpThetaJensenCellsBatch059_bounds hpThetaShiftTwoBatch059Neg100_weight_bounds
  have hl : (-10215155459 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch059Lower j * hpThetaShiftTwoBatch059Neg100WeightLower j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftTwoBatch059Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftTwoBatch059Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch059Lower j * hpThetaShiftTwoBatch059Neg100WeightUpper j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftTwoBatch059Neg100WeightUpper j) / 1600) ≤ (-4932672093 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftTwoBatch059Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1180 : ℝ) / 1600 = 59 / 80 by norm_num,
    show ((1180 : ℝ) + 20) / 1600 = (59 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch059Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4629381431 / 500000000000 : ℝ)
  | 1 => (-9701968919 / 1000000000000 : ℝ)
  | 2 => (-2030425963 / 200000000000 : ℝ)
  | 3 => (-10609320207 / 1000000000000 : ℝ)
  | 4 => (-11073615363 / 1000000000000 : ℝ)
  | 5 => (-5772545583 / 500000000000 : ℝ)
  | 6 => (-12023824121 / 1000000000000 : ℝ)
  | 7 => (-12509891353 / 1000000000000 : ℝ)
  | 8 => (-2600674123 / 200000000000 : ℝ)
  | 9 => (-2700868059 / 200000000000 : ℝ)
  | 10 => (-1401287941 / 100000000000 : ℝ)
  | 11 => (-14529067623 / 1000000000000 : ℝ)
  | 12 => (-3763246309 / 250000000000 : ℝ)
  | 13 => (-38961783 / 2500000000 : ℝ)
  | 14 => (-16124333117 / 1000000000000 : ℝ)
  | 15 => (-16671927247 / 1000000000000 : ℝ)
  | 16 => (-4306894627 / 250000000000 : ℝ)
  | 17 => (-8895685241 / 500000000000 : ℝ)
  | 18 => (-18363387419 / 1000000000000 : ℝ)
  | 19 => (-3788742849 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch059Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1764487519 / 200000000000 : ℝ)
  | 1 => (-9258762861 / 1000000000000 : ℝ)
  | 2 => (-4850984459 / 500000000000 : ℝ)
  | 3 => (-5076064907 / 500000000000 : ℝ)
  | 4 => (-5304660103 / 500000000000 : ℝ)
  | 5 => (-5536807681 / 500000000000 : ℝ)
  | 6 => (-2309018233 / 200000000000 : ℝ)
  | 7 => (-300595603 / 25000000000 : ℝ)
  | 8 => (-1563736419 / 125000000000 : ℝ)
  | 9 => (-6501685307 / 500000000000 : ℝ)
  | 10 => (-6752170147 / 500000000000 : ℝ)
  | 11 => (-14012879409 / 1000000000000 : ℝ)
  | 12 => (-7264533811 / 500000000000 : ℝ)
  | 13 => (-3010597047 / 200000000000 : ℝ)
  | 14 => (-15584713199 / 1000000000000 : ℝ)
  | 15 => (-4031083279 / 250000000000 : ℝ)
  | 16 => (-8335963623 / 500000000000 : ℝ)
  | 17 => (-17227578507 / 1000000000000 : ℝ)
  | 18 => (-17791370481 / 1000000000000 : ℝ)
  | 19 => (-9181693709 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch059Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1180 : ℝ) + (j.val : ℝ)) / 1600)
      (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch059Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch059Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1180 : ℝ) + (j.val : ℝ)) / 1600)
    (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch059Neg65WeightLower j.val) (hpThetaShiftTwoBatch059Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch059Neg65WeightLower, hpThetaShiftTwoBatch059Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch059Neg65_integral_bounds :
    (-79283913 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-298510029 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch059Lower hpThetaJensenCellsBatch059Upper
    hpThetaShiftTwoBatch059Neg65WeightLower hpThetaShiftTwoBatch059Neg65WeightUpper hpThetaJensenCellsBatch059_bounds hpThetaShiftTwoBatch059Neg65_weight_bounds
  have hl : (-79283913 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch059Lower j * hpThetaShiftTwoBatch059Neg65WeightLower j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftTwoBatch059Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftTwoBatch059Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch059Lower j * hpThetaShiftTwoBatch059Neg65WeightUpper j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftTwoBatch059Neg65WeightUpper j) / 1600) ≤ (-298510029 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftTwoBatch059Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1180 : ℝ) / 1600 = 59 / 80 by norm_num,
    show ((1180 : ℝ) + 20) / 1600 = (59 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch059Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (8331102697 / 500000000000 : ℝ)
  | 1 => (16755173419 / 1000000000000 : ℝ)
  | 2 => (16847898991 / 1000000000000 : ℝ)
  | 3 => (1694037091 / 100000000000 : ℝ)
  | 4 => (8516288921 / 500000000000 : ℝ)
  | 5 => (8562254159 / 500000000000 : ℝ)
  | 6 => (17216150733 / 1000000000000 : ℝ)
  | 7 => (3461498669 / 200000000000 : ℝ)
  | 8 => (1087407767 / 62500000000 : ℝ)
  | 9 => (3497846299 / 200000000000 : ℝ)
  | 10 => (17579602853 / 1000000000000 : ℝ)
  | 11 => (8834813023 / 500000000000 : ℝ)
  | 12 => (4439822157 / 250000000000 : ℝ)
  | 13 => (17848578013 / 1000000000000 : ℝ)
  | 14 => (17937481467 / 1000000000000 : ℝ)
  | 15 => (18025986113 / 1000000000000 : ℝ)
  | 16 => (9057039463 / 500000000000 : ℝ)
  | 17 => (4550436683 / 250000000000 : ℝ)
  | 18 => (1828897621 / 100000000000 : ℝ)
  | 19 => (9187876943 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch059Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (837758671 / 50000000000 : ℝ)
  | 1 => (1052993687 / 62500000000 : ℝ)
  | 2 => (16940370911 / 1000000000000 : ℝ)
  | 3 => (17032577843 / 1000000000000 : ℝ)
  | 4 => (17124508319 / 1000000000000 : ℝ)
  | 5 => (8608075367 / 500000000000 : ℝ)
  | 6 => (8653746673 / 500000000000 : ℝ)
  | 7 => (17398524273 / 1000000000000 : ℝ)
  | 8 => (2186153937 / 125000000000 : ℝ)
  | 9 => (8789801427 / 500000000000 : ℝ)
  | 10 => (17669626047 / 1000000000000 : ℝ)
  | 11 => (17759288629 / 1000000000000 : ℝ)
  | 12 => (8924289007 / 500000000000 : ℝ)
  | 13 => (4484370367 / 250000000000 : ℝ)
  | 14 => (9012993057 / 500000000000 : ℝ)
  | 15 => (18114078927 / 1000000000000 : ℝ)
  | 16 => (18201746733 / 1000000000000 : ℝ)
  | 17 => (18288976211 / 1000000000000 : ℝ)
  | 18 => (18375753887 / 1000000000000 : ℝ)
  | 19 => (923103307 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch059Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1180 : ℝ) + (j.val : ℝ)) / 1600)
      (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch059Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch059Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1180 : ℝ) + (j.val : ℝ)) / 1600)
    (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch059Neg45WeightLower j.val) (hpThetaShiftTwoBatch059Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch059Neg45WeightLower, hpThetaShiftTwoBatch059Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch059Neg45_integral_bounds :
    (397286131 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (40861499 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch059Lower hpThetaJensenCellsBatch059Upper
    hpThetaShiftTwoBatch059Neg45WeightLower hpThetaShiftTwoBatch059Neg45WeightUpper hpThetaJensenCellsBatch059_bounds hpThetaShiftTwoBatch059Neg45_weight_bounds
  have hl : (397286131 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch059Lower j * hpThetaShiftTwoBatch059Neg45WeightLower j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftTwoBatch059Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftTwoBatch059Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch059Lower j * hpThetaShiftTwoBatch059Neg45WeightUpper j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftTwoBatch059Neg45WeightUpper j) / 1600) ≤ (40861499 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftTwoBatch059Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1180 : ℝ) / 1600 = 59 / 80 by norm_num,
    show ((1180 : ℝ) + 20) / 1600 = (59 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch059Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2832982897 / 1000000000000 : ℝ)
  | 1 => (-350850287 / 125000000000 : ℝ)
  | 2 => (-2780235183 / 1000000000000 : ℝ)
  | 3 => (-1376639671 / 500000000000 : ℝ)
  | 4 => (-1362966279 / 500000000000 : ℝ)
  | 5 => (-2698192609 / 1000000000000 : ℝ)
  | 6 => (-1335028637 / 500000000000 : ℝ)
  | 7 => (-2641524331 / 1000000000000 : ℝ)
  | 8 => (-2612591553 / 1000000000000 : ℝ)
  | 9 => (-2583256713 / 1000000000000 : ℝ)
  | 10 => (-1276758791 / 500000000000 : ℝ)
  | 11 => (-2523371931 / 1000000000000 : ℝ)
  | 12 => (-99712701 / 40000000000 : ℝ)
  | 13 => (-615463033 / 250000000000 : ℝ)
  | 14 => (-2430473517 / 1000000000000 : ℝ)
  | 15 => (-1199339721 / 500000000000 : ℝ)
  | 16 => (-236646767 / 100000000000 : ℝ)
  | 17 => (-1166917981 / 500000000000 : ℝ)
  | 18 => (-2300782077 / 1000000000000 : ℝ)
  | 19 => (-90692151 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch059Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-561360459 / 200000000000 : ℝ)
  | 1 => (-1390117591 / 500000000000 : ℝ)
  | 2 => (-2753279341 / 1000000000000 : ℝ)
  | 3 => (-2725932557 / 1000000000000 : ℝ)
  | 4 => (-84318519 / 31250000000 : ℝ)
  | 5 => (-2670057273 / 1000000000000 : ℝ)
  | 6 => (-264152433 / 100000000000 : ℝ)
  | 7 => (-40821743 / 15625000000 : ℝ)
  | 8 => (-322907089 / 125000000000 : ℝ)
  | 9 => (-2553517581 / 1000000000000 : ℝ)
  | 10 => (-252337193 / 100000000000 : ℝ)
  | 11 => (-623204381 / 250000000000 : ℝ)
  | 12 => (-2461852131 / 1000000000000 : ℝ)
  | 13 => (-607618379 / 250000000000 : ℝ)
  | 14 => (-2398679441 / 1000000000000 : ℝ)
  | 15 => (-2366467669 / 1000000000000 : ℝ)
  | 16 => (-2333835961 / 1000000000000 : ℝ)
  | 17 => (-575195519 / 250000000000 : ℝ)
  | 18 => (-1133651887 / 500000000000 : ℝ)
  | 19 => (-558349703 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch059Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1180 : ℝ) + (j.val : ℝ)) / 1600)
      (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch059Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch059Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1180 : ℝ) + (j.val : ℝ)) / 1600)
    (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch059Neg25WeightLower j.val) (hpThetaShiftTwoBatch059Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch059Neg25WeightLower, hpThetaShiftTwoBatch059Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch059Neg25_integral_bounds :
    (-11977379 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-28925361 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch059Lower hpThetaJensenCellsBatch059Upper
    hpThetaShiftTwoBatch059Neg25WeightLower hpThetaShiftTwoBatch059Neg25WeightUpper hpThetaJensenCellsBatch059_bounds hpThetaShiftTwoBatch059Neg25_weight_bounds
  have hl : (-11977379 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch059Lower j * hpThetaShiftTwoBatch059Neg25WeightLower j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftTwoBatch059Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftTwoBatch059Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch059Lower j * hpThetaShiftTwoBatch059Neg25WeightUpper j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftTwoBatch059Neg25WeightUpper j) / 1600) ≤ (-28925361 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftTwoBatch059Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1180 : ℝ) / 1600 = 59 / 80 by norm_num,
    show ((1180 : ℝ) + 20) / 1600 = (59 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch059Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch059Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch059Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch059Neg25_integral_bounds
end HodgeProofHP
