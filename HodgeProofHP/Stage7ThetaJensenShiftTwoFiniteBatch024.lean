/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch024

/-! Exact signed weight and batch integral certificates, batch 24 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch024Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-172855013 / 1000000000000 : ℝ)
  | 1 => (-174542509 / 1000000000000 : ℝ)
  | 2 => (-11013921 / 62500000000 : ℝ)
  | 3 => (-177895221 / 1000000000000 : ℝ)
  | 4 => (-44889871 / 250000000000 : ℝ)
  | 5 => (-90607519 / 500000000000 : ℝ)
  | 6 => (-182861389 / 1000000000000 : ℝ)
  | 7 => (-184498039 / 1000000000000 : ℝ)
  | 8 => (-186124479 / 1000000000000 : ℝ)
  | 9 => (-93870099 / 500000000000 : ℝ)
  | 10 => (-94672337 / 500000000000 : ℝ)
  | 11 => (-95468691 / 500000000000 : ℝ)
  | 12 => (-48129447 / 250000000000 : ℝ)
  | 13 => (-24260669 / 125000000000 : ℝ)
  | 14 => (-24454941 / 125000000000 : ℝ)
  | 15 => (-2464747 / 12500000000 : ℝ)
  | 16 => (-19870549 / 100000000000 : ℝ)
  | 17 => (-200216149 / 1000000000000 : ℝ)
  | 18 => (-50427791 / 250000000000 : ℝ)
  | 19 => (-203189953 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch024Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-85580357 / 500000000000 : ℝ)
  | 1 => (-43213753 / 250000000000 : ℝ)
  | 2 => (-43635627 / 250000000000 : ℝ)
  | 3 => (-35244547 / 200000000000 : ℝ)
  | 4 => (-8894761 / 50000000000 : ℝ)
  | 5 => (-179559483 / 1000000000000 : ℝ)
  | 6 => (-181215037 / 1000000000000 : ℝ)
  | 7 => (-45715347 / 250000000000 : ℝ)
  | 8 => (-92249019 / 500000000000 : ℝ)
  | 9 => (-93062239 / 500000000000 : ℝ)
  | 10 => (-187740197 / 1000000000000 : ℝ)
  | 11 => (-189344673 / 1000000000000 : ℝ)
  | 12 => (-190937381 / 1000000000000 : ℝ)
  | 13 => (-192517787 / 1000000000000 : ℝ)
  | 14 => (-194085351 / 1000000000000 : ℝ)
  | 15 => (-195639527 / 1000000000000 : ℝ)
  | 16 => (-197179759 / 1000000000000 : ℝ)
  | 17 => (-198705489 / 1000000000000 : ℝ)
  | 18 => (-50054037 / 250000000000 : ℝ)
  | 19 => (-201711163 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch024Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((480 : ℝ) + (j.val : ℝ)) / 1600)
      (((480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch024Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch024Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((480 : ℝ) + (j.val : ℝ)) / 1600)
    (((480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch024Neg100WeightLower j.val) (hpThetaShiftTwoBatch024Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch024Neg100WeightLower, hpThetaShiftTwoBatch024Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch024Neg100_integral_bounds :
    (-836270567 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-818331177 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch024Lower hpThetaJensenCellsBatch024Upper
    hpThetaShiftTwoBatch024Neg100WeightLower hpThetaShiftTwoBatch024Neg100WeightUpper hpThetaJensenCellsBatch024_bounds hpThetaShiftTwoBatch024Neg100_weight_bounds
  have hl : (-836270567 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch024Lower j * hpThetaShiftTwoBatch024Neg100WeightLower j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftTwoBatch024Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftTwoBatch024Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch024Lower j * hpThetaShiftTwoBatch024Neg100WeightUpper j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftTwoBatch024Neg100WeightUpper j) / 1600) ≤ (-818331177 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftTwoBatch024Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (480 : ℝ) / 1600 = 24 / 80 by norm_num,
    show ((480 : ℝ) + 20) / 1600 = (24 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch024Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3515311 / 50000000000 : ℝ)
  | 1 => (-72385731 / 1000000000000 : ℝ)
  | 2 => (-74484929 / 1000000000000 : ℝ)
  | 3 => (-4787737 / 62500000000 : ℝ)
  | 4 => (-15748459 / 200000000000 : ℝ)
  | 5 => (-80900407 / 1000000000000 : ℝ)
  | 6 => (-83078097 / 1000000000000 : ℝ)
  | 7 => (-85275329 / 1000000000000 : ℝ)
  | 8 => (-43746033 / 500000000000 : ℝ)
  | 9 => (-89728267 / 1000000000000 : ℝ)
  | 10 => (-45991943 / 500000000000 : ℝ)
  | 11 => (-23564719 / 250000000000 : ℝ)
  | 12 => (-96553187 / 1000000000000 : ℝ)
  | 13 => (-24716691 / 250000000000 : ℝ)
  | 14 => (-2023991 / 20000000000 : ℝ)
  | 15 => (-25887871 / 250000000000 : ℝ)
  | 16 => (-52961251 / 500000000000 : ℝ)
  | 17 => (-13539067 / 125000000000 : ℝ)
  | 18 => (-110721517 / 1000000000000 : ℝ)
  | 19 => (-113149369 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch024Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-68246417 / 1000000000000 : ℝ)
  | 1 => (-70306219 / 1000000000000 : ℝ)
  | 2 => (-7238573 / 100000000000 : ℝ)
  | 3 => (-1163827 / 15625000000 : ℝ)
  | 4 => (-76603791 / 1000000000000 : ℝ)
  | 5 => (-39371147 / 500000000000 : ℝ)
  | 6 => (-40450203 / 500000000000 : ℝ)
  | 7 => (-5192381 / 62500000000 : ℝ)
  | 8 => (-1332427 / 15625000000 : ℝ)
  | 9 => (-17498413 / 200000000000 : ℝ)
  | 10 => (-44864133 / 500000000000 : ℝ)
  | 11 => (-18396777 / 200000000000 : ℝ)
  | 12 => (-754071 / 8000000000 : ℝ)
  | 13 => (-48276593 / 500000000000 : ℝ)
  | 14 => (-98866763 / 1000000000000 : ℝ)
  | 15 => (-101199549 / 1000000000000 : ℝ)
  | 16 => (-103551483 / 1000000000000 : ℝ)
  | 17 => (-105922501 / 1000000000000 : ℝ)
  | 18 => (-21662507 / 200000000000 : ℝ)
  | 19 => (-27680379 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch024Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((480 : ℝ) + (j.val : ℝ)) / 1600)
      (((480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch024Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch024Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((480 : ℝ) + (j.val : ℝ)) / 1600)
    (((480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch024Neg65WeightLower j.val) (hpThetaShiftTwoBatch024Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch024Neg65WeightLower, hpThetaShiftTwoBatch024Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch024Neg65_integral_bounds :
    (-161576441 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-777665443 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch024Lower hpThetaJensenCellsBatch024Upper
    hpThetaShiftTwoBatch024Neg65WeightLower hpThetaShiftTwoBatch024Neg65WeightUpper hpThetaJensenCellsBatch024_bounds hpThetaShiftTwoBatch024Neg65_weight_bounds
  have hl : (-161576441 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch024Lower j * hpThetaShiftTwoBatch024Neg65WeightLower j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftTwoBatch024Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftTwoBatch024Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch024Lower j * hpThetaShiftTwoBatch024Neg65WeightUpper j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftTwoBatch024Neg65WeightUpper j) / 1600) ≤ (-777665443 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftTwoBatch024Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (480 : ℝ) / 1600 = 24 / 80 by norm_num,
    show ((480 : ℝ) + 20) / 1600 = (24 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch024Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (73278089 / 1000000000000 : ℝ)
  | 1 => (72203461 / 1000000000000 : ℝ)
  | 2 => (1777691 / 25000000000 : ℝ)
  | 3 => (69990491 / 1000000000000 : ℝ)
  | 4 => (17212969 / 250000000000 : ℝ)
  | 5 => (3384583 / 50000000000 : ℝ)
  | 6 => (66509707 / 1000000000000 : ℝ)
  | 7 => (16326471 / 250000000000 : ℝ)
  | 8 => (8010007 / 125000000000 : ℝ)
  | 9 => (62832091 / 1000000000000 : ℝ)
  | 10 => (60119 / 976562500 : ℝ)
  | 11 => (3013461 / 50000000000 : ℝ)
  | 12 => (14738513 / 250000000000 : ℝ)
  | 13 => (57616223 / 1000000000000 : ℝ)
  | 14 => (28127801 / 500000000000 : ℝ)
  | 15 => (54872063 / 1000000000000 : ℝ)
  | 16 => (13366369 / 250000000000 : ℝ)
  | 17 => (52035717 / 1000000000000 : ℝ)
  | 18 => (25291329 / 500000000000 : ℝ)
  | 19 => (191821 / 3906250000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch024Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (74331663 / 1000000000000 : ℝ)
  | 1 => (7327809 / 100000000000 : ℝ)
  | 2 => (36101731 / 500000000000 : ℝ)
  | 3 => (71107641 / 1000000000000 : ℝ)
  | 4 => (17497623 / 250000000000 : ℝ)
  | 5 => (68851877 / 1000000000000 : ℝ)
  | 6 => (67691661 / 1000000000000 : ℝ)
  | 7 => (16627427 / 250000000000 : ℝ)
  | 8 => (13061177 / 200000000000 : ℝ)
  | 9 => (64080057 / 1000000000000 : ℝ)
  | 10 => (15708023 / 250000000000 : ℝ)
  | 11 => (61561857 / 1000000000000 : ℝ)
  | 12 => (60269221 / 1000000000000 : ℝ)
  | 13 => (58954053 / 1000000000000 : ℝ)
  | 14 => (1800507 / 31250000000 : ℝ)
  | 15 => (56255603 / 1000000000000 : ℝ)
  | 16 => (26793 / 488281250 : ℝ)
  | 17 => (53465477 / 1000000000000 : ℝ)
  | 18 => (26017859 / 500000000000 : ℝ)
  | 19 => (50582659 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch024Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((480 : ℝ) + (j.val : ℝ)) / 1600)
      (((480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch024Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch024Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((480 : ℝ) + (j.val : ℝ)) / 1600)
    (((480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch024Neg45WeightLower j.val) (hpThetaShiftTwoBatch024Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch024Neg45WeightLower, hpThetaShiftTwoBatch024Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch024Neg45_integral_bounds :
    (543964101 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (281167259 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch024Lower hpThetaJensenCellsBatch024Upper
    hpThetaShiftTwoBatch024Neg45WeightLower hpThetaShiftTwoBatch024Neg45WeightUpper hpThetaJensenCellsBatch024_bounds hpThetaShiftTwoBatch024Neg45_weight_bounds
  have hl : (543964101 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch024Lower j * hpThetaShiftTwoBatch024Neg45WeightLower j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftTwoBatch024Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftTwoBatch024Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch024Lower j * hpThetaShiftTwoBatch024Neg45WeightUpper j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftTwoBatch024Neg45WeightUpper j) / 1600) ≤ (281167259 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftTwoBatch024Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (480 : ℝ) / 1600 = 24 / 80 by norm_num,
    show ((480 : ℝ) + 20) / 1600 = (24 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch024Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (144774693 / 500000000000 : ℝ)
  | 1 => (290632127 / 1000000000000 : ℝ)
  | 2 => (291707159 / 1000000000000 : ℝ)
  | 3 => (58554867 / 200000000000 : ℝ)
  | 4 => (73458377 / 250000000000 : ℝ)
  | 5 => (29488453 / 100000000000 : ℝ)
  | 6 => (73981813 / 250000000000 : ℝ)
  | 7 => (74240381 / 250000000000 : ℝ)
  | 8 => (297987197 / 1000000000000 : ℝ)
  | 9 => (7475103 / 25000000000 : ℝ)
  | 10 => (150006071 / 500000000000 : ℝ)
  | 11 => (75252777 / 250000000000 : ℝ)
  | 12 => (75500217 / 250000000000 : ℝ)
  | 13 => (302981267 / 1000000000000 : ℝ)
  | 14 => (303952149 / 1000000000000 : ℝ)
  | 15 => (152456681 / 500000000000 : ℝ)
  | 16 => (305864747 / 1000000000000 : ℝ)
  | 17 => (306806149 / 1000000000000 : ℝ)
  | 18 => (30773741 / 100000000000 : ℝ)
  | 19 => (77164593 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch024Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (4541127 / 15625000000 : ℝ)
  | 1 => (7292679 / 25000000000 : ℝ)
  | 2 => (4574599 / 15625000000 : ℝ)
  | 3 => (293833509 / 1000000000000 : ℝ)
  | 4 => (294884531 / 1000000000000 : ℝ)
  | 5 => (295927253 / 1000000000000 : ℝ)
  | 6 => (11878461 / 40000000000 : ℝ)
  | 7 => (148993599 / 500000000000 : ℝ)
  | 8 => (299004121 / 1000000000000 : ℝ)
  | 9 => (300012143 / 1000000000000 : ℝ)
  | 10 => (301011109 / 1000000000000 : ℝ)
  | 11 => (302000869 / 1000000000000 : ℝ)
  | 12 => (75745317 / 250000000000 : ℝ)
  | 13 => (6079043 / 20000000000 : ℝ)
  | 14 => (304913363 / 1000000000000 : ℝ)
  | 15 => (76466187 / 250000000000 : ℝ)
  | 16 => (6136123 / 20000000000 : ℝ)
  | 17 => (307737411 / 1000000000000 : ℝ)
  | 18 => (308658373 / 1000000000000 : ℝ)
  | 19 => (154784439 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch024Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((480 : ℝ) + (j.val : ℝ)) / 1600)
      (((480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch024Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch024Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((480 : ℝ) + (j.val : ℝ)) / 1600)
    (((480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch024Neg25WeightLower j.val) (hpThetaShiftTwoBatch024Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch024Neg25WeightLower, hpThetaShiftTwoBatch024Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch024Neg25_integral_bounds :
    (2625396723 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (1334498459 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch024Lower hpThetaJensenCellsBatch024Upper
    hpThetaShiftTwoBatch024Neg25WeightLower hpThetaShiftTwoBatch024Neg25WeightUpper hpThetaJensenCellsBatch024_bounds hpThetaShiftTwoBatch024Neg25_weight_bounds
  have hl : (2625396723 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch024Lower j * hpThetaShiftTwoBatch024Neg25WeightLower j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftTwoBatch024Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftTwoBatch024Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch024Lower j * hpThetaShiftTwoBatch024Neg25WeightUpper j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftTwoBatch024Neg25WeightUpper j) / 1600) ≤ (1334498459 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftTwoBatch024Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (480 : ℝ) / 1600 = 24 / 80 by norm_num,
    show ((480 : ℝ) + 20) / 1600 = (24 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch024Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch024Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch024Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch024Neg25_integral_bounds
end HodgeProofHP
