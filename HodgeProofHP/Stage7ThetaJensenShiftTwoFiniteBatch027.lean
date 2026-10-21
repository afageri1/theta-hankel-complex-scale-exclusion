/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch027

/-! Exact signed weight and batch integral certificates, batch 27 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch027Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-120872209 / 500000000000 : ℝ)
  | 1 => (-9677033 / 40000000000 : ℝ)
  | 2 => (-189109 / 781250000 : ℝ)
  | 3 => (-242144621 / 1000000000000 : ℝ)
  | 4 => (-242180243 / 1000000000000 : ℝ)
  | 5 => (-1210909 / 5000000000 : ℝ)
  | 6 => (-242165493 / 1000000000000 : ℝ)
  | 7 => (-24209947 / 100000000000 : ℝ)
  | 8 => (-241981271 / 1000000000000 : ℝ)
  | 9 => (-3778281 / 15625000000 : ℝ)
  | 10 => (-24158469 / 100000000000 : ℝ)
  | 11 => (-48260893 / 200000000000 : ℝ)
  | 12 => (-240968381 / 1000000000000 : ℝ)
  | 13 => (-240575501 / 1000000000000 : ℝ)
  | 14 => (-240124883 / 1000000000000 : ℝ)
  | 15 => (-11980779 / 50000000000 : ℝ)
  | 16 => (-239046639 / 1000000000000 : ℝ)
  | 17 => (-238417099 / 1000000000000 : ℝ)
  | 18 => (-59431499 / 250000000000 : ℝ)
  | 19 => (-5924309 / 25000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch027Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-60379043 / 250000000000 : ℝ)
  | 1 => (-241744417 / 1000000000000 : ℝ)
  | 2 => (-3780091 / 15625000000 : ℝ)
  | 3 => (-242059519 / 1000000000000 : ℝ)
  | 4 => (-12107231 / 50000000000 : ℝ)
  | 5 => (-60541373 / 250000000000 : ℝ)
  | 6 => (-242099469 / 1000000000000 : ℝ)
  | 7 => (-24198127 / 100000000000 : ℝ)
  | 8 => (-241809983 / 1000000000000 : ℝ)
  | 9 => (-241584689 / 1000000000000 : ℝ)
  | 10 => (-15081529 / 62500000000 : ℝ)
  | 11 => (-12048419 / 50000000000 : ℝ)
  | 12 => (-481151 / 2000000000 : ℝ)
  | 13 => (-120062441 / 500000000000 : ℝ)
  | 14 => (-239615579 / 1000000000000 : ℝ)
  | 15 => (-119523319 / 500000000000 : ℝ)
  | 16 => (-119208549 / 500000000000 : ℝ)
  | 17 => (-47545199 / 200000000000 : ℝ)
  | 18 => (-236972359 / 1000000000000 : ℝ)
  | 19 => (-118077607 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch027Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((540 : ℝ) + (j.val : ℝ)) / 1600)
      (((540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch027Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch027Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((540 : ℝ) + (j.val : ℝ)) / 1600)
    (((540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch027Neg100WeightLower j.val) (hpThetaShiftTwoBatch027Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch027Neg100WeightLower, hpThetaShiftTwoBatch027Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch027Neg100_integral_bounds :
    (-331054853 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-407651967 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch027Lower hpThetaJensenCellsBatch027Upper
    hpThetaShiftTwoBatch027Neg100WeightLower hpThetaShiftTwoBatch027Neg100WeightUpper hpThetaJensenCellsBatch027_bounds hpThetaShiftTwoBatch027Neg100_weight_bounds
  have hl : (-331054853 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch027Lower j * hpThetaShiftTwoBatch027Neg100WeightLower j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftTwoBatch027Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftTwoBatch027Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch027Lower j * hpThetaShiftTwoBatch027Neg100WeightUpper j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftTwoBatch027Neg100WeightUpper j) / 1600) ≤ (-407651967 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftTwoBatch027Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (540 : ℝ) / 1600 = 27 / 80 by norm_num,
    show ((540 : ℝ) + 20) / 1600 = (27 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch027Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-227510367 / 1000000000000 : ℝ)
  | 1 => (-57653179 / 250000000000 : ℝ)
  | 2 => (-233726977 / 1000000000000 : ℝ)
  | 3 => (-118426443 / 500000000000 : ℝ)
  | 4 => (-11999509 / 50000000000 : ℝ)
  | 5 => (-121569293 / 500000000000 : ℝ)
  | 6 => (-246297829 / 1000000000000 : ℝ)
  | 7 => (-62366907 / 250000000000 : ℝ)
  | 8 => (-15790481 / 62500000000 : ℝ)
  | 9 => (-255837743 / 1000000000000 : ℝ)
  | 10 => (-259037471 / 1000000000000 : ℝ)
  | 11 => (-131123289 / 500000000000 : ℝ)
  | 12 => (-132732379 / 500000000000 : ℝ)
  | 13 => (-134345849 / 500000000000 : ℝ)
  | 14 => (-271927081 / 1000000000000 : ℝ)
  | 15 => (-137585291 / 500000000000 : ℝ)
  | 16 => (-17819 / 64000000 : ℝ)
  | 17 => (-17605039 / 62500000000 : ℝ)
  | 18 => (-28494649 / 100000000000 : ℝ)
  | 19 => (-288219129 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch027Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-112210091 / 500000000000 : ℝ)
  | 1 => (-113755183 / 500000000000 : ℝ)
  | 2 => (-46122543 / 200000000000 : ℝ)
  | 3 => (-228249 / 976562500 : ℝ)
  | 4 => (-47370577 / 200000000000 : ℝ)
  | 5 => (-239990179 / 1000000000000 : ℝ)
  | 6 => (-48627717 / 200000000000 : ℝ)
  | 7 => (-61574457 / 250000000000 : ℝ)
  | 8 => (-249467627 / 1000000000000 : ℝ)
  | 9 => (-50529539 / 200000000000 : ℝ)
  | 10 => (-127918871 / 500000000000 : ℝ)
  | 11 => (-25903747 / 100000000000 : ℝ)
  | 12 => (-262246577 / 1000000000000 : ℝ)
  | 13 => (-265464757 / 1000000000000 : ℝ)
  | 14 => (-268691697 / 1000000000000 : ℝ)
  | 15 => (-6798177 / 25000000000 : ℝ)
  | 16 => (-275170581 / 1000000000000 : ℝ)
  | 17 => (-139210937 / 500000000000 : ℝ)
  | 18 => (-281680623 / 1000000000000 : ℝ)
  | 19 => (-284946489 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch027Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((540 : ℝ) + (j.val : ℝ)) / 1600)
      (((540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch027Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch027Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((540 : ℝ) + (j.val : ℝ)) / 1600)
    (((540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch027Neg65WeightLower j.val) (hpThetaShiftTwoBatch027Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch027Neg65WeightLower, hpThetaShiftTwoBatch027Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch027Neg65_integral_bounds :
    (-220857529 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-1721287473 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch027Lower hpThetaJensenCellsBatch027Upper
    hpThetaShiftTwoBatch027Neg65WeightLower hpThetaShiftTwoBatch027Neg65WeightUpper hpThetaJensenCellsBatch027_bounds hpThetaShiftTwoBatch027Neg65_weight_bounds
  have hl : (-220857529 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch027Lower j * hpThetaShiftTwoBatch027Neg65WeightLower j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftTwoBatch027Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftTwoBatch027Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch027Lower j * hpThetaShiftTwoBatch027Neg65WeightUpper j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftTwoBatch027Neg65WeightUpper j) / 1600) ≤ (-1721287473 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftTwoBatch027Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (540 : ℝ) / 1600 = 27 / 80 by norm_num,
    show ((540 : ℝ) + 20) / 1600 = (27 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch027Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4123453 / 125000000000 : ℝ)
  | 1 => (-7109063 / 200000000000 : ℝ)
  | 2 => (-595791 / 15625000000 : ℝ)
  | 3 => (-8148723 / 200000000000 : ℝ)
  | 4 => (-867687 / 20000000000 : ℝ)
  | 5 => (-23026443 / 500000000000 : ℝ)
  | 6 => (-304683 / 6250000000 : ℝ)
  | 7 => (-12868397 / 250000000000 : ℝ)
  | 8 => (-54225863 / 1000000000000 : ℝ)
  | 9 => (-28503077 / 500000000000 : ℝ)
  | 10 => (-59814511 / 1000000000000 : ℝ)
  | 11 => (-62650981 / 1000000000000 : ℝ)
  | 12 => (-65515607 / 1000000000000 : ℝ)
  | 13 => (-4275527 / 62500000000 : ℝ)
  | 14 => (-14265899 / 200000000000 : ℝ)
  | 15 => (-14855767 / 200000000000 : ℝ)
  | 16 => (-9657061 / 125000000000 : ℝ)
  | 17 => (-16052497 / 200000000000 : ℝ)
  | 18 => (-83296859 / 1000000000000 : ℝ)
  | 19 => (-43179819 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch027Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1903593 / 62500000000 : ℝ)
  | 1 => (-32987623 / 1000000000000 : ℝ)
  | 2 => (-17772657 / 500000000000 : ℝ)
  | 3 => (-38130623 / 1000000000000 : ℝ)
  | 4 => (-20371807 / 500000000000 : ℝ)
  | 5 => (-43384349 / 1000000000000 : ℝ)
  | 6 => (-9210577 / 200000000000 : ℝ)
  | 7 => (-48749279 / 1000000000000 : ℝ)
  | 8 => (-51473587 / 1000000000000 : ℝ)
  | 9 => (-27112931 / 500000000000 : ℝ)
  | 10 => (-57006153 / 1000000000000 : ℝ)
  | 11 => (-5981451 / 100000000000 : ℝ)
  | 12 => (-3132549 / 50000000000 : ℝ)
  | 13 => (-32757803 / 500000000000 : ℝ)
  | 14 => (-68408431 / 1000000000000 : ℝ)
  | 15 => (-35664747 / 500000000000 : ℝ)
  | 16 => (-37139417 / 500000000000 : ℝ)
  | 17 => (-77256487 / 1000000000000 : ℝ)
  | 18 => (-20065621 / 250000000000 : ℝ)
  | 19 => (-41648429 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch027Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((540 : ℝ) + (j.val : ℝ)) / 1600)
      (((540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch027Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch027Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((540 : ℝ) + (j.val : ℝ)) / 1600)
    (((540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch027Neg45WeightLower j.val) (hpThetaShiftTwoBatch027Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch027Neg45WeightLower, hpThetaShiftTwoBatch027Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch027Neg45_integral_bounds :
    (-50204557 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-377267283 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch027Lower hpThetaJensenCellsBatch027Upper
    hpThetaShiftTwoBatch027Neg45WeightLower hpThetaShiftTwoBatch027Neg45WeightUpper hpThetaJensenCellsBatch027_bounds hpThetaShiftTwoBatch027Neg45_weight_bounds
  have hl : (-50204557 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch027Lower j * hpThetaShiftTwoBatch027Neg45WeightLower j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftTwoBatch027Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftTwoBatch027Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch027Lower j * hpThetaShiftTwoBatch027Neg45WeightUpper j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftTwoBatch027Neg45WeightUpper j) / 1600) ≤ (-377267283 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftTwoBatch027Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (540 : ℝ) / 1600 = 27 / 80 by norm_num,
    show ((540 : ℝ) + 20) / 1600 = (27 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch027Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (335510001 / 1000000000000 : ℝ)
  | 1 => (335847051 / 1000000000000 : ℝ)
  | 2 => (168083203 / 500000000000 : ℝ)
  | 3 => (168233941 / 500000000000 : ℝ)
  | 4 => (168375647 / 500000000000 : ℝ)
  | 5 => (337016457 / 1000000000000 : ℝ)
  | 6 => (168631593 / 500000000000 : ℝ)
  | 7 => (168745647 / 500000000000 : ℝ)
  | 8 => (168850297 / 500000000000 : ℝ)
  | 9 => (337890901 / 1000000000000 : ℝ)
  | 10 => (169031013 / 500000000000 : ℝ)
  | 11 => (338213783 / 1000000000000 : ℝ)
  | 12 => (338345981 / 1000000000000 : ℝ)
  | 13 => (169229217 / 500000000000 : ℝ)
  | 14 => (338550951 / 1000000000000 : ℝ)
  | 15 => (67724669 / 200000000000 : ℝ)
  | 16 => (10583607 / 31250000000 : ℝ)
  | 17 => (169353499 / 500000000000 : ℝ)
  | 18 => (10584621 / 31250000000 : ℝ)
  | 19 => (338676789 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch027Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (83961763 / 250000000000 : ℝ)
  | 1 => (336166407 / 1000000000000 : ℝ)
  | 2 => (336467883 / 1000000000000 : ℝ)
  | 3 => (67350259 / 200000000000 : ℝ)
  | 4 => (168508229 / 500000000000 : ℝ)
  | 5 => (337263187 / 1000000000000 : ℝ)
  | 6 => (67498259 / 200000000000 : ℝ)
  | 7 => (67540119 / 200000000000 : ℝ)
  | 8 => (168945451 / 500000000000 : ℝ)
  | 9 => (338062027 / 1000000000000 : ℝ)
  | 10 => (42276723 / 125000000000 : ℝ)
  | 11 => (169172991 / 500000000000 : ℝ)
  | 12 => (67691687 / 200000000000 : ℝ)
  | 13 => (42318869 / 125000000000 : ℝ)
  | 14 => (169311673 / 500000000000 : ℝ)
  | 15 => (13547017 / 40000000000 : ℝ)
  | 16 => (338706999 / 1000000000000 : ℝ)
  | 17 => (338717879 / 1000000000000 : ℝ)
  | 18 => (169358963 / 500000000000 : ℝ)
  | 19 => (338707873 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch027Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((540 : ℝ) + (j.val : ℝ)) / 1600)
      (((540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch027Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch027Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((540 : ℝ) + (j.val : ℝ)) / 1600)
    (((540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch027Neg25WeightLower j.val) (hpThetaShiftTwoBatch027Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch027Neg25WeightLower, hpThetaShiftTwoBatch027Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch027Neg25_integral_bounds :
    (2288780737 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (1160684947 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch027Lower hpThetaJensenCellsBatch027Upper
    hpThetaShiftTwoBatch027Neg25WeightLower hpThetaShiftTwoBatch027Neg25WeightUpper hpThetaJensenCellsBatch027_bounds hpThetaShiftTwoBatch027Neg25_weight_bounds
  have hl : (2288780737 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch027Lower j * hpThetaShiftTwoBatch027Neg25WeightLower j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftTwoBatch027Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftTwoBatch027Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch027Lower j * hpThetaShiftTwoBatch027Neg25WeightUpper j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftTwoBatch027Neg25WeightUpper j) / 1600) ≤ (1160684947 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftTwoBatch027Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (540 : ℝ) / 1600 = 27 / 80 by norm_num,
    show ((540 : ℝ) + 20) / 1600 = (27 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch027Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch027Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch027Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch027Neg25_integral_bounds
end HodgeProofHP
