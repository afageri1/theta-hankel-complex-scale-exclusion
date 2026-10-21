/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch032

/-! Exact signed weight and batch integral certificates, batch 32 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch032Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4619047619 / 62500000000 : ℝ)
  | 1 => (2995208401 / 40000000000 : ℝ)
  | 2 => (75858874539 / 1000000000000 : ℝ)
  | 3 => (76840662879 / 1000000000000 : ℝ)
  | 4 => (77825480643 / 1000000000000 : ℝ)
  | 5 => (9851653947 / 125000000000 : ℝ)
  | 6 => (79803817549 / 1000000000000 : ℝ)
  | 7 => (40398569273 / 500000000000 : ℝ)
  | 8 => (511206829 / 6250000000 : ℝ)
  | 9 => (41395787991 / 500000000000 : ℝ)
  | 10 => (10474060347 / 125000000000 : ℝ)
  | 11 => (5299731579 / 62500000000 : ℝ)
  | 12 => (85801133707 / 1000000000000 : ℝ)
  | 13 => (17361731273 / 200000000000 : ℝ)
  | 14 => (87818159481 / 1000000000000 : ℝ)
  | 15 => (4441476363 / 50000000000 : ℝ)
  | 16 => (89842641849 / 1000000000000 : ℝ)
  | 17 => (45428691661 / 500000000000 : ℝ)
  | 18 => (45936814827 / 500000000000 : ℝ)
  | 19 => (9289125671 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch032Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (37440105013 / 500000000000 : ℝ)
  | 1 => (3792943727 / 50000000000 : ℝ)
  | 2 => (480254143 / 6250000000 : ℝ)
  | 3 => (19456370161 / 250000000000 : ℝ)
  | 4 => (78813231577 / 1000000000000 : ℝ)
  | 5 => (1596076351 / 20000000000 : ℝ)
  | 6 => (80797138547 / 1000000000000 : ℝ)
  | 7 => (81793092641 / 1000000000000 : ℝ)
  | 8 => (82791575983 / 1000000000000 : ℝ)
  | 9 => (83792482777 / 1000000000000 : ℝ)
  | 10 => (16959141053 / 200000000000 : ℝ)
  | 11 => (21450283427 / 250000000000 : ℝ)
  | 12 => (43404328183 / 500000000000 : ℝ)
  | 13 => (43909079741 / 500000000000 : ℝ)
  | 14 => (88829527261 / 1000000000000 : ℝ)
  | 15 => (1796852837 / 20000000000 : ℝ)
  | 16 => (90857383323 / 1000000000000 : ℝ)
  | 17 => (18374725931 / 200000000000 : ℝ)
  | 18 => (92891256711 / 1000000000000 : ℝ)
  | 19 => (93910138221 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch032Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((640 : ℝ) + (j.val : ℝ)) / 1600)
      (((640 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch032Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch032Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((640 : ℝ) + (j.val : ℝ)) / 1600)
    (((640 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch032Neg100WeightLower j.val) (hpThetaShiftOneBatch032Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch032Neg100WeightLower, hpThetaShiftOneBatch032Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch032Neg100_integral_bounds :
    (168462157317 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (86500616029 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (640 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch032Lower hpThetaJensenCellsBatch032Upper
    hpThetaShiftOneBatch032Neg100WeightLower hpThetaShiftOneBatch032Neg100WeightUpper hpThetaJensenCellsBatch032_bounds hpThetaShiftOneBatch032Neg100_weight_bounds
  have hl : (168462157317 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch032Lower j * hpThetaShiftOneBatch032Neg100WeightLower j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftOneBatch032Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftOneBatch032Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch032Lower j * hpThetaShiftOneBatch032Neg100WeightUpper j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftOneBatch032Neg100WeightUpper j) / 1600) ≤ (86500616029 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftOneBatch032Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (640 : ℝ) / 1600 = 32 / 80 by norm_num,
    show ((640 : ℝ) + 20) / 1600 = (32 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch032Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5244952381 / 500000000000 : ℝ)
  | 1 => (-10120402827 / 1000000000000 : ℝ)
  | 2 => (-2436408601 / 250000000000 : ℝ)
  | 3 => (-2341394289 / 250000000000 : ℝ)
  | 4 => (-4490104479 / 500000000000 : ℝ)
  | 5 => (-4294753949 / 500000000000 : ℝ)
  | 6 => (-4096726143 / 500000000000 : ℝ)
  | 7 => (-1948005163 / 250000000000 : ℝ)
  | 8 => (-1846297939 / 250000000000 : ℝ)
  | 9 => (-1743236147 / 250000000000 : ℝ)
  | 10 => (-52442067 / 8000000000 : ℝ)
  | 11 => (-306605629 / 50000000000 : ℝ)
  | 12 => (-89116983 / 15625000000 : ℝ)
  | 13 => (-2634680663 / 500000000000 : ℝ)
  | 14 => (-482971603 / 100000000000 : ℝ)
  | 15 => (-2192265743 / 500000000000 : ℝ)
  | 16 => (-3933788417 / 1000000000000 : ℝ)
  | 17 => (-3477467809 / 1000000000000 : ℝ)
  | 18 => (-1507775459 / 500000000000 : ℝ)
  | 19 => (-2548019271 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch032Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5060201413 / 500000000000 : ℝ)
  | 1 => (-9745634403 / 1000000000000 : ℝ)
  | 2 => (-1873115431 / 200000000000 : ℝ)
  | 3 => (-8980208957 / 1000000000000 : ℝ)
  | 4 => (-8589507897 / 1000000000000 : ℝ)
  | 5 => (-1638690457 / 200000000000 : ℝ)
  | 6 => (-7792020651 / 1000000000000 : ℝ)
  | 7 => (-1477038351 / 200000000000 : ℝ)
  | 8 => (-6972944587 / 1000000000000 : ℝ)
  | 9 => (-3277629187 / 500000000000 : ℝ)
  | 10 => (-6132112579 / 1000000000000 : ℝ)
  | 11 => (-5703486911 / 1000000000000 : ℝ)
  | 12 => (-210774453 / 40000000000 : ℝ)
  | 13 => (-4829716029 / 1000000000000 : ℝ)
  | 14 => (-876906297 / 200000000000 : ℝ)
  | 15 => (-15366361 / 3906250000 : ℝ)
  | 16 => (-108670869 / 31250000000 : ℝ)
  | 17 => (-3015550917 / 1000000000000 : ℝ)
  | 18 => (-254801927 / 100000000000 : ℝ)
  | 19 => (-2074854671 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch032Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((640 : ℝ) + (j.val : ℝ)) / 1600)
      (((640 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch032Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch032Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((640 : ℝ) + (j.val : ℝ)) / 1600)
    (((640 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch032Neg65WeightLower j.val) (hpThetaShiftOneBatch032Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch032Neg65WeightLower, hpThetaShiftOneBatch032Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch032Neg65_integral_bounds :
    (-6942640011 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-25666966269 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (640 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch032Lower hpThetaJensenCellsBatch032Upper
    hpThetaShiftOneBatch032Neg65WeightLower hpThetaShiftOneBatch032Neg65WeightUpper hpThetaJensenCellsBatch032_bounds hpThetaShiftOneBatch032Neg65_weight_bounds
  have hl : (-6942640011 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch032Lower j * hpThetaShiftOneBatch032Neg65WeightLower j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftOneBatch032Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftOneBatch032Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch032Lower j * hpThetaShiftOneBatch032Neg65WeightUpper j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftOneBatch032Neg65WeightUpper j) / 1600) ≤ (-25666966269 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftOneBatch032Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (640 : ℝ) / 1600 = 32 / 80 by norm_num,
    show ((640 : ℝ) + 20) / 1600 = (32 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch032Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-465642869 / 12500000000 : ℝ)
  | 1 => (-3737526691 / 100000000000 : ℝ)
  | 2 => (-9374396937 / 250000000000 : ℝ)
  | 3 => (-4702296539 / 125000000000 : ℝ)
  | 4 => (-18868800407 / 500000000000 : ℝ)
  | 5 => (-7571050681 / 200000000000 : ℝ)
  | 6 => (-9492827543 / 250000000000 : ℝ)
  | 7 => (-38085751141 / 1000000000000 : ℝ)
  | 8 => (-9549639069 / 250000000000 : ℝ)
  | 9 => (-38309705479 / 1000000000000 : ℝ)
  | 10 => (-38419178593 / 1000000000000 : ℝ)
  | 11 => (-192634777 / 5000000000 : ℝ)
  | 12 => (-4829126953 / 125000000000 : ℝ)
  | 13 => (-38737338927 / 1000000000000 : ℝ)
  | 14 => (-9709976229 / 250000000000 : ℝ)
  | 15 => (-19470346569 / 500000000000 : ℝ)
  | 16 => (-39039683083 / 1000000000000 : ℝ)
  | 17 => (-7827370837 / 200000000000 : ℝ)
  | 18 => (-39232185821 / 1000000000000 : ℝ)
  | 19 => (-39325657313 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch032Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-18563047619 / 500000000000 : ℝ)
  | 1 => (-37251429519 / 1000000000000 : ℝ)
  | 2 => (-37375266909 / 1000000000000 : ℝ)
  | 3 => (-37497587747 / 1000000000000 : ℝ)
  | 4 => (-37618372311 / 1000000000000 : ℝ)
  | 5 => (-37737600813 / 1000000000000 : ℝ)
  | 6 => (-9463813351 / 250000000000 : ℝ)
  | 7 => (-37971310171 / 1000000000000 : ℝ)
  | 8 => (-1904287557 / 50000000000 : ℝ)
  | 9 => (-1527942251 / 40000000000 : ℝ)
  | 10 => (-19154852739 / 500000000000 : ℝ)
  | 11 => (-1200599331 / 31250000000 : ℝ)
  | 12 => (-38526955399 / 1000000000000 : ℝ)
  | 13 => (-38633015623 / 1000000000000 : ℝ)
  | 14 => (-19368669463 / 500000000000 : ℝ)
  | 15 => (-7767980983 / 200000000000 : ℝ)
  | 16 => (-38940693137 / 1000000000000 : ℝ)
  | 17 => (-19519841541 / 500000000000 : ℝ)
  | 18 => (-4892106773 / 125000000000 : ℝ)
  | 19 => (-1961609291 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch032Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((640 : ℝ) + (j.val : ℝ)) / 1600)
      (((640 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch032Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch032Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((640 : ℝ) + (j.val : ℝ)) / 1600)
    (((640 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch032Neg40WeightLower j.val) (hpThetaShiftOneBatch032Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch032Neg40WeightLower, hpThetaShiftOneBatch032Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch032Neg40_integral_bounds :
    (-157560758197 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-154825388579 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (640 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch032Lower hpThetaJensenCellsBatch032Upper
    hpThetaShiftOneBatch032Neg40WeightLower hpThetaShiftOneBatch032Neg40WeightUpper hpThetaJensenCellsBatch032_bounds hpThetaShiftOneBatch032Neg40_weight_bounds
  have hl : (-157560758197 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch032Lower j * hpThetaShiftOneBatch032Neg40WeightLower j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftOneBatch032Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftOneBatch032Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch032Lower j * hpThetaShiftOneBatch032Neg40WeightUpper j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftOneBatch032Neg40WeightUpper j) / 1600) ≤ (-154825388579 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftOneBatch032Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (640 : ℝ) / 1600 = 32 / 80 by norm_num,
    show ((640 : ℝ) + 20) / 1600 = (32 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch032Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-10366163943 / 1000000000000 : ℝ)
  | 1 => (-10572348969 / 1000000000000 : ℝ)
  | 2 => (-5389656947 / 500000000000 : ℝ)
  | 3 => (-10987055591 / 1000000000000 : ℝ)
  | 4 => (-5597785447 / 500000000000 : ℝ)
  | 5 => (-5702428299 / 500000000000 : ℝ)
  | 6 => (-11614909461 / 1000000000000 : ℝ)
  | 7 => (-11825726199 / 1000000000000 : ℝ)
  | 8 => (-12037303493 / 1000000000000 : ℝ)
  | 9 => (-6124818991 / 500000000000 : ℝ)
  | 10 => (-12462726267 / 1000000000000 : ℝ)
  | 11 => (-12676564911 / 1000000000000 : ℝ)
  | 12 => (-3222787609 / 250000000000 : ℝ)
  | 13 => (-6553239663 / 500000000000 : ℝ)
  | 14 => (-532901921 / 40000000000 : ℝ)
  | 15 => (-6769676469 / 500000000000 : ℝ)
  | 16 => (-1375689043 / 100000000000 : ℝ)
  | 17 => (-13975156827 / 1000000000000 : ℝ)
  | 18 => (-221783569 / 15625000000 : ℝ)
  | 19 => (-7206930721 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch032Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-635047619 / 62500000000 : ℝ)
  | 1 => (-5183081971 / 500000000000 : ℝ)
  | 2 => (-1321543621 / 125000000000 : ℝ)
  | 3 => (-10779313893 / 1000000000000 : ℝ)
  | 4 => (-1098705559 / 100000000000 : ℝ)
  | 5 => (-11195570893 / 1000000000000 : ℝ)
  | 6 => (-11404856597 / 1000000000000 : ℝ)
  | 7 => (-580745473 / 50000000000 : ℝ)
  | 8 => (-5912863099 / 500000000000 : ℝ)
  | 9 => (-3009325873 / 250000000000 : ℝ)
  | 10 => (-12249637981 / 1000000000000 : ℝ)
  | 11 => (-6231363133 / 500000000000 : ℝ)
  | 12 => (-1267656491 / 100000000000 : ℝ)
  | 13 => (-2578230087 / 200000000000 : ℝ)
  | 14 => (-524259173 / 40000000000 : ℝ)
  | 15 => (-1665318503 / 125000000000 : ℝ)
  | 16 => (-13539352937 / 1000000000000 : ℝ)
  | 17 => (-13756890429 / 1000000000000 : ℝ)
  | 18 => (-6987578413 / 500000000000 : ℝ)
  | 19 => (-2838829683 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch032Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((640 : ℝ) + (j.val : ℝ)) / 1600)
      (((640 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch032Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch032Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((640 : ℝ) + (j.val : ℝ)) / 1600)
    (((640 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch032Neg20WeightLower j.val) (hpThetaShiftOneBatch032Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch032Neg20WeightLower, hpThetaShiftOneBatch032Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch032Neg20_integral_bounds :
    (-50695622873 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-24548940381 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (640 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch032Lower hpThetaJensenCellsBatch032Upper
    hpThetaShiftOneBatch032Neg20WeightLower hpThetaShiftOneBatch032Neg20WeightUpper hpThetaJensenCellsBatch032_bounds hpThetaShiftOneBatch032Neg20_weight_bounds
  have hl : (-50695622873 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch032Lower j * hpThetaShiftOneBatch032Neg20WeightLower j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftOneBatch032Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftOneBatch032Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch032Lower j * hpThetaShiftOneBatch032Neg20WeightUpper j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftOneBatch032Neg20WeightUpper j) / 1600) ≤ (-24548940381 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftOneBatch032Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (640 : ℝ) / 1600 = 32 / 80 by norm_num,
    show ((640 : ℝ) + 20) / 1600 = (32 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch032Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch032Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch032Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch032Neg20_integral_bounds
end HodgeProofHP
