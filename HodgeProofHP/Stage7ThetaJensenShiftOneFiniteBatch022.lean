/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch022

/-! Exact signed weight and batch integral certificates, batch 22 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch022Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-16514020513 / 1000000000000 : ℝ)
  | 1 => (-8258726991 / 500000000000 : ℝ)
  | 2 => (-258098143 / 15625000000 : ℝ)
  | 3 => (-16518164841 / 1000000000000 : ℝ)
  | 4 => (-16516117673 / 1000000000000 : ℝ)
  | 5 => (-4127819249 / 250000000000 : ℝ)
  | 6 => (-8251803633 / 500000000000 : ℝ)
  | 7 => (-16493072881 / 1000000000000 : ℝ)
  | 8 => (-16479638187 / 1000000000000 : ℝ)
  | 9 => (-8231633739 / 500000000000 : ℝ)
  | 10 => (-16443924999 / 1000000000000 : ℝ)
  | 11 => (-3284314991 / 200000000000 : ℝ)
  | 12 => (-4099045377 / 250000000000 : ℝ)
  | 13 => (-1022981799 / 62500000000 : ℝ)
  | 14 => (-16336120879 / 1000000000000 : ℝ)
  | 15 => (-16301381857 / 1000000000000 : ℝ)
  | 16 => (-203293197 / 12500000000 : ℝ)
  | 17 => (-3244461321 / 200000000000 : ℝ)
  | 18 => (-4044474599 / 250000000000 : ℝ)
  | 19 => (-16130195121 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch022Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-16507899783 / 1000000000000 : ℝ)
  | 1 => (-516063141 / 31250000000 : ℝ)
  | 2 => (-16517453981 / 1000000000000 : ℝ)
  | 3 => (-2064514709 / 125000000000 : ℝ)
  | 4 => (-3302255399 / 200000000000 : ℝ)
  | 5 => (-3300721453 / 200000000000 : ℝ)
  | 6 => (-206163411 / 12500000000 : ℝ)
  | 7 => (-8239819093 / 500000000000 : ℝ)
  | 8 => (-16463267477 / 1000000000000 : ℝ)
  | 9 => (-8221962499 / 500000000000 : ℝ)
  | 10 => (-8210787477 / 500000000000 : ℝ)
  | 11 => (-16396181507 / 1000000000000 : ℝ)
  | 12 => (-16367708783 / 1000000000000 : ℝ)
  | 13 => (-8168060439 / 500000000000 : ℝ)
  | 14 => (-509418183 / 31250000000 : ℝ)
  | 15 => (-16263455759 / 1000000000000 : ℝ)
  | 16 => (-4055576651 / 250000000000 : ℝ)
  | 17 => (-3235579679 / 200000000000 : ℝ)
  | 18 => (-201627439 / 12500000000 : ℝ)
  | 19 => (-8039580379 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch022Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((440 : ℝ) + (j.val : ℝ)) / 1600)
      (((440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch022Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch022Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((440 : ℝ) + (j.val : ℝ)) / 1600)
    (((440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch022Neg100WeightLower j.val) (hpThetaShiftOneBatch022Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch022Neg100WeightLower, hpThetaShiftOneBatch022Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch022Neg100_integral_bounds :
    (-84894584659 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-83701477031 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch022Lower hpThetaJensenCellsBatch022Upper
    hpThetaShiftOneBatch022Neg100WeightLower hpThetaShiftOneBatch022Neg100WeightUpper hpThetaJensenCellsBatch022_bounds hpThetaShiftOneBatch022Neg100_weight_bounds
  have hl : (-84894584659 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch022Lower j * hpThetaShiftOneBatch022Neg100WeightLower j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftOneBatch022Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftOneBatch022Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch022Lower j * hpThetaShiftOneBatch022Neg100WeightUpper j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftOneBatch022Neg100WeightUpper j) / 1600) ≤ (-83701477031 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftOneBatch022Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (440 : ℝ) / 1600 = 22 / 80 by norm_num,
    show ((440 : ℝ) + 20) / 1600 = (22 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch022Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-7466805933 / 500000000000 : ℝ)
  | 1 => (-15080598249 / 1000000000000 : ℝ)
  | 2 => (-15227387529 / 1000000000000 : ℝ)
  | 3 => (-614958491 / 40000000000 : ℝ)
  | 4 => (-7760152459 / 500000000000 : ℝ)
  | 5 => (-15666397751 / 1000000000000 : ℝ)
  | 6 => (-15812222927 / 1000000000000 : ℝ)
  | 7 => (-7978881231 / 500000000000 : ℝ)
  | 8 => (-16102998231 / 1000000000000 : ℝ)
  | 9 => (-2030988997 / 125000000000 : ℝ)
  | 10 => (-16392485297 / 1000000000000 : ℝ)
  | 11 => (-16536699659 / 1000000000000 : ℝ)
  | 12 => (-1668053639 / 100000000000 : ℝ)
  | 13 => (-16823976681 / 1000000000000 : ℝ)
  | 14 => (-16967001587 / 1000000000000 : ℝ)
  | 15 => (-684383681 / 40000000000 : ℝ)
  | 16 => (-17251728779 / 1000000000000 : ℝ)
  | 17 => (-17393392497 / 1000000000000 : ℝ)
  | 18 => (-4383640923 / 250000000000 : ℝ)
  | 19 => (-17675222741 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch022Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-14786445669 / 1000000000000 : ℝ)
  | 1 => (-2986722373 / 200000000000 : ℝ)
  | 2 => (-1885074781 / 125000000000 : ℝ)
  | 3 => (-1903423441 / 125000000000 : ℝ)
  | 4 => (-7686981137 / 500000000000 : ℝ)
  | 5 => (-15520304917 / 1000000000000 : ℝ)
  | 6 => (-62665591 / 4000000000 : ℝ)
  | 7 => (-7906111463 / 500000000000 : ℝ)
  | 8 => (-15957762461 / 1000000000000 : ℝ)
  | 9 => (-1610299823 / 100000000000 : ℝ)
  | 10 => (-649916479 / 40000000000 : ℝ)
  | 11 => (-1024530331 / 62500000000 : ℝ)
  | 12 => (-8268349829 / 500000000000 : ℝ)
  | 13 => (-16680536389 / 1000000000000 : ℝ)
  | 14 => (-420599417 / 25000000000 : ℝ)
  | 15 => (-8483500793 / 500000000000 : ℝ)
  | 16 => (-2138699003 / 125000000000 : ℝ)
  | 17 => (-8625864389 / 500000000000 : ℝ)
  | 18 => (-1087087031 / 62500000000 : ℝ)
  | 19 => (-17534563691 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch022Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((440 : ℝ) + (j.val : ℝ)) / 1600)
      (((440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch022Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch022Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((440 : ℝ) + (j.val : ℝ)) / 1600)
    (((440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch022Neg65WeightLower j.val) (hpThetaShiftOneBatch022Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch022Neg65WeightLower, hpThetaShiftOneBatch022Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch022Neg65_integral_bounds :
    (-84325090017 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-33005621633 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch022Lower hpThetaJensenCellsBatch022Upper
    hpThetaShiftOneBatch022Neg65WeightLower hpThetaShiftOneBatch022Neg65WeightUpper hpThetaJensenCellsBatch022_bounds hpThetaShiftOneBatch022Neg65_weight_bounds
  have hl : (-84325090017 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch022Lower j * hpThetaShiftOneBatch022Neg65WeightLower j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftOneBatch022Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftOneBatch022Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch022Lower j * hpThetaShiftOneBatch022Neg65WeightUpper j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftOneBatch022Neg65WeightUpper j) / 1600) ≤ (-33005621633 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftOneBatch022Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (440 : ℝ) / 1600 = 22 / 80 by norm_num,
    show ((440 : ℝ) + 20) / 1600 = (22 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch022Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-345975059 / 100000000000 : ℝ)
  | 1 => (-1797892533 / 500000000000 : ℝ)
  | 2 => (-233290411 / 62500000000 : ℝ)
  | 3 => (-3870331593 / 1000000000000 : ℝ)
  | 4 => (-4008836513 / 1000000000000 : ℝ)
  | 5 => (-207407883 / 50000000000 : ℝ)
  | 6 => (-4288291281 / 1000000000000 : ℝ)
  | 7 => (-1107308387 / 250000000000 : ℝ)
  | 8 => (-57137257 / 12500000000 : ℝ)
  | 9 => (-4713528337 / 1000000000000 : ℝ)
  | 10 => (-194274913 / 40000000000 : ℝ)
  | 11 => (-1000201979 / 200000000000 : ℝ)
  | 12 => (-2572967669 / 500000000000 : ℝ)
  | 13 => (-5291644873 / 1000000000000 : ℝ)
  | 14 => (-271906707 / 50000000000 : ℝ)
  | 15 => (-5585398701 / 1000000000000 : ℝ)
  | 16 => (-2866717021 / 500000000000 : ℝ)
  | 17 => (-1470558893 / 250000000000 : ℝ)
  | 18 => (-6031798621 / 1000000000000 : ℝ)
  | 19 => (-1545529611 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch022Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3324546601 / 1000000000000 : ℝ)
  | 1 => (-3459750589 / 1000000000000 : ℝ)
  | 2 => (-719157013 / 200000000000 : ℝ)
  | 3 => (-149305863 / 40000000000 : ℝ)
  | 4 => (-483791449 / 125000000000 : ℝ)
  | 5 => (-125276141 / 31250000000 : ℝ)
  | 6 => (-4148157659 / 1000000000000 : ℝ)
  | 7 => (-53603641 / 12500000000 : ℝ)
  | 8 => (-4429233547 / 1000000000000 : ℝ)
  | 9 => (-4570980559 / 1000000000000 : ℝ)
  | 10 => (-294595521 / 62500000000 : ℝ)
  | 11 => (-607109103 / 125000000000 : ℝ)
  | 12 => (-2500504947 / 500000000000 : ℝ)
  | 13 => (-5145935337 / 1000000000000 : ℝ)
  | 14 => (-661455609 / 125000000000 : ℝ)
  | 15 => (-5438134139 / 1000000000000 : ℝ)
  | 16 => (-55853987 / 10000000000 : ℝ)
  | 17 => (-5733434041 / 1000000000000 : ℝ)
  | 18 => (-5882235571 / 1000000000000 : ℝ)
  | 19 => (-301589931 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch022Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((440 : ℝ) + (j.val : ℝ)) / 1600)
      (((440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch022Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch022Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((440 : ℝ) + (j.val : ℝ)) / 1600)
    (((440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch022Neg40WeightLower j.val) (hpThetaShiftOneBatch022Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch022Neg40WeightLower, hpThetaShiftOneBatch022Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch022Neg40_integral_bounds :
    (-49477284219 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-11847166847 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch022Lower hpThetaJensenCellsBatch022Upper
    hpThetaShiftOneBatch022Neg40WeightLower hpThetaShiftOneBatch022Neg40WeightUpper hpThetaJensenCellsBatch022_bounds hpThetaShiftOneBatch022Neg40_weight_bounds
  have hl : (-49477284219 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch022Lower j * hpThetaShiftOneBatch022Neg40WeightLower j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftOneBatch022Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftOneBatch022Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch022Lower j * hpThetaShiftOneBatch022Neg40WeightUpper j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftOneBatch022Neg40WeightUpper j) / 1600) ≤ (-11847166847 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftOneBatch022Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (440 : ℝ) / 1600 = 22 / 80 by norm_num,
    show ((440 : ℝ) + 20) / 1600 = (22 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch022Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (13353823901 / 1000000000000 : ℝ)
  | 1 => (13320746677 / 1000000000000 : ℝ)
  | 2 => (13286907653 / 1000000000000 : ℝ)
  | 3 => (13252304293 / 1000000000000 : ℝ)
  | 4 => (528677363 / 40000000000 : ℝ)
  | 5 => (13180794497 / 1000000000000 : ℝ)
  | 6 => (1314388307 / 100000000000 : ℝ)
  | 7 => (6553098663 / 500000000000 : ℝ)
  | 8 => (13067734811 / 1000000000000 : ℝ)
  | 9 => (13028493091 / 1000000000000 : ℝ)
  | 10 => (6494234873 / 500000000000 : ℝ)
  | 11 => (12947662377 / 1000000000000 : ℝ)
  | 12 => (64530343 / 5000000000 : ℝ)
  | 13 => (257273721 / 20000000000 : ℝ)
  | 14 => (12820512379 / 1000000000000 : ℝ)
  | 15 => (638827263 / 50000000000 : ℝ)
  | 16 => (12731782379 / 1000000000000 : ℝ)
  | 17 => (3171555361 / 250000000000 : ℝ)
  | 18 => (12639860181 / 1000000000000 : ℝ)
  | 19 => (6296348167 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch022Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (334653547 / 25000000000 : ℝ)
  | 1 => (6676911951 / 500000000000 : ℝ)
  | 2 => (6660373339 / 500000000000 : ℝ)
  | 3 => (6643453827 / 500000000000 : ℝ)
  | 4 => (6626152147 / 500000000000 : ℝ)
  | 5 => (3304233519 / 250000000000 : ℝ)
  | 6 => (6590397249 / 500000000000 : ℝ)
  | 7 => (13143883071 / 1000000000000 : ℝ)
  | 8 => (13106197327 / 1000000000000 : ℝ)
  | 9 => (3266933703 / 250000000000 : ℝ)
  | 10 => (3257123273 / 250000000000 : ℝ)
  | 11 => (12988469747 / 1000000000000 : ℝ)
  | 12 => (6473831189 / 500000000000 : ℝ)
  | 13 => (12906068601 / 1000000000000 : ℝ)
  | 14 => (12863686051 / 1000000000000 : ℝ)
  | 15 => (641025619 / 50000000000 : ℝ)
  | 16 => (12776545261 / 1000000000000 : ℝ)
  | 17 => (636589119 / 50000000000 : ℝ)
  | 18 => (2537244289 / 200000000000 : ℝ)
  | 19 => (6319930091 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch022Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((440 : ℝ) + (j.val : ℝ)) / 1600)
      (((440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch022Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch022Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((440 : ℝ) + (j.val : ℝ)) / 1600)
    (((440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch022Neg20WeightLower j.val) (hpThetaShiftOneBatch022Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch022Neg20WeightLower, hpThetaShiftOneBatch022Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch022Neg20_integral_bounds :
    (16602829549 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (8433977877 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch022Lower hpThetaJensenCellsBatch022Upper
    hpThetaShiftOneBatch022Neg20WeightLower hpThetaShiftOneBatch022Neg20WeightUpper hpThetaJensenCellsBatch022_bounds hpThetaShiftOneBatch022Neg20_weight_bounds
  have hl : (16602829549 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch022Lower j * hpThetaShiftOneBatch022Neg20WeightLower j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftOneBatch022Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftOneBatch022Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch022Lower j * hpThetaShiftOneBatch022Neg20WeightUpper j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftOneBatch022Neg20WeightUpper j) / 1600) ≤ (8433977877 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftOneBatch022Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (440 : ℝ) / 1600 = 22 / 80 by norm_num,
    show ((440 : ℝ) + 20) / 1600 = (22 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch022Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch022Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch022Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch022Neg20_integral_bounds
end HodgeProofHP
