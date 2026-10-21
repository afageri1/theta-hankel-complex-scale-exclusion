/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch019

/-! Exact signed weight and batch integral certificates, batch 19 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch019Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1414451 / 62500000000 : ℝ)
  | 1 => (-5908749 / 250000000000 : ℝ)
  | 2 => (-12325813 / 500000000000 : ℝ)
  | 3 => (-12840553 / 500000000000 : ℝ)
  | 4 => (-13361717 / 500000000000 : ℝ)
  | 5 => (-27778603 / 1000000000000 : ℝ)
  | 6 => (-7211651 / 250000000000 : ℝ)
  | 7 => (-7481857 / 250000000000 : ℝ)
  | 8 => (-15510529 / 500000000000 : ℝ)
  | 9 => (-16063739 / 500000000000 : ℝ)
  | 10 => (-8311667 / 250000000000 : ℝ)
  | 11 => (-6875721 / 200000000000 : ℝ)
  | 12 => (-17761631 / 500000000000 : ℝ)
  | 13 => (-36680611 / 1000000000000 : ℝ)
  | 14 => (-1892531 / 50000000000 : ℝ)
  | 15 => (-9758313 / 250000000000 : ℝ)
  | 16 => (-4022847 / 100000000000 : ℝ)
  | 17 => (-5179529 / 125000000000 : ℝ)
  | 18 => (-10664123 / 250000000000 : ℝ)
  | 19 => (-43889203 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch019Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4328057 / 200000000000 : ℝ)
  | 1 => (-4526243 / 200000000000 : ℝ)
  | 2 => (-4726999 / 200000000000 : ℝ)
  | 3 => (-197213 / 8000000000 : ℝ)
  | 4 => (-5136221 / 200000000000 : ℝ)
  | 5 => (-26723433 / 1000000000000 : ℝ)
  | 6 => (-13889301 / 500000000000 : ℝ)
  | 7 => (-28846603 / 1000000000000 : ℝ)
  | 8 => (-29927427 / 1000000000000 : ℝ)
  | 9 => (-31021057 / 1000000000000 : ℝ)
  | 10 => (-32127477 / 1000000000000 : ℝ)
  | 11 => (-33246667 / 1000000000000 : ℝ)
  | 12 => (-8594651 / 250000000000 : ℝ)
  | 13 => (-35523261 / 1000000000000 : ℝ)
  | 14 => (-3668061 / 100000000000 : ℝ)
  | 15 => (-37850619 / 1000000000000 : ℝ)
  | 16 => (-39033251 / 1000000000000 : ℝ)
  | 17 => (-40228469 / 1000000000000 : ℝ)
  | 18 => (-41436231 / 1000000000000 : ℝ)
  | 19 => (-42656491 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch019Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((380 : ℝ) + (j.val : ℝ)) / 1600)
      (((380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch019Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch019Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((380 : ℝ) + (j.val : ℝ)) / 1600)
    (((380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch019Neg100WeightLower j.val) (hpThetaShiftTwoBatch019Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch019Neg100WeightLower, hpThetaShiftTwoBatch019Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch019Neg100_integral_bounds :
    (-51787987 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-98835687 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch019Lower hpThetaJensenCellsBatch019Upper
    hpThetaShiftTwoBatch019Neg100WeightLower hpThetaShiftTwoBatch019Neg100WeightUpper hpThetaJensenCellsBatch019_bounds hpThetaShiftTwoBatch019Neg100_weight_bounds
  have hl : (-51787987 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch019Lower j * hpThetaShiftTwoBatch019Neg100WeightLower j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftTwoBatch019Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftTwoBatch019Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch019Lower j * hpThetaShiftTwoBatch019Neg100WeightUpper j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftTwoBatch019Neg100WeightUpper j) / 1600) ≤ (-98835687 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftTwoBatch019Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (380 : ℝ) / 1600 = 19 / 80 by norm_num,
    show ((380 : ℝ) + 20) / 1600 = (19 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch019Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (44347191 / 1000000000000 : ℝ)
  | 1 => (10996609 / 250000000000 : ℝ)
  | 2 => (43613269 / 1000000000000 : ℝ)
  | 3 => (4322757 / 100000000000 : ℝ)
  | 4 => (8565843 / 200000000000 : ℝ)
  | 5 => (10604521 / 250000000000 : ℝ)
  | 6 => (5249257 / 125000000000 : ℝ)
  | 7 => (4155701 / 100000000000 : ℝ)
  | 8 => (20553413 / 500000000000 : ℝ)
  | 9 => (5080423 / 125000000000 : ℝ)
  | 10 => (10041641 / 250000000000 : ℝ)
  | 11 => (19838123 / 500000000000 : ℝ)
  | 12 => (39172313 / 1000000000000 : ℝ)
  | 13 => (7730929 / 200000000000 : ℝ)
  | 14 => (9530781 / 250000000000 : ℝ)
  | 15 => (1174301 / 31250000000 : ℝ)
  | 16 => (37018053 / 1000000000000 : ℝ)
  | 17 => (36444269 / 1000000000000 : ℝ)
  | 18 => (7171233 / 200000000000 : ℝ)
  | 19 => (4406703 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch019Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5586957 / 125000000000 : ℝ)
  | 1 => (5543399 / 125000000000 : ℝ)
  | 2 => (43986437 / 1000000000000 : ℝ)
  | 3 => (4361327 / 100000000000 : ℝ)
  | 4 => (43227571 / 1000000000000 : ℝ)
  | 5 => (1338413 / 31250000000 : ℝ)
  | 6 => (8483617 / 200000000000 : ℝ)
  | 7 => (41994057 / 1000000000000 : ℝ)
  | 8 => (41557011 / 1000000000000 : ℝ)
  | 9 => (41106827 / 1000000000000 : ℝ)
  | 10 => (8128677 / 200000000000 : ℝ)
  | 11 => (8033313 / 200000000000 : ℝ)
  | 12 => (39676247 / 1000000000000 : ℝ)
  | 13 => (19586157 / 500000000000 : ℝ)
  | 14 => (19327323 / 500000000000 : ℝ)
  | 15 => (60997 / 1600000000 : ℝ)
  | 16 => (37577633 / 1000000000000 : ℝ)
  | 17 => (18509027 / 500000000000 : ℝ)
  | 18 => (3644427 / 100000000000 : ℝ)
  | 19 => (17928083 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch019Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((380 : ℝ) + (j.val : ℝ)) / 1600)
      (((380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch019Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch019Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((380 : ℝ) + (j.val : ℝ)) / 1600)
    (((380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch019Neg65WeightLower j.val) (hpThetaShiftTwoBatch019Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch019Neg65WeightLower, hpThetaShiftTwoBatch019Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch019Neg65_integral_bounds :
    (100438049 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (257191003 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch019Lower hpThetaJensenCellsBatch019Upper
    hpThetaShiftTwoBatch019Neg65WeightLower hpThetaShiftTwoBatch019Neg65WeightUpper hpThetaJensenCellsBatch019_bounds hpThetaShiftTwoBatch019Neg65_weight_bounds
  have hl : (100438049 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch019Lower j * hpThetaShiftTwoBatch019Neg65WeightLower j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftTwoBatch019Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftTwoBatch019Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch019Lower j * hpThetaShiftTwoBatch019Neg65WeightUpper j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftTwoBatch019Neg65WeightUpper j) / 1600) ≤ (257191003 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftTwoBatch019Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (380 : ℝ) / 1600 = 19 / 80 by norm_num,
    show ((380 : ℝ) + 20) / 1600 = (19 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch019Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (98124551 / 1000000000000 : ℝ)
  | 1 => (6153097 / 62500000000 : ℝ)
  | 2 => (98767641 / 1000000000000 : ℝ)
  | 3 => (99078691 / 1000000000000 : ℝ)
  | 4 => (49691289 / 500000000000 : ℝ)
  | 5 => (12459897 / 125000000000 : ℝ)
  | 6 => (99968357 / 1000000000000 : ℝ)
  | 7 => (50124997 / 500000000000 : ℝ)
  | 8 => (100523959 / 1000000000000 : ℝ)
  | 9 => (100790123 / 1000000000000 : ℝ)
  | 10 => (50524179 / 500000000000 : ℝ)
  | 11 => (25324633 / 250000000000 : ℝ)
  | 12 => (101540517 / 1000000000000 : ℝ)
  | 13 => (5088709 / 50000000000 : ℝ)
  | 14 => (10199939 / 100000000000 : ℝ)
  | 15 => (20443203 / 200000000000 : ℝ)
  | 16 => (102423923 / 1000000000000 : ℝ)
  | 17 => (5131149 / 50000000000 : ℝ)
  | 18 => (25703263 / 250000000000 : ℝ)
  | 19 => (51497003 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch019Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (98449553 / 1000000000000 : ℝ)
  | 1 => (49383821 / 500000000000 : ℝ)
  | 2 => (24769673 / 250000000000 : ℝ)
  | 3 => (99382579 / 1000000000000 : ℝ)
  | 4 => (99679177 / 1000000000000 : ℝ)
  | 5 => (49984179 / 500000000000 : ℝ)
  | 6 => (20049999 / 200000000000 : ℝ)
  | 7 => (2513099 / 25000000000 : ℝ)
  | 8 => (25197531 / 250000000000 : ℝ)
  | 9 => (101048359 / 1000000000000 : ℝ)
  | 10 => (101298533 / 1000000000000 : ℝ)
  | 11 => (50770259 / 500000000000 : ℝ)
  | 12 => (101774181 / 1000000000000 : ℝ)
  | 13 => (101999391 / 1000000000000 : ℝ)
  | 14 => (6388501 / 62500000000 : ℝ)
  | 15 => (25605981 / 250000000000 : ℝ)
  | 16 => (102622981 / 1000000000000 : ℝ)
  | 17 => (102813053 / 1000000000000 : ℝ)
  | 18 => (102994007 / 1000000000000 : ℝ)
  | 19 => (51582853 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch019Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((380 : ℝ) + (j.val : ℝ)) / 1600)
      (((380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch019Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch019Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((380 : ℝ) + (j.val : ℝ)) / 1600)
    (((380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch019Neg45WeightLower j.val) (hpThetaShiftTwoBatch019Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch019Neg45WeightLower, hpThetaShiftTwoBatch019Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch019Neg45_integral_bounds :
    (628867789 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (638285293 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch019Lower hpThetaJensenCellsBatch019Upper
    hpThetaShiftTwoBatch019Neg45WeightLower hpThetaShiftTwoBatch019Neg45WeightUpper hpThetaJensenCellsBatch019_bounds hpThetaShiftTwoBatch019Neg45_weight_bounds
  have hl : (628867789 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch019Lower j * hpThetaShiftTwoBatch019Neg45WeightLower j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftTwoBatch019Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftTwoBatch019Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch019Lower j * hpThetaShiftTwoBatch019Neg45WeightUpper j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftTwoBatch019Neg45WeightUpper j) / 1600) ≤ (638285293 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftTwoBatch019Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (380 : ℝ) / 1600 = 19 / 80 by norm_num,
    show ((380 : ℝ) + 20) / 1600 = (19 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch019Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (163975579 / 1000000000000 : ℝ)
  | 1 => (165227011 / 1000000000000 : ℝ)
  | 2 => (83240653 / 500000000000 : ℝ)
  | 3 => (209673 / 1250000000 : ℝ)
  | 4 => (84499113 / 500000000000 : ℝ)
  | 5 => (170260717 / 1000000000000 : ℝ)
  | 6 => (171525807 / 1000000000000 : ℝ)
  | 7 => (86396713 / 500000000000 : ℝ)
  | 8 => (87031753 / 500000000000 : ℝ)
  | 9 => (21916997 / 125000000000 : ℝ)
  | 10 => (35322153 / 200000000000 : ℝ)
  | 11 => (177887803 / 1000000000000 : ℝ)
  | 12 => (22395877 / 125000000000 : ℝ)
  | 13 => (180448331 / 1000000000000 : ℝ)
  | 14 => (90865837 / 500000000000 : ℝ)
  | 15 => (183016971 / 1000000000000 : ℝ)
  | 16 => (36860829 / 200000000000 : ℝ)
  | 17 => (185593121 / 1000000000000 : ℝ)
  | 18 => (9344191 / 50000000000 : ℝ)
  | 19 => (37635233 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch019Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (41306753 / 250000000000 : ℝ)
  | 1 => (166481307 / 1000000000000 : ℝ)
  | 2 => (167738401 / 1000000000000 : ℝ)
  | 3 => (168998227 / 1000000000000 : ℝ)
  | 4 => (85130359 / 500000000000 : ℝ)
  | 5 => (10720363 / 62500000000 : ℝ)
  | 6 => (172793427 / 1000000000000 : ℝ)
  | 7 => (174063507 / 1000000000000 : ℝ)
  | 8 => (175335977 / 1000000000000 : ℝ)
  | 9 => (88305383 / 500000000000 : ℝ)
  | 10 => (44471951 / 250000000000 : ℝ)
  | 11 => (179167017 / 1000000000000 : ℝ)
  | 12 => (45112083 / 250000000000 : ℝ)
  | 13 => (7269267 / 40000000000 : ℝ)
  | 14 => (45754243 / 250000000000 : ℝ)
  | 15 => (92152073 / 500000000000 : ℝ)
  | 16 => (92796561 / 500000000000 : ℝ)
  | 17 => (186883821 / 1000000000000 : ℝ)
  | 18 => (94088083 / 500000000000 : ℝ)
  | 19 => (94735039 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch019Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((380 : ℝ) + (j.val : ℝ)) / 1600)
      (((380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch019Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch019Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((380 : ℝ) + (j.val : ℝ)) / 1600)
    (((380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch019Neg25WeightLower j.val) (hpThetaShiftTwoBatch019Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch019Neg25WeightLower, hpThetaShiftTwoBatch019Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch019Neg25_integral_bounds :
    (2195410299 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (559704497 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch019Lower hpThetaJensenCellsBatch019Upper
    hpThetaShiftTwoBatch019Neg25WeightLower hpThetaShiftTwoBatch019Neg25WeightUpper hpThetaJensenCellsBatch019_bounds hpThetaShiftTwoBatch019Neg25_weight_bounds
  have hl : (2195410299 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch019Lower j * hpThetaShiftTwoBatch019Neg25WeightLower j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftTwoBatch019Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftTwoBatch019Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch019Lower j * hpThetaShiftTwoBatch019Neg25WeightUpper j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftTwoBatch019Neg25WeightUpper j) / 1600) ≤ (559704497 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftTwoBatch019Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (380 : ℝ) / 1600 = 19 / 80 by norm_num,
    show ((380 : ℝ) + 20) / 1600 = (19 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch019Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch019Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch019Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch019Neg25_integral_bounds
end HodgeProofHP
