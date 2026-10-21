/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch050

/-! Exact signed weight and batch integral certificates, batch 50 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch050Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (17410633 / 1000000000000 : ℝ)
  | 1 => (655323 / 50000000000 : ℝ)
  | 2 => (868767 / 100000000000 : ℝ)
  | 3 => (519039 / 125000000000 : ℝ)
  | 4 => (-250797 / 500000000000 : ℝ)
  | 5 => (-5276051 / 1000000000000 : ℝ)
  | 6 => (-10173091 / 1000000000000 : ℝ)
  | 7 => (-15194769 / 1000000000000 : ℝ)
  | 8 => (-20343169 / 1000000000000 : ℝ)
  | 9 => (-25620401 / 1000000000000 : ℝ)
  | 10 => (-7757151 / 250000000000 : ℝ)
  | 11 => (-18284971 / 500000000000 : ℝ)
  | 12 => (-42246607 / 1000000000000 : ℝ)
  | 13 => (-24030411 / 500000000000 : ℝ)
  | 14 => (-27007417 / 500000000000 : ℝ)
  | 15 => (-60110923 / 1000000000000 : ℝ)
  | 16 => (-13270279 / 200000000000 : ℝ)
  | 17 => (-72738587 / 1000000000000 : ℝ)
  | 18 => (-4954679 / 62500000000 : ℝ)
  | 19 => (-42981311 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch050Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (10801059 / 500000000000 : ℝ)
  | 1 => (8705317 / 500000000000 : ℝ)
  | 2 => (13106461 / 1000000000000 : ℝ)
  | 3 => (8687671 / 1000000000000 : ℝ)
  | 4 => (4152313 / 1000000000000 : ℝ)
  | 5 => (-501593 / 1000000000000 : ℝ)
  | 6 => (-105521 / 20000000000 : ℝ)
  | 7 => (-1017309 / 100000000000 : ℝ)
  | 8 => (-949673 / 62500000000 : ℝ)
  | 9 => (-158931 / 7812500000 : ℝ)
  | 10 => (-64051 / 2500000000 : ℝ)
  | 11 => (-31028603 / 1000000000000 : ℝ)
  | 12 => (-36569941 / 1000000000000 : ℝ)
  | 13 => (-21123303 / 500000000000 : ℝ)
  | 14 => (-48060821 / 1000000000000 : ℝ)
  | 15 => (-54014833 / 1000000000000 : ℝ)
  | 16 => (-30055461 / 500000000000 : ℝ)
  | 17 => (-33175697 / 500000000000 : ℝ)
  | 18 => (-36369293 / 500000000000 : ℝ)
  | 19 => (-79274863 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch050Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1000 : ℝ) + (j.val : ℝ)) / 1600)
      (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch050Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch050Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1000 : ℝ) + (j.val : ℝ)) / 1600)
    (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch050Neg100WeightLower j.val) (hpThetaShiftThreeBatch050Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch050Neg100WeightLower, hpThetaShiftThreeBatch050Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch050Neg100_integral_bounds :
    (-1275689 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-2531623 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1000 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch050Lower hpThetaJensenCellsBatch050Upper
    hpThetaShiftThreeBatch050Neg100WeightLower hpThetaShiftThreeBatch050Neg100WeightUpper hpThetaJensenCellsBatch050_bounds hpThetaShiftThreeBatch050Neg100_weight_bounds
  have hl : (-1275689 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch050Lower j * hpThetaShiftThreeBatch050Neg100WeightLower j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftThreeBatch050Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftThreeBatch050Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch050Lower j * hpThetaShiftThreeBatch050Neg100WeightUpper j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftThreeBatch050Neg100WeightUpper j) / 1600) ≤ (-2531623 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftThreeBatch050Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1000 : ℝ) / 1600 = 50 / 80 by norm_num,
    show ((1000 : ℝ) + 20) / 1600 = (50 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch050Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (175796043 / 1000000000000 : ℝ)
  | 1 => (177728581 / 1000000000000 : ℝ)
  | 2 => (35933801 / 200000000000 : ℝ)
  | 3 => (181617157 / 1000000000000 : ℝ)
  | 4 => (22946609 / 125000000000 : ℝ)
  | 5 => (185535983 / 1000000000000 : ℝ)
  | 6 => (93753159 / 500000000000 : ℝ)
  | 7 => (189483699 / 1000000000000 : ℝ)
  | 8 => (38293589 / 200000000000 : ℝ)
  | 9 => (19345887 / 100000000000 : ℝ)
  | 10 => (48864071 / 250000000000 : ℝ)
  | 11 => (197459991 / 1000000000000 : ℝ)
  | 12 => (199469791 / 1000000000000 : ℝ)
  | 13 => (100742739 / 500000000000 : ℝ)
  | 14 => (101753421 / 500000000000 : ℝ)
  | 15 => (205533669 / 1000000000000 : ℝ)
  | 16 => (207565739 / 1000000000000 : ℝ)
  | 17 => (8384113 / 40000000000 : ℝ)
  | 18 => (211644697 / 1000000000000 : ℝ)
  | 19 => (2671139 / 12500000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch050Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (88864291 / 500000000000 : ℝ)
  | 1 => (89834503 / 500000000000 : ℝ)
  | 2 => (90808579 / 500000000000 : ℝ)
  | 3 => (183572873 / 1000000000000 : ℝ)
  | 4 => (11595999 / 62500000000 : ℝ)
  | 5 => (187506319 / 1000000000000 : ℝ)
  | 6 => (1894837 / 10000000000 : ℝ)
  | 7 => (95733973 / 500000000000 : ℝ)
  | 8 => (193458871 / 1000000000000 : ℝ)
  | 9 => (39091257 / 200000000000 : ℝ)
  | 10 => (24682499 / 125000000000 : ℝ)
  | 11 => (6233431 / 31250000000 : ℝ)
  | 12 => (201485479 / 1000000000000 : ℝ)
  | 13 => (203506843 / 1000000000000 : ℝ)
  | 14 => (20553367 / 100000000000 : ℝ)
  | 15 => (10378287 / 50000000000 : ℝ)
  | 16 => (104801413 / 500000000000 : ℝ)
  | 17 => (105822349 / 500000000000 : ℝ)
  | 18 => (213691121 / 1000000000000 : ℝ)
  | 19 => (215741853 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch050Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1000 : ℝ) + (j.val : ℝ)) / 1600)
      (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch050Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch050Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1000 : ℝ) + (j.val : ℝ)) / 1600)
    (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch050Neg70WeightLower j.val) (hpThetaShiftThreeBatch050Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch050Neg70WeightLower, hpThetaShiftThreeBatch050Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch050Neg70_integral_bounds :
    (8480639 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (436841 / 10000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1000 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch050Lower hpThetaJensenCellsBatch050Upper
    hpThetaShiftThreeBatch050Neg70WeightLower hpThetaShiftThreeBatch050Neg70WeightUpper hpThetaJensenCellsBatch050_bounds hpThetaShiftThreeBatch050Neg70_weight_bounds
  have hl : (8480639 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch050Lower j * hpThetaShiftThreeBatch050Neg70WeightLower j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftThreeBatch050Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftThreeBatch050Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch050Lower j * hpThetaShiftThreeBatch050Neg70WeightUpper j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftThreeBatch050Neg70WeightUpper j) / 1600) ≤ (436841 / 10000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftThreeBatch050Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1000 : ℝ) / 1600 = 50 / 80 by norm_num,
    show ((1000 : ℝ) + 20) / 1600 = (50 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch050Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-33768993 / 1000000000000 : ℝ)
  | 1 => (-33319647 / 1000000000000 : ℝ)
  | 2 => (-4107483 / 125000000000 : ℝ)
  | 3 => (-16194769 / 500000000000 : ℝ)
  | 4 => (-6381713 / 200000000000 : ℝ)
  | 5 => (-31416839 / 1000000000000 : ℝ)
  | 6 => (-15457127 / 500000000000 : ℝ)
  | 7 => (-15200351 / 500000000000 : ℝ)
  | 8 => (-29876077 / 1000000000000 : ℝ)
  | 9 => (-1833767 / 62500000000 : ℝ)
  | 10 => (-14396589 / 500000000000 : ℝ)
  | 11 => (-441167 / 15625000000 : ℝ)
  | 12 => (-27664691 / 1000000000000 : ℝ)
  | 13 => (-677077 / 25000000000 : ℝ)
  | 14 => (-1655609 / 62500000000 : ℝ)
  | 15 => (-25884573 / 1000000000000 : ℝ)
  | 16 => (-25267457 / 1000000000000 : ℝ)
  | 17 => (-4927657 / 200000000000 : ℝ)
  | 18 => (-11998473 / 500000000000 : ℝ)
  | 19 => (-729479 / 31250000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch050Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-16659823 / 500000000000 : ℝ)
  | 1 => (-32859863 / 1000000000000 : ℝ)
  | 2 => (-32389537 / 1000000000000 : ℝ)
  | 3 => (-7977141 / 250000000000 : ℝ)
  | 4 => (-15708419 / 500000000000 : ℝ)
  | 5 => (-30914253 / 1000000000000 : ℝ)
  | 6 => (-30400701 / 1000000000000 : ℝ)
  | 7 => (-7469019 / 250000000000 : ℝ)
  | 8 => (-29340271 / 1000000000000 : ℝ)
  | 9 => (-28793177 / 1000000000000 : ℝ)
  | 10 => (-28234687 / 1000000000000 : ℝ)
  | 11 => (-2766469 / 100000000000 : ℝ)
  | 12 => (-27083079 / 1000000000000 : ℝ)
  | 13 => (-26489743 / 1000000000000 : ℝ)
  | 14 => (-6471143 / 250000000000 : ℝ)
  | 15 => (-98701 / 3906250000 : ℝ)
  | 16 => (-6159571 / 250000000000 : ℝ)
  | 17 => (-4799389 / 200000000000 : ℝ)
  | 18 => (-23343327 / 1000000000000 : ℝ)
  | 19 => (-11338659 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch050Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1000 : ℝ) + (j.val : ℝ)) / 1600)
      (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch050Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch050Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1000 : ℝ) + (j.val : ℝ)) / 1600)
    (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch050Neg45WeightLower j.val) (hpThetaShiftThreeBatch050Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch050Neg45WeightLower, hpThetaShiftThreeBatch050Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch050Neg45_integral_bounds :
    (-648601 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-6240313 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1000 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch050Lower hpThetaJensenCellsBatch050Upper
    hpThetaShiftThreeBatch050Neg45WeightLower hpThetaShiftThreeBatch050Neg45WeightUpper hpThetaJensenCellsBatch050_bounds hpThetaShiftThreeBatch050Neg45_weight_bounds
  have hl : (-648601 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch050Lower j * hpThetaShiftThreeBatch050Neg45WeightLower j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftThreeBatch050Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftThreeBatch050Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch050Lower j * hpThetaShiftThreeBatch050Neg45WeightUpper j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftThreeBatch050Neg45WeightUpper j) / 1600) ≤ (-6240313 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftThreeBatch050Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1000 : ℝ) / 1600 = 50 / 80 by norm_num,
    show ((1000 : ℝ) + 20) / 1600 = (50 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch050Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-31466803 / 500000000000 : ℝ)
  | 1 => (-63636153 / 1000000000000 : ℝ)
  | 2 => (-12868451 / 200000000000 : ℝ)
  | 3 => (-254109 / 3906250000 : ℝ)
  | 4 => (-65765093 / 1000000000000 : ℝ)
  | 5 => (-13296363 / 200000000000 : ℝ)
  | 6 => (-67202063 / 1000000000000 : ℝ)
  | 7 => (-33962913 / 500000000000 : ℝ)
  | 8 => (-34326549 / 500000000000 : ℝ)
  | 9 => (-6938387 / 100000000000 : ℝ)
  | 10 => (-17529533 / 250000000000 : ℝ)
  | 11 => (-17713969 / 250000000000 : ℝ)
  | 12 => (-71597091 / 1000000000000 : ℝ)
  | 13 => (-72341767 / 1000000000000 : ℝ)
  | 14 => (-36544947 / 500000000000 : ℝ)
  | 15 => (-73841463 / 1000000000000 : ℝ)
  | 16 => (-74596461 / 1000000000000 : ℝ)
  | 17 => (-75354877 / 1000000000000 : ℝ)
  | 18 => (-761167 / 10000000000 : ℝ)
  | 19 => (-38440959 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch050Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-62234619 / 1000000000000 : ℝ)
  | 1 => (-12586721 / 200000000000 : ℝ)
  | 2 => (-7954519 / 125000000000 : ℝ)
  | 3 => (-32171127 / 500000000000 : ℝ)
  | 4 => (-65051903 / 1000000000000 : ℝ)
  | 5 => (-16441273 / 250000000000 : ℝ)
  | 6 => (-33240907 / 500000000000 : ℝ)
  | 7 => (-33601031 / 500000000000 : ℝ)
  | 8 => (-2717033 / 40000000000 : ℝ)
  | 9 => (-68653097 / 1000000000000 : ℝ)
  | 10 => (-69383869 / 1000000000000 : ℝ)
  | 11 => (-70118131 / 1000000000000 : ℝ)
  | 12 => (-566847 / 8000000000 : ℝ)
  | 13 => (-7159709 / 100000000000 : ℝ)
  | 14 => (-36170883 / 500000000000 : ℝ)
  | 15 => (-73089893 / 1000000000000 : ℝ)
  | 16 => (-36920731 / 500000000000 : ℝ)
  | 17 => (-3729823 / 50000000000 : ℝ)
  | 18 => (-18838719 / 250000000000 : ℝ)
  | 19 => (-76116699 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch050Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1000 : ℝ) + (j.val : ℝ)) / 1600)
      (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch050Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch050Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1000 : ℝ) + (j.val : ℝ)) / 1600)
    (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch050Neg25WeightLower j.val) (hpThetaShiftThreeBatch050Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch050Neg25WeightLower, hpThetaShiftThreeBatch050Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch050Neg25_integral_bounds :
    (-7756297 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-602111 / 40000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1000 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch050Lower hpThetaJensenCellsBatch050Upper
    hpThetaShiftThreeBatch050Neg25WeightLower hpThetaShiftThreeBatch050Neg25WeightUpper hpThetaJensenCellsBatch050_bounds hpThetaShiftThreeBatch050Neg25_weight_bounds
  have hl : (-7756297 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch050Lower j * hpThetaShiftThreeBatch050Neg25WeightLower j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftThreeBatch050Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftThreeBatch050Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch050Lower j * hpThetaShiftThreeBatch050Neg25WeightUpper j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftThreeBatch050Neg25WeightUpper j) / 1600) ≤ (-602111 / 40000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftThreeBatch050Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1000 : ℝ) / 1600 = 50 / 80 by norm_num,
    show ((1000 : ℝ) + 20) / 1600 = (50 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch050Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch050Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch050Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch050Neg25_integral_bounds
end HodgeProofHP
