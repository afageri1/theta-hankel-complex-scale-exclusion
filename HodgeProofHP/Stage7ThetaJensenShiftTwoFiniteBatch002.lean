/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch002

/-! Exact signed weight and batch integral certificates, batch 2 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch002Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3993 / 125000000000 : ℝ)
  | 1 => (17613 / 500000000000 : ℝ)
  | 2 => (38753 / 1000000000000 : ℝ)
  | 3 => (8507 / 200000000000 : ℝ)
  | 4 => (5823 / 125000000000 : ℝ)
  | 5 => (50911 / 1000000000000 : ℝ)
  | 6 => (5553 / 100000000000 : ℝ)
  | 7 => (15113 / 250000000000 : ℝ)
  | 8 => (65689 / 1000000000000 : ℝ)
  | 9 => (35627 / 500000000000 : ℝ)
  | 10 => (1929 / 25000000000 : ℝ)
  | 11 => (4171 / 50000000000 : ℝ)
  | 12 => (1407 / 15625000000 : ℝ)
  | 13 => (19411 / 200000000000 : ℝ)
  | 14 => (104457 / 1000000000000 : ℝ)
  | 15 => (56133 / 500000000000 : ℝ)
  | 16 => (7531 / 62500000000 : ℝ)
  | 17 => (64581 / 500000000000 : ℝ)
  | 18 => (138277 / 1000000000000 : ℝ)
  | 19 => (29571 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch002Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (35227 / 1000000000000 : ℝ)
  | 1 => (19377 / 500000000000 : ℝ)
  | 2 => (5317 / 125000000000 : ℝ)
  | 3 => (9317 / 200000000000 : ℝ)
  | 4 => (1591 / 31250000000 : ℝ)
  | 5 => (55531 / 1000000000000 : ℝ)
  | 6 => (60453 / 1000000000000 : ℝ)
  | 7 => (6569 / 100000000000 : ℝ)
  | 8 => (14251 / 200000000000 : ℝ)
  | 9 => (77161 / 1000000000000 : ℝ)
  | 10 => (83421 / 1000000000000 : ℝ)
  | 11 => (90049 / 1000000000000 : ℝ)
  | 12 => (3033 / 31250000000 : ℝ)
  | 13 => (52229 / 500000000000 : ℝ)
  | 14 => (112267 / 1000000000000 : ℝ)
  | 15 => (120497 / 1000000000000 : ℝ)
  | 16 => (129163 / 1000000000000 : ℝ)
  | 17 => (69139 / 500000000000 : ℝ)
  | 18 => (9241 / 62500000000 : ℝ)
  | 19 => (157913 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch002Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((40 : ℝ) + (j.val : ℝ)) / 1600)
      (((40 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch002Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch002Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((40 : ℝ) + (j.val : ℝ)) / 1600)
    (((40 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch002Neg100WeightLower j.val) (hpThetaShiftTwoBatch002Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch002Neg100WeightLower, hpThetaShiftTwoBatch002Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch002Neg100_integral_bounds :
    (879317 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (1917537 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (40 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch002Lower hpThetaJensenCellsBatch002Upper
    hpThetaShiftTwoBatch002Neg100WeightLower hpThetaShiftTwoBatch002Neg100WeightUpper hpThetaJensenCellsBatch002_bounds hpThetaShiftTwoBatch002Neg100_weight_bounds
  have hl : (879317 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch002Lower j * hpThetaShiftTwoBatch002Neg100WeightLower j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftTwoBatch002Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftTwoBatch002Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch002Lower j * hpThetaShiftTwoBatch002Neg100WeightUpper j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftTwoBatch002Neg100WeightUpper j) / 1600) ≤ (1917537 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftTwoBatch002Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (40 : ℝ) / 1600 = 2 / 80 by norm_num,
    show ((40 : ℝ) + 20) / 1600 = (2 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch002Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (8039 / 250000000000 : ℝ)
  | 1 => (2217 / 62500000000 : ℝ)
  | 2 => (39037 / 1000000000000 : ℝ)
  | 3 => (21431 / 500000000000 : ℝ)
  | 4 => (46959 / 1000000000000 : ℝ)
  | 5 => (2567 / 50000000000 : ℝ)
  | 6 => (56019 / 1000000000000 : ℝ)
  | 7 => (3813 / 62500000000 : ℝ)
  | 8 => (829 / 12500000000 : ℝ)
  | 9 => (2249 / 31250000000 : ℝ)
  | 10 => (38983 / 500000000000 : ℝ)
  | 11 => (84327 / 1000000000000 : ℝ)
  | 12 => (45533 / 500000000000 : ℝ)
  | 13 => (24549 / 250000000000 : ℝ)
  | 14 => (105733 / 1000000000000 : ℝ)
  | 15 => (113689 / 1000000000000 : ℝ)
  | 16 => (122081 / 1000000000000 : ℝ)
  | 17 => (32731 / 250000000000 : ℝ)
  | 18 => (140231 / 1000000000000 : ℝ)
  | 19 => (7501 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch002Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (35473 / 1000000000000 : ℝ)
  | 1 => (19519 / 500000000000 : ℝ)
  | 2 => (42863 / 1000000000000 : ℝ)
  | 3 => (587 / 12500000000 : ℝ)
  | 4 => (51341 / 1000000000000 : ℝ)
  | 5 => (2801 / 50000000000 : ℝ)
  | 6 => (61009 / 1000000000000 : ℝ)
  | 7 => (66321 / 1000000000000 : ℝ)
  | 8 => (71969 / 1000000000000 : ℝ)
  | 9 => (77967 / 1000000000000 : ℝ)
  | 10 => (10541 / 125000000000 : ℝ)
  | 11 => (91067 / 1000000000000 : ℝ)
  | 12 => (98197 / 1000000000000 : ℝ)
  | 13 => (52867 / 500000000000 : ℝ)
  | 14 => (11369 / 100000000000 : ℝ)
  | 15 => (61041 / 500000000000 : ℝ)
  | 16 => (5237 / 40000000000 : ℝ)
  | 17 => (17529 / 125000000000 : ℝ)
  | 18 => (150021 / 1000000000000 : ℝ)
  | 19 => (80153 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch002Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((40 : ℝ) + (j.val : ℝ)) / 1600)
      (((40 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch002Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch002Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((40 : ℝ) + (j.val : ℝ)) / 1600)
    (((40 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch002Neg65WeightLower j.val) (hpThetaShiftTwoBatch002Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch002Neg65WeightLower, hpThetaShiftTwoBatch002Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch002Neg65_integral_bounds :
    (27793 / 15625000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (970147 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (40 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch002Lower hpThetaJensenCellsBatch002Upper
    hpThetaShiftTwoBatch002Neg65WeightLower hpThetaShiftTwoBatch002Neg65WeightUpper hpThetaJensenCellsBatch002_bounds hpThetaShiftTwoBatch002Neg65_weight_bounds
  have hl : (27793 / 15625000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch002Lower j * hpThetaShiftTwoBatch002Neg65WeightLower j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftTwoBatch002Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftTwoBatch002Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch002Lower j * hpThetaShiftTwoBatch002Neg65WeightUpper j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftTwoBatch002Neg65WeightUpper j) / 1600) ≤ (970147 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftTwoBatch002Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (40 : ℝ) / 1600 = 2 / 80 by norm_num,
    show ((40 : ℝ) + 20) / 1600 = (2 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch002Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (32277 / 1000000000000 : ℝ)
  | 1 => (35613 / 1000000000000 : ℝ)
  | 2 => (49 / 1250000000 : ℝ)
  | 3 => (43049 / 1000000000000 : ℝ)
  | 4 => (23587 / 500000000000 : ℝ)
  | 5 => (25793 / 500000000000 : ℝ)
  | 6 => (563 / 10000000000 : ℝ)
  | 7 => (61327 / 1000000000000 : ℝ)
  | 8 => (33341 / 500000000000 : ℝ)
  | 9 => (72377 / 1000000000000 : ℝ)
  | 10 => (19607 / 250000000000 : ℝ)
  | 11 => (84847 / 1000000000000 : ℝ)
  | 12 => (1833 / 20000000000 : ℝ)
  | 13 => (98851 / 1000000000000 : ℝ)
  | 14 => (21293 / 200000000000 : ℝ)
  | 15 => (114507 / 1000000000000 : ℝ)
  | 16 => (7687 / 62500000000 : ℝ)
  | 17 => (4123 / 31250000000 : ℝ)
  | 18 => (70677 / 500000000000 : ℝ)
  | 19 => (4727 / 31250000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch002Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (17807 / 500000000000 : ℝ)
  | 1 => (39201 / 1000000000000 : ℝ)
  | 2 => (861 / 20000000000 : ℝ)
  | 3 => (1887 / 40000000000 : ℝ)
  | 4 => (51587 / 1000000000000 : ℝ)
  | 5 => (56301 / 1000000000000 : ℝ)
  | 6 => (3833 / 62500000000 : ℝ)
  | 7 => (66683 / 1000000000000 : ℝ)
  | 8 => (36189 / 500000000000 : ℝ)
  | 9 => (78429 / 1000000000000 : ℝ)
  | 10 => (5303 / 62500000000 : ℝ)
  | 11 => (91651 / 1000000000000 : ℝ)
  | 12 => (24713 / 250000000000 : ℝ)
  | 13 => (53233 / 500000000000 : ℝ)
  | 14 => (28627 / 250000000000 : ℝ)
  | 15 => (122993 / 1000000000000 : ℝ)
  | 16 => (131937 / 1000000000000 : ℝ)
  | 17 => (28271 / 200000000000 : ℝ)
  | 18 => (30253 / 200000000000 : ℝ)
  | 19 => (161681 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch002Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((40 : ℝ) + (j.val : ℝ)) / 1600)
      (((40 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch002Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch002Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((40 : ℝ) + (j.val : ℝ)) / 1600)
    (((40 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch002Neg45WeightLower j.val) (hpThetaShiftTwoBatch002Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch002Neg45WeightLower, hpThetaShiftTwoBatch002Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch002Neg45_integral_bounds :
    (1790301 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (24417 / 12500000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (40 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch002Lower hpThetaJensenCellsBatch002Upper
    hpThetaShiftTwoBatch002Neg45WeightLower hpThetaShiftTwoBatch002Neg45WeightUpper hpThetaJensenCellsBatch002_bounds hpThetaShiftTwoBatch002Neg45_weight_bounds
  have hl : (1790301 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch002Lower j * hpThetaShiftTwoBatch002Neg45WeightLower j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftTwoBatch002Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftTwoBatch002Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch002Lower j * hpThetaShiftTwoBatch002Neg45WeightUpper j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftTwoBatch002Neg45WeightUpper j) / 1600) ≤ (24417 / 12500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftTwoBatch002Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (40 : ℝ) / 1600 = 2 / 80 by norm_num,
    show ((40 : ℝ) + 20) / 1600 = (2 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch002Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (32399 / 1000000000000 : ℝ)
  | 1 => (17877 / 500000000000 : ℝ)
  | 2 => (39363 / 1000000000000 : ℝ)
  | 3 => (43237 / 1000000000000 : ℝ)
  | 4 => (47389 / 1000000000000 : ℝ)
  | 5 => (51833 / 1000000000000 : ℝ)
  | 6 => (56581 / 1000000000000 : ℝ)
  | 7 => (61647 / 1000000000000 : ℝ)
  | 8 => (13409 / 200000000000 : ℝ)
  | 9 => (18197 / 250000000000 : ℝ)
  | 10 => (78891 / 1000000000000 : ℝ)
  | 11 => (85369 / 1000000000000 : ℝ)
  | 12 => (23059 / 250000000000 : ℝ)
  | 13 => (24877 / 250000000000 : ℝ)
  | 14 => (67 / 625000000 : ℝ)
  | 15 => (115327 / 1000000000000 : ℝ)
  | 16 => (24781 / 200000000000 : ℝ)
  | 17 => (132951 / 1000000000000 : ℝ)
  | 18 => (142481 / 1000000000000 : ℝ)
  | 19 => (2383 / 15625000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch002Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (7151 / 200000000000 : ℝ)
  | 1 => (9841 / 250000000000 : ℝ)
  | 2 => (21619 / 500000000000 : ℝ)
  | 3 => (4739 / 100000000000 : ℝ)
  | 4 => (25917 / 500000000000 : ℝ)
  | 5 => (28291 / 500000000000 : ℝ)
  | 6 => (3853 / 62500000000 : ℝ)
  | 7 => (33523 / 500000000000 : ℝ)
  | 8 => (72789 / 1000000000000 : ℝ)
  | 9 => (19723 / 250000000000 : ℝ)
  | 10 => (8537 / 100000000000 : ℝ)
  | 11 => (92237 / 1000000000000 : ℝ)
  | 12 => (99509 / 1000000000000 : ℝ)
  | 13 => (107201 / 1000000000000 : ℝ)
  | 14 => (901 / 7812500000 : ℝ)
  | 15 => (61953 / 500000000000 : ℝ)
  | 16 => (16619 / 125000000000 : ℝ)
  | 17 => (71241 / 500000000000 : ℝ)
  | 18 => (152513 / 1000000000000 : ℝ)
  | 19 => (81531 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch002Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((40 : ℝ) + (j.val : ℝ)) / 1600)
      (((40 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch002Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch002Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((40 : ℝ) + (j.val : ℝ)) / 1600)
    (((40 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch002Neg25WeightLower j.val) (hpThetaShiftTwoBatch002Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch002Neg25WeightLower, hpThetaShiftTwoBatch002Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch002Neg25_integral_bounds :
    (450471 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (1966467 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (40 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch002Lower hpThetaJensenCellsBatch002Upper
    hpThetaShiftTwoBatch002Neg25WeightLower hpThetaShiftTwoBatch002Neg25WeightUpper hpThetaJensenCellsBatch002_bounds hpThetaShiftTwoBatch002Neg25_weight_bounds
  have hl : (450471 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch002Lower j * hpThetaShiftTwoBatch002Neg25WeightLower j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftTwoBatch002Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftTwoBatch002Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch002Lower j * hpThetaShiftTwoBatch002Neg25WeightUpper j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftTwoBatch002Neg25WeightUpper j) / 1600) ≤ (1966467 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftTwoBatch002Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (40 : ℝ) / 1600 = 2 / 80 by norm_num,
    show ((40 : ℝ) + 20) / 1600 = (2 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch002Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch002Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch002Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch002Neg25_integral_bounds
end HodgeProofHP
