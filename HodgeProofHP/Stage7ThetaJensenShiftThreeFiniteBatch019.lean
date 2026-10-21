/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch019

/-! Exact signed weight and batch integral certificates, batch 19 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch019Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (204821 / 1000000000000 : ℝ)
  | 1 => (203633 / 1000000000000 : ℝ)
  | 2 => (5059 / 25000000000 : ℝ)
  | 3 => (201001 / 1000000000000 : ℝ)
  | 4 => (99777 / 500000000000 : ℝ)
  | 5 => (99009 / 500000000000 : ℝ)
  | 6 => (196391 / 1000000000000 : ℝ)
  | 7 => (12167 / 62500000000 : ℝ)
  | 8 => (96429 / 500000000000 : ℝ)
  | 9 => (190949 / 1000000000000 : ℝ)
  | 10 => (94471 / 500000000000 : ℝ)
  | 11 => (186837 / 1000000000000 : ℝ)
  | 12 => (184631 / 1000000000000 : ℝ)
  | 13 => (182323 / 1000000000000 : ℝ)
  | 14 => (17991 / 100000000000 : ℝ)
  | 15 => (177393 / 1000000000000 : ℝ)
  | 16 => (10923 / 62500000000 : ℝ)
  | 17 => (86017 / 500000000000 : ℝ)
  | 18 => (16919 / 100000000000 : ℝ)
  | 19 => (166233 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch019Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (205927 / 1000000000000 : ℝ)
  | 1 => (102411 / 500000000000 : ℝ)
  | 2 => (101817 / 500000000000 : ℝ)
  | 3 => (202361 / 1000000000000 : ℝ)
  | 4 => (100501 / 500000000000 : ℝ)
  | 5 => (39911 / 200000000000 : ℝ)
  | 6 => (198019 / 1000000000000 : ℝ)
  | 7 => (24549 / 125000000000 : ℝ)
  | 8 => (194673 / 1000000000000 : ℝ)
  | 9 => (192859 / 1000000000000 : ℝ)
  | 10 => (3819 / 20000000000 : ℝ)
  | 11 => (188943 / 1000000000000 : ℝ)
  | 12 => (93419 / 500000000000 : ℝ)
  | 13 => (23079 / 125000000000 : ℝ)
  | 14 => (45581 / 250000000000 : ℝ)
  | 15 => (179911 / 1000000000000 : ℝ)
  | 16 => (88697 / 500000000000 : ℝ)
  | 17 => (174769 / 1000000000000 : ℝ)
  | 18 => (34407 / 200000000000 : ℝ)
  | 19 => (169191 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch019Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((380 : ℝ) + (j.val : ℝ)) / 1600)
      (((380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch019Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch019Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((380 : ℝ) + (j.val : ℝ)) / 1600)
    (((380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch019Neg100WeightLower j.val) (hpThetaShiftThreeBatch019Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch019Neg100WeightLower, hpThetaShiftThreeBatch019Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch019Neg100_integral_bounds :
    (588331 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (601887 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch019Lower hpThetaJensenCellsBatch019Upper
    hpThetaShiftThreeBatch019Neg100WeightLower hpThetaShiftThreeBatch019Neg100WeightUpper hpThetaJensenCellsBatch019_bounds hpThetaShiftThreeBatch019Neg100_weight_bounds
  have hl : (588331 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch019Lower j * hpThetaShiftThreeBatch019Neg100WeightLower j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftThreeBatch019Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftThreeBatch019Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch019Lower j * hpThetaShiftThreeBatch019Neg100WeightUpper j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftThreeBatch019Neg100WeightUpper j) / 1600) ≤ (601887 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftThreeBatch019Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (380 : ℝ) / 1600 = 19 / 80 by norm_num,
    show ((380 : ℝ) + 20) / 1600 = (19 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch019Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (245569 / 500000000000 : ℝ)
  | 1 => (494881 / 1000000000000 : ℝ)
  | 2 => (498601 / 1000000000000 : ℝ)
  | 3 => (62787 / 125000000000 : ℝ)
  | 4 => (101193 / 200000000000 : ℝ)
  | 5 => (509607 / 1000000000000 : ℝ)
  | 6 => (25661 / 50000000000 : ℝ)
  | 7 => (516803 / 1000000000000 : ℝ)
  | 8 => (104071 / 200000000000 : ℝ)
  | 9 => (261937 / 500000000000 : ℝ)
  | 10 => (103 / 195312500 : ℝ)
  | 11 => (530809 / 1000000000000 : ℝ)
  | 12 => (267111 / 500000000000 : ℝ)
  | 13 => (537597 / 1000000000000 : ℝ)
  | 14 => (540931 / 1000000000000 : ℝ)
  | 15 => (17007 / 31250000000 : ℝ)
  | 16 => (21899 / 40000000000 : ℝ)
  | 17 => (550681 / 1000000000000 : ℝ)
  | 18 => (553841 / 1000000000000 : ℝ)
  | 19 => (278477 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch019Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (247441 / 500000000000 : ℝ)
  | 1 => (249301 / 500000000000 : ℝ)
  | 2 => (502297 / 1000000000000 : ℝ)
  | 3 => (252983 / 500000000000 : ℝ)
  | 4 => (63701 / 125000000000 : ℝ)
  | 5 => (513221 / 1000000000000 : ℝ)
  | 6 => (129201 / 250000000000 : ℝ)
  | 7 => (130089 / 250000000000 : ℝ)
  | 8 => (4191 / 8000000000 : ℝ)
  | 9 => (527361 / 1000000000000 : ℝ)
  | 10 => (53081 / 100000000000 : ℝ)
  | 11 => (534223 / 1000000000000 : ℝ)
  | 12 => (268799 / 500000000000 : ℝ)
  | 13 => (135233 / 250000000000 : ℝ)
  | 14 => (21769 / 40000000000 : ℝ)
  | 15 => (136869 / 250000000000 : ℝ)
  | 16 => (275341 / 500000000000 : ℝ)
  | 17 => (276921 / 500000000000 : ℝ)
  | 18 => (111391 / 200000000000 : ℝ)
  | 19 => (280009 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch019Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((380 : ℝ) + (j.val : ℝ)) / 1600)
      (((380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch019Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch019Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((380 : ℝ) + (j.val : ℝ)) / 1600)
    (((380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch019Neg70WeightLower j.val) (hpThetaShiftThreeBatch019Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch019Neg70WeightLower, hpThetaShiftThreeBatch019Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch019Neg70_integral_bounds :
    (6549339 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (1334873 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch019Lower hpThetaJensenCellsBatch019Upper
    hpThetaShiftThreeBatch019Neg70WeightLower hpThetaShiftThreeBatch019Neg70WeightUpper hpThetaJensenCellsBatch019_bounds hpThetaShiftThreeBatch019Neg70_weight_bounds
  have hl : (6549339 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch019Lower j * hpThetaShiftThreeBatch019Neg70WeightLower j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftThreeBatch019Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftThreeBatch019Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch019Lower j * hpThetaShiftThreeBatch019Neg70WeightUpper j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftThreeBatch019Neg70WeightUpper j) / 1600) ≤ (1334873 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftThreeBatch019Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (380 : ℝ) / 1600 = 19 / 80 by norm_num,
    show ((380 : ℝ) + 20) / 1600 = (19 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch019Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (792391 / 1000000000000 : ℝ)
  | 1 => (80179 / 100000000000 : ℝ)
  | 2 => (202813 / 250000000000 : ℝ)
  | 3 => (102597 / 125000000000 : ℝ)
  | 4 => (830361 / 1000000000000 : ℝ)
  | 5 => (105001 / 125000000000 : ℝ)
  | 6 => (169943 / 200000000000 : ℝ)
  | 7 => (214871 / 250000000000 : ℝ)
  | 8 => (13583 / 15625000000 : ℝ)
  | 9 => (1099 / 1250000000 : ℝ)
  | 10 => (222287 / 250000000000 : ℝ)
  | 11 => (449577 / 500000000000 : ℝ)
  | 12 => (454609 / 500000000000 : ℝ)
  | 13 => (919341 / 1000000000000 : ℝ)
  | 14 => (929521 / 1000000000000 : ℝ)
  | 15 => (469879 / 500000000000 : ℝ)
  | 16 => (950051 / 1000000000000 : ℝ)
  | 17 => (960399 / 1000000000000 : ℝ)
  | 18 => (970803 / 1000000000000 : ℝ)
  | 19 => (490631 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch019Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (801791 / 1000000000000 : ℝ)
  | 1 => (811253 / 1000000000000 : ℝ)
  | 2 => (820777 / 1000000000000 : ℝ)
  | 3 => (415181 / 500000000000 : ℝ)
  | 4 => (840009 / 1000000000000 : ℝ)
  | 5 => (212429 / 250000000000 : ℝ)
  | 6 => (171897 / 200000000000 : ℝ)
  | 7 => (869313 / 1000000000000 : ℝ)
  | 8 => (879201 / 1000000000000 : ℝ)
  | 9 => (889149 / 1000000000000 : ℝ)
  | 10 => (179831 / 200000000000 : ℝ)
  | 11 => (909219 / 1000000000000 : ℝ)
  | 12 => (459671 / 500000000000 : ℝ)
  | 13 => (464761 / 500000000000 : ℝ)
  | 14 => (939759 / 1000000000000 : ℝ)
  | 15 => (237513 / 250000000000 : ℝ)
  | 16 => (2401 / 2500000000 : ℝ)
  | 17 => (242701 / 250000000000 : ℝ)
  | 18 => (981263 / 1000000000000 : ℝ)
  | 19 => (39671 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch019Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((380 : ℝ) + (j.val : ℝ)) / 1600)
      (((380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch019Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch019Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((380 : ℝ) + (j.val : ℝ)) / 1600)
    (((380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch019Neg45WeightLower j.val) (hpThetaShiftThreeBatch019Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch019Neg45WeightLower, hpThetaShiftThreeBatch019Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch019Neg45_integral_bounds :
    (2759017 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (5649621 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch019Lower hpThetaJensenCellsBatch019Upper
    hpThetaShiftThreeBatch019Neg45WeightLower hpThetaShiftThreeBatch019Neg45WeightUpper hpThetaJensenCellsBatch019_bounds hpThetaShiftThreeBatch019Neg45_weight_bounds
  have hl : (2759017 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch019Lower j * hpThetaShiftThreeBatch019Neg45WeightLower j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftThreeBatch019Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftThreeBatch019Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch019Lower j * hpThetaShiftThreeBatch019Neg45WeightUpper j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftThreeBatch019Neg45WeightUpper j) / 1600) ≤ (5649621 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftThreeBatch019Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (380 : ℝ) / 1600 = 19 / 80 by norm_num,
    show ((380 : ℝ) + 20) / 1600 = (19 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch019Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (269569 / 250000000000 : ℝ)
  | 1 => (546681 / 500000000000 : ℝ)
  | 2 => (554303 / 500000000000 : ℝ)
  | 3 => (1124009 / 1000000000000 : ℝ)
  | 4 => (284893 / 250000000000 : ℝ)
  | 5 => (577647 / 500000000000 : ℝ)
  | 6 => (1171179 / 1000000000000 : ℝ)
  | 7 => (593613 / 500000000000 : ℝ)
  | 8 => (300859 / 250000000000 : ℝ)
  | 9 => (1219811 / 1000000000000 : ℝ)
  | 10 => (1236351 / 1000000000000 : ℝ)
  | 11 => (1253057 / 1000000000000 : ℝ)
  | 12 => (126993 / 100000000000 : ℝ)
  | 13 => (321743 / 250000000000 : ℝ)
  | 14 => (652091 / 500000000000 : ℝ)
  | 15 => (660781 / 500000000000 : ℝ)
  | 16 => (1339113 / 1000000000000 : ℝ)
  | 17 => (271367 / 200000000000 : ℝ)
  | 18 => (137473 / 100000000000 : ℝ)
  | 19 => (696399 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch019Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1093363 / 1000000000000 : ℝ)
  | 1 => (1108607 / 1000000000000 : ℝ)
  | 2 => (112401 / 100000000000 : ℝ)
  | 3 => (1139573 / 1000000000000 : ℝ)
  | 4 => (231059 / 200000000000 : ℝ)
  | 5 => (58559 / 50000000000 : ℝ)
  | 6 => (1187227 / 1000000000000 : ℝ)
  | 7 => (1203437 / 1000000000000 : ℝ)
  | 8 => (304953 / 250000000000 : ℝ)
  | 9 => (9659 / 7812500000 : ℝ)
  | 10 => (626529 / 500000000000 : ℝ)
  | 11 => (1269931 / 1000000000000 : ℝ)
  | 12 => (1286973 / 1000000000000 : ℝ)
  | 13 => (1304183 / 1000000000000 : ℝ)
  | 14 => (1321563 / 1000000000000 : ℝ)
  | 15 => (669557 / 500000000000 : ℝ)
  | 16 => (339209 / 250000000000 : ℝ)
  | 17 => (1374731 / 1000000000000 : ℝ)
  | 18 => (1392799 / 1000000000000 : ℝ)
  | 19 => (1411041 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch019Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((380 : ℝ) + (j.val : ℝ)) / 1600)
      (((380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch019Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch019Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((380 : ℝ) + (j.val : ℝ)) / 1600)
    (((380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch019Neg25WeightLower j.val) (hpThetaShiftThreeBatch019Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch019Neg25WeightLower, hpThetaShiftThreeBatch019Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch019Neg25_integral_bounds :
    (15342411 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (15743291 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch019Lower hpThetaJensenCellsBatch019Upper
    hpThetaShiftThreeBatch019Neg25WeightLower hpThetaShiftThreeBatch019Neg25WeightUpper hpThetaJensenCellsBatch019_bounds hpThetaShiftThreeBatch019Neg25_weight_bounds
  have hl : (15342411 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch019Lower j * hpThetaShiftThreeBatch019Neg25WeightLower j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftThreeBatch019Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftThreeBatch019Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch019Lower j * hpThetaShiftThreeBatch019Neg25WeightUpper j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftThreeBatch019Neg25WeightUpper j) / 1600) ≤ (15743291 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftThreeBatch019Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (380 : ℝ) / 1600 = 19 / 80 by norm_num,
    show ((380 : ℝ) + 20) / 1600 = (19 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch019Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch019Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch019Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch019Neg25_integral_bounds
end HodgeProofHP
