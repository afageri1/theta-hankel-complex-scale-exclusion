/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch004

/-! Exact signed weight and batch integral certificates, batch 4 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch004Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (96493 / 200000000000 : ℝ)
  | 1 => (7907 / 15625000000 : ℝ)
  | 2 => (530447 / 1000000000000 : ℝ)
  | 3 => (555677 / 1000000000000 : ℝ)
  | 4 => (290877 / 500000000000 : ℝ)
  | 5 => (152173 / 250000000000 : ℝ)
  | 6 => (636509 / 1000000000000 : ℝ)
  | 7 => (332609 / 500000000000 : ℝ)
  | 8 => (694837 / 1000000000000 : ℝ)
  | 9 => (36269 / 50000000000 : ℝ)
  | 10 => (378431 / 500000000000 : ℝ)
  | 11 => (7893 / 10000000000 : ℝ)
  | 12 => (822707 / 1000000000000 : ℝ)
  | 13 => (8571 / 10000000000 : ℝ)
  | 14 => (892493 / 1000000000000 : ℝ)
  | 15 => (928901 / 1000000000000 : ℝ)
  | 16 => (966339 / 1000000000000 : ℝ)
  | 17 => (1004821 / 1000000000000 : ℝ)
  | 18 => (1044363 / 1000000000000 : ℝ)
  | 19 => (542489 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch004Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (506049 / 1000000000000 : ℝ)
  | 1 => (33153 / 62500000000 : ℝ)
  | 2 => (277839 / 500000000000 : ℝ)
  | 3 => (116351 / 200000000000 : ℝ)
  | 4 => (608693 / 1000000000000 : ℝ)
  | 5 => (63651 / 100000000000 : ℝ)
  | 6 => (665219 / 1000000000000 : ℝ)
  | 7 => (347419 / 500000000000 : ℝ)
  | 8 => (725381 / 1000000000000 : ℝ)
  | 9 => (756863 / 1000000000000 : ℝ)
  | 10 => (789301 / 1000000000000 : ℝ)
  | 11 => (205677 / 250000000000 : ℝ)
  | 12 => (857101 / 1000000000000 : ℝ)
  | 13 => (446247 / 500000000000 : ℝ)
  | 14 => (464451 / 500000000000 : ℝ)
  | 15 => (48317 / 50000000000 : ℝ)
  | 16 => (502411 / 500000000000 : ℝ)
  | 17 => (261091 / 250000000000 : ℝ)
  | 18 => (1084979 / 1000000000000 : ℝ)
  | 19 => (563341 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch004Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((80 : ℝ) + (j.val : ℝ)) / 1600)
      (((80 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch004Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch004Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((80 : ℝ) + (j.val : ℝ)) / 1600)
    (((80 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch004Neg100WeightLower j.val) (hpThetaShiftTwoBatch004Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch004Neg100WeightLower, hpThetaShiftTwoBatch004Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch004Neg100_integral_bounds :
    (16313259 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (8596039 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (80 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch004Lower hpThetaJensenCellsBatch004Upper
    hpThetaShiftTwoBatch004Neg100WeightLower hpThetaShiftTwoBatch004Neg100WeightUpper hpThetaJensenCellsBatch004_bounds hpThetaShiftTwoBatch004Neg100_weight_bounds
  have hl : (16313259 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch004Lower j * hpThetaShiftTwoBatch004Neg100WeightLower j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftTwoBatch004Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftTwoBatch004Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch004Lower j * hpThetaShiftTwoBatch004Neg100WeightUpper j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftTwoBatch004Neg100WeightUpper j) / 1600) ≤ (8596039 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftTwoBatch004Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (80 : ℝ) / 1600 = 4 / 80 by norm_num,
    show ((80 : ℝ) + 20) / 1600 = (4 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch004Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (61967 / 125000000000 : ℝ)
  | 1 => (32521 / 62500000000 : ℝ)
  | 2 => (109163 / 200000000000 : ℝ)
  | 3 => (572191 / 1000000000000 : ℝ)
  | 4 => (149871 / 250000000000 : ℝ)
  | 5 => (613 / 976562500 : ℝ)
  | 6 => (131379 / 200000000000 : ℝ)
  | 7 => (687051 / 1000000000000 : ℝ)
  | 8 => (3591 / 5000000000 : ℝ)
  | 9 => (750361 / 1000000000000 : ℝ)
  | 10 => (783553 / 1000000000000 : ℝ)
  | 11 => (204449 / 250000000000 : ℝ)
  | 12 => (213277 / 250000000000 : ℝ)
  | 13 => (88951 / 100000000000 : ℝ)
  | 14 => (46351 / 50000000000 : ℝ)
  | 15 => (965659 / 1000000000000 : ℝ)
  | 16 => (201089 / 200000000000 : ℝ)
  | 17 => (1046399 / 1000000000000 : ℝ)
  | 18 => (544269 / 500000000000 : ℝ)
  | 19 => (282971 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch004Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (520337 / 1000000000000 : ℝ)
  | 1 => (68227 / 125000000000 : ℝ)
  | 2 => (17881 / 31250000000 : ℝ)
  | 3 => (119897 / 200000000000 : ℝ)
  | 4 => (627713 / 1000000000000 : ℝ)
  | 5 => (1283 / 1953125000 : ℝ)
  | 6 => (171763 / 250000000000 : ℝ)
  | 7 => (718201 / 1000000000000 : ℝ)
  | 8 => (375181 / 500000000000 : ℝ)
  | 9 => (391777 / 500000000000 : ℝ)
  | 10 => (817797 / 1000000000000 : ℝ)
  | 11 => (853109 / 1000000000000 : ℝ)
  | 12 => (889511 / 1000000000000 : ℝ)
  | 13 => (927021 / 1000000000000 : ℝ)
  | 14 => (48283 / 50000000000 : ℝ)
  | 15 => (502723 / 500000000000 : ℝ)
  | 16 => (327 / 312500000 : ℝ)
  | 17 => (1088539 / 1000000000000 : ℝ)
  | 18 => (226377 / 200000000000 : ℝ)
  | 19 => (1176457 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch004Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((80 : ℝ) + (j.val : ℝ)) / 1600)
      (((80 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch004Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch004Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((80 : ℝ) + (j.val : ℝ)) / 1600)
    (((80 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch004Neg65WeightLower j.val) (hpThetaShiftTwoBatch004Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch004Neg65WeightLower, hpThetaShiftTwoBatch004Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch004Neg65_integral_bounds :
    (8451713 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (8914201 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (80 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch004Lower hpThetaJensenCellsBatch004Upper
    hpThetaShiftTwoBatch004Neg65WeightLower hpThetaShiftTwoBatch004Neg65WeightUpper hpThetaJensenCellsBatch004_bounds hpThetaShiftTwoBatch004Neg65_weight_bounds
  have hl : (8451713 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch004Lower j * hpThetaShiftTwoBatch004Neg65WeightLower j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftTwoBatch004Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftTwoBatch004Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch004Lower j * hpThetaShiftTwoBatch004Neg65WeightUpper j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftTwoBatch004Neg65WeightUpper j) / 1600) ≤ (8914201 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftTwoBatch004Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (80 : ℝ) / 1600 = 4 / 80 by norm_num,
    show ((80 : ℝ) + 20) / 1600 = (4 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch004Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (125849 / 250000000000 : ℝ)
  | 1 => (66073 / 125000000000 : ℝ)
  | 2 => (554689 / 1000000000000 : ℝ)
  | 3 => (581729 / 1000000000000 : ℝ)
  | 4 => (9527 / 15625000000 : ℝ)
  | 5 => (39919 / 62500000000 : ℝ)
  | 6 => (668679 / 1000000000000 : ℝ)
  | 7 => (27987 / 40000000000 : ℝ)
  | 8 => (731713 / 1000000000000 : ℝ)
  | 9 => (382407 / 500000000000 : ℝ)
  | 10 => (798999 / 1000000000000 : ℝ)
  | 11 => (834291 / 1000000000000 : ℝ)
  | 12 => (108839 / 125000000000 : ℝ)
  | 13 => (908283 / 1000000000000 : ℝ)
  | 14 => (473513 / 500000000000 : ℝ)
  | 15 => (986963 / 1000000000000 : ℝ)
  | 16 => (1028117 / 1000000000000 : ℝ)
  | 17 => (107051 / 100000000000 : ℝ)
  | 18 => (222833 / 200000000000 : ℝ)
  | 19 => (18111 / 15625000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch004Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (105717 / 200000000000 : ℝ)
  | 1 => (55469 / 100000000000 : ℝ)
  | 2 => (58173 / 100000000000 : ℝ)
  | 3 => (609729 / 1000000000000 : ℝ)
  | 4 => (127741 / 200000000000 : ℝ)
  | 5 => (16717 / 25000000000 : ℝ)
  | 6 => (174919 / 250000000000 : ℝ)
  | 7 => (365857 / 500000000000 : ℝ)
  | 8 => (152963 / 200000000000 : ℝ)
  | 9 => (799 / 1000000000 : ℝ)
  | 10 => (208573 / 250000000000 : ℝ)
  | 11 => (870713 / 1000000000000 : ℝ)
  | 12 => (227071 / 250000000000 : ℝ)
  | 13 => (947027 / 1000000000000 : ℝ)
  | 14 => (246741 / 250000000000 : ℝ)
  | 15 => (514059 / 500000000000 : ℝ)
  | 16 => (1070511 / 1000000000000 : ℝ)
  | 17 => (557083 / 500000000000 : ℝ)
  | 18 => (231821 / 200000000000 : ℝ)
  | 19 => (24107 / 20000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch004Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((80 : ℝ) + (j.val : ℝ)) / 1600)
      (((80 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch004Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch004Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((80 : ℝ) + (j.val : ℝ)) / 1600)
    (((80 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch004Neg45WeightLower j.val) (hpThetaShiftTwoBatch004Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch004Neg45WeightLower, hpThetaShiftTwoBatch004Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch004Neg45_integral_bounds :
    (17245143 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (18196949 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (80 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch004Lower hpThetaJensenCellsBatch004Upper
    hpThetaShiftTwoBatch004Neg45WeightLower hpThetaShiftTwoBatch004Neg45WeightUpper hpThetaJensenCellsBatch004_bounds hpThetaShiftTwoBatch004Neg45_weight_bounds
  have hl : (17245143 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch004Lower j * hpThetaShiftTwoBatch004Neg45WeightLower j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftTwoBatch004Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftTwoBatch004Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch004Lower j * hpThetaShiftTwoBatch004Neg45WeightUpper j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftTwoBatch004Neg45WeightUpper j) / 1600) ≤ (18196949 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftTwoBatch004Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (80 : ℝ) / 1600 = 4 / 80 by norm_num,
    show ((80 : ℝ) + 20) / 1600 = (4 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch004Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (511111 / 1000000000000 : ℝ)
  | 1 => (268447 / 500000000000 : ℝ)
  | 2 => (56363 / 100000000000 : ℝ)
  | 3 => (295671 / 500000000000 : ℝ)
  | 4 => (620053 / 1000000000000 : ℝ)
  | 5 => (324893 / 500000000000 : ℝ)
  | 6 => (680563 / 1000000000000 : ℝ)
  | 7 => (89051 / 125000000000 : ℝ)
  | 8 => (149069 / 200000000000 : ℝ)
  | 9 => (779397 / 1000000000000 : ℝ)
  | 10 => (203647 / 250000000000 : ℝ)
  | 11 => (425471 / 500000000000 : ℝ)
  | 12 => (177697 / 200000000000 : ℝ)
  | 13 => (23181 / 25000000000 : ℝ)
  | 14 => (15113 / 15625000000 : ℝ)
  | 15 => (504243 / 500000000000 : ℝ)
  | 16 => (1051027 / 1000000000000 : ℝ)
  | 17 => (6843 / 6250000000 : ℝ)
  | 18 => (142509 / 125000000000 : ℝ)
  | 19 => (1186627 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch004Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (107379 / 200000000000 : ℝ)
  | 1 => (563631 / 1000000000000 : ℝ)
  | 2 => (591343 / 1000000000000 : ℝ)
  | 3 => (310027 / 500000000000 : ℝ)
  | 4 => (649787 / 1000000000000 : ℝ)
  | 5 => (170141 / 250000000000 : ℝ)
  | 6 => (712409 / 1000000000000 : ℝ)
  | 7 => (372673 / 500000000000 : ℝ)
  | 8 => (389699 / 500000000000 : ℝ)
  | 9 => (814589 / 1000000000000 : ℝ)
  | 10 => (850943 / 1000000000000 : ℝ)
  | 11 => (444243 / 500000000000 : ℝ)
  | 12 => (927241 / 1000000000000 : ℝ)
  | 13 => (967233 / 1000000000000 : ℝ)
  | 14 => (1008487 / 1000000000000 : ℝ)
  | 15 => (262757 / 250000000000 : ℝ)
  | 16 => (1094881 / 1000000000000 : ℝ)
  | 17 => (1140073 / 1000000000000 : ℝ)
  | 18 => (296657 / 250000000000 : ℝ)
  | 19 => (1234573 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch004Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((80 : ℝ) + (j.val : ℝ)) / 1600)
      (((80 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch004Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch004Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((80 : ℝ) + (j.val : ℝ)) / 1600)
    (((80 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch004Neg25WeightLower j.val) (hpThetaShiftTwoBatch004Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch004Neg25WeightLower, hpThetaShiftTwoBatch004Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch004Neg25_integral_bounds :
    (17590131 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (18569103 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (80 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch004Lower hpThetaJensenCellsBatch004Upper
    hpThetaShiftTwoBatch004Neg25WeightLower hpThetaShiftTwoBatch004Neg25WeightUpper hpThetaJensenCellsBatch004_bounds hpThetaShiftTwoBatch004Neg25_weight_bounds
  have hl : (17590131 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch004Lower j * hpThetaShiftTwoBatch004Neg25WeightLower j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftTwoBatch004Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftTwoBatch004Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch004Lower j * hpThetaShiftTwoBatch004Neg25WeightUpper j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftTwoBatch004Neg25WeightUpper j) / 1600) ≤ (18569103 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftTwoBatch004Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (80 : ℝ) / 1600 = 4 / 80 by norm_num,
    show ((80 : ℝ) + 20) / 1600 = (4 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch004Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch004Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch004Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch004Neg25_integral_bounds
end HodgeProofHP
