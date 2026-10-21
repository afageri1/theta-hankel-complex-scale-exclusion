/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch047

/-! Exact signed weight and batch integral certificates, batch 47 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch047Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (126417807 / 1000000000000 : ℝ)
  | 1 => (15779941 / 125000000000 : ℝ)
  | 2 => (126025959 / 1000000000000 : ℝ)
  | 3 => (15722033 / 125000000000 : ℝ)
  | 4 => (125489597 / 1000000000000 : ℝ)
  | 5 => (125165097 / 1000000000000 : ℝ)
  | 6 => (124801891 / 1000000000000 : ℝ)
  | 7 => (124399091 / 1000000000000 : ℝ)
  | 8 => (123955797 / 1000000000000 : ℝ)
  | 9 => (61735547 / 500000000000 : ℝ)
  | 10 => (30736013 / 250000000000 : ℝ)
  | 11 => (12237373 / 100000000000 : ℝ)
  | 12 => (12175917 / 100000000000 : ℝ)
  | 13 => (121099399 / 1000000000000 : ℝ)
  | 14 => (120393431 / 1000000000000 : ℝ)
  | 15 => (59820133 / 500000000000 : ℝ)
  | 16 => (59419443 / 500000000000 : ℝ)
  | 17 => (5899413 / 50000000000 : ℝ)
  | 18 => (5854367 / 50000000000 : ℝ)
  | 19 => (14516883 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch047Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (7910101 / 62500000000 : ℝ)
  | 1 => (7901113 / 62500000000 : ℝ)
  | 2 => (126239529 / 1000000000000 : ℝ)
  | 3 => (3150649 / 25000000000 : ℝ)
  | 4 => (25155253 / 200000000000 : ℝ)
  | 5 => (62744799 / 500000000000 : ℝ)
  | 6 => (62582549 / 500000000000 : ℝ)
  | 7 => (31200473 / 250000000000 : ℝ)
  | 8 => (31099773 / 250000000000 : ℝ)
  | 9 => (61977899 / 500000000000 : ℝ)
  | 10 => (24694219 / 200000000000 : ℝ)
  | 11 => (122944053 / 1000000000000 : ℝ)
  | 12 => (122373731 / 1000000000000 : ℝ)
  | 13 => (121759171 / 1000000000000 : ℝ)
  | 14 => (605497 / 5000000000 : ℝ)
  | 15 => (15049179 / 125000000000 : ℝ)
  | 16 => (119640267 / 1000000000000 : ℝ)
  | 17 => (118838887 / 1000000000000 : ℝ)
  | 18 => (117988261 / 1000000000000 : ℝ)
  | 19 => (117087341 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch047Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((940 : ℝ) + (j.val : ℝ)) / 1600)
      (((940 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch047Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch047Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((940 : ℝ) + (j.val : ℝ)) / 1600)
    (((940 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch047Neg100WeightLower j.val) (hpThetaShiftThreeBatch047Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch047Neg100WeightLower, hpThetaShiftThreeBatch047Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch047Neg100_integral_bounds :
    (49957261 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (25551023 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (940 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch047Lower hpThetaJensenCellsBatch047Upper
    hpThetaShiftThreeBatch047Neg100WeightLower hpThetaShiftThreeBatch047Neg100WeightUpper hpThetaJensenCellsBatch047_bounds hpThetaShiftThreeBatch047Neg100_weight_bounds
  have hl : (49957261 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch047Lower j * hpThetaShiftThreeBatch047Neg100WeightLower j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftThreeBatch047Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftThreeBatch047Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch047Lower j * hpThetaShiftThreeBatch047Neg100WeightUpper j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftThreeBatch047Neg100WeightUpper j) / 1600) ≤ (25551023 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftThreeBatch047Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (940 : ℝ) / 1600 = 47 / 80 by norm_num,
    show ((940 : ℝ) + 20) / 1600 = (47 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch047Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (78149481 / 1000000000000 : ℝ)
  | 1 => (79448367 / 1000000000000 : ℝ)
  | 2 => (39433 / 488281250 : ℝ)
  | 3 => (41040369 / 500000000000 : ℝ)
  | 4 => (83414239 / 1000000000000 : ℝ)
  | 5 => (8475929 / 100000000000 : ℝ)
  | 6 => (43057947 / 500000000000 : ℝ)
  | 7 => (43742027 / 500000000000 : ℝ)
  | 8 => (8886377 / 100000000000 : ℝ)
  | 9 => (90255039 / 1000000000000 : ℝ)
  | 10 => (45828929 / 500000000000 : ℝ)
  | 11 => (93072221 / 1000000000000 : ℝ)
  | 12 => (47249061 / 500000000000 : ℝ)
  | 13 => (1918711 / 20000000000 : ℝ)
  | 14 => (19476899 / 200000000000 : ℝ)
  | 15 => (98844943 / 1000000000000 : ℝ)
  | 16 => (100316879 / 1000000000000 : ℝ)
  | 17 => (50900143 / 500000000000 : ℝ)
  | 18 => (12911893 / 125000000000 : ℝ)
  | 19 => (13100179 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch047Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (4965523 / 62500000000 : ℝ)
  | 1 => (16151757 / 200000000000 : ℝ)
  | 2 => (82080739 / 1000000000000 : ℝ)
  | 3 => (521339 / 6250000000 : ℝ)
  | 4 => (84759291 / 1000000000000 : ℝ)
  | 5 => (17223179 / 200000000000 : ℝ)
  | 6 => (17496811 / 200000000000 : ℝ)
  | 7 => (88863771 / 1000000000000 : ℝ)
  | 8 => (282047 / 3125000000 : ℝ)
  | 9 => (91657859 / 1000000000000 : ℝ)
  | 10 => (46536111 / 500000000000 : ℝ)
  | 11 => (94498123 / 1000000000000 : ℝ)
  | 12 => (95935551 / 1000000000000 : ℝ)
  | 13 => (6086531 / 62500000000 : ℝ)
  | 14 => (6177809 / 62500000000 : ℝ)
  | 15 => (1253961 / 12500000000 : ℝ)
  | 16 => (101800287 / 1000000000000 : ℝ)
  | 17 => (20659029 / 200000000000 : ℝ)
  | 18 => (104801433 / 1000000000000 : ℝ)
  | 19 => (13289891 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch047Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((940 : ℝ) + (j.val : ℝ)) / 1600)
      (((940 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch047Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch047Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((940 : ℝ) + (j.val : ℝ)) / 1600)
    (((940 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch047Neg70WeightLower j.val) (hpThetaShiftThreeBatch047Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch047Neg70WeightLower, hpThetaShiftThreeBatch047Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch047Neg70_integral_bounds :
    (738619 / 20000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (4775593 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (940 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch047Lower hpThetaJensenCellsBatch047Upper
    hpThetaShiftThreeBatch047Neg70WeightLower hpThetaShiftThreeBatch047Neg70WeightUpper hpThetaJensenCellsBatch047_bounds hpThetaShiftThreeBatch047Neg70_weight_bounds
  have hl : (738619 / 20000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch047Lower j * hpThetaShiftThreeBatch047Neg70WeightLower j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftThreeBatch047Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftThreeBatch047Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch047Lower j * hpThetaShiftThreeBatch047Neg70WeightUpper j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftThreeBatch047Neg70WeightUpper j) / 1600) ≤ (4775593 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftThreeBatch047Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (940 : ℝ) / 1600 = 47 / 80 by norm_num,
    show ((940 : ℝ) + 20) / 1600 = (47 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch047Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-45306283 / 1000000000000 : ℝ)
  | 1 => (-566331 / 12500000000 : ℝ)
  | 2 => (-22652493 / 500000000000 : ℝ)
  | 3 => (-11324637 / 250000000000 : ℝ)
  | 4 => (-9057379 / 200000000000 : ℝ)
  | 5 => (-905399 / 20000000000 : ℝ)
  | 6 => (-1131191 / 25000000000 : ℝ)
  | 7 => (-45219887 / 1000000000000 : ℝ)
  | 8 => (-5648327 / 125000000000 : ℝ)
  | 9 => (-11286937 / 250000000000 : ℝ)
  | 10 => (-22551603 / 500000000000 : ℝ)
  | 11 => (-2815807 / 62500000000 : ℝ)
  | 12 => (-11249197 / 250000000000 : ℝ)
  | 13 => (-44934753 / 1000000000000 : ℝ)
  | 14 => (-5608341 / 125000000000 : ℝ)
  | 15 => (-44792633 / 1000000000000 : ℝ)
  | 16 => (-22356193 / 500000000000 : ℝ)
  | 17 => (-44625907 / 1000000000000 : ℝ)
  | 18 => (-44533113 / 1000000000000 : ℝ)
  | 19 => (-22216961 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch047Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-45302511 / 1000000000000 : ℝ)
  | 1 => (-9060997 / 200000000000 : ℝ)
  | 2 => (-45298547 / 1000000000000 : ℝ)
  | 3 => (-22643447 / 500000000000 : ℝ)
  | 4 => (-45269949 / 1000000000000 : ℝ)
  | 5 => (-45247639 / 1000000000000 : ℝ)
  | 6 => (-22609943 / 500000000000 : ℝ)
  | 7 => (-9037323 / 200000000000 : ℝ)
  | 8 => (-45147747 / 1000000000000 : ℝ)
  | 9 => (-9020641 / 200000000000 : ℝ)
  | 10 => (-45052911 / 1000000000000 : ℝ)
  | 11 => (-44996787 / 1000000000000 : ℝ)
  | 12 => (-1404211 / 31250000000 : ℝ)
  | 13 => (-44866727 / 1000000000000 : ℝ)
  | 14 => (-5599079 / 125000000000 : ℝ)
  | 15 => (-8942477 / 200000000000 : ℝ)
  | 16 => (-22312953 / 500000000000 : ℝ)
  | 17 => (-5566639 / 125000000000 : ℝ)
  | 18 => (-44433921 / 1000000000000 : ℝ)
  | 19 => (-44328249 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch047Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((940 : ℝ) + (j.val : ℝ)) / 1600)
      (((940 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch047Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch047Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((940 : ℝ) + (j.val : ℝ)) / 1600)
    (((940 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch047Neg45WeightLower j.val) (hpThetaShiftThreeBatch047Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch047Neg45WeightLower, hpThetaShiftThreeBatch047Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch047Neg45_integral_bounds :
    (-4671837 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-18325009 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (940 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch047Lower hpThetaJensenCellsBatch047Upper
    hpThetaShiftThreeBatch047Neg45WeightLower hpThetaShiftThreeBatch047Neg45WeightUpper hpThetaJensenCellsBatch047_bounds hpThetaShiftThreeBatch047Neg45_weight_bounds
  have hl : (-4671837 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch047Lower j * hpThetaShiftThreeBatch047Neg45WeightLower j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftThreeBatch047Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftThreeBatch047Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch047Lower j * hpThetaShiftThreeBatch047Neg45WeightUpper j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftThreeBatch047Neg45WeightUpper j) / 1600) ≤ (-18325009 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftThreeBatch047Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (940 : ℝ) / 1600 = 47 / 80 by norm_num,
    show ((940 : ℝ) + 20) / 1600 = (47 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch047Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1095753 / 40000000000 : ℝ)
  | 1 => (-1393997 / 50000000000 : ℝ)
  | 2 => (-5673917 / 200000000000 : ℝ)
  | 3 => (-5772553 / 200000000000 : ℝ)
  | 4 => (-29359487 / 1000000000000 : ℝ)
  | 5 => (-29859757 / 1000000000000 : ℝ)
  | 6 => (-30363581 / 1000000000000 : ℝ)
  | 7 => (-30870963 / 1000000000000 : ℝ)
  | 8 => (-3138191 / 100000000000 : ℝ)
  | 9 => (-15948213 / 500000000000 : ℝ)
  | 10 => (-16207259 / 500000000000 : ℝ)
  | 11 => (-32936189 / 1000000000000 : ℝ)
  | 12 => (-8365361 / 250000000000 : ℝ)
  | 13 => (-33990289 / 1000000000000 : ℝ)
  | 14 => (-34522727 / 1000000000000 : ℝ)
  | 15 => (-35058763 / 1000000000000 : ℝ)
  | 16 => (-35598401 / 1000000000000 : ℝ)
  | 17 => (-9035411 / 250000000000 : ℝ)
  | 18 => (-2293031 / 62500000000 : ℝ)
  | 19 => (-18619481 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch047Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-26911231 / 1000000000000 : ℝ)
  | 1 => (-856057 / 31250000000 : ℝ)
  | 2 => (-27879939 / 1000000000000 : ℝ)
  | 3 => (-1773099 / 62500000000 : ℝ)
  | 4 => (-7215691 / 250000000000 : ℝ)
  | 5 => (-14679743 / 500000000000 : ℝ)
  | 6 => (-7464939 / 250000000000 : ℝ)
  | 7 => (-1518179 / 50000000000 : ℝ)
  | 8 => (-15435481 / 500000000000 : ℝ)
  | 9 => (-31381909 / 1000000000000 : ℝ)
  | 10 => (-1275857 / 40000000000 : ℝ)
  | 11 => (-32414517 / 1000000000000 : ℝ)
  | 12 => (-8234047 / 250000000000 : ℝ)
  | 13 => (-33461443 / 1000000000000 : ℝ)
  | 14 => (-2124393 / 62500000000 : ℝ)
  | 15 => (-17261363 / 500000000000 : ℝ)
  | 16 => (-17529381 / 500000000000 : ℝ)
  | 17 => (-22249 / 625000000 : ℝ)
  | 18 => (-36141643 / 1000000000000 : ℝ)
  | 19 => (-7337699 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch047Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((940 : ℝ) + (j.val : ℝ)) / 1600)
      (((940 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch047Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch047Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((940 : ℝ) + (j.val : ℝ)) / 1600)
    (((940 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch047Neg25WeightLower j.val) (hpThetaShiftThreeBatch047Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch047Neg25WeightLower, hpThetaShiftThreeBatch047Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch047Neg25_integral_bounds :
    (-13293897 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-12839893 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (940 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch047Lower hpThetaJensenCellsBatch047Upper
    hpThetaShiftThreeBatch047Neg25WeightLower hpThetaShiftThreeBatch047Neg25WeightUpper hpThetaJensenCellsBatch047_bounds hpThetaShiftThreeBatch047Neg25_weight_bounds
  have hl : (-13293897 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch047Lower j * hpThetaShiftThreeBatch047Neg25WeightLower j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftThreeBatch047Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftThreeBatch047Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch047Lower j * hpThetaShiftThreeBatch047Neg25WeightUpper j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftThreeBatch047Neg25WeightUpper j) / 1600) ≤ (-12839893 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftThreeBatch047Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (940 : ℝ) / 1600 = 47 / 80 by norm_num,
    show ((940 : ℝ) + 20) / 1600 = (47 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch047Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch047Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch047Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch047Neg25_integral_bounds
end HodgeProofHP
