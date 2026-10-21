/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch008

/-! Exact signed weight and batch integral certificates, batch 8 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch008Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1329 / 200000000000 : ℝ)
  | 1 => (6877 / 1000000000000 : ℝ)
  | 2 => (1779 / 250000000000 : ℝ)
  | 3 => (7361 / 1000000000000 : ℝ)
  | 4 => (7613 / 1000000000000 : ℝ)
  | 5 => (7871 / 1000000000000 : ℝ)
  | 6 => (1017 / 125000000000 : ℝ)
  | 7 => (1051 / 125000000000 : ℝ)
  | 8 => (543 / 62500000000 : ℝ)
  | 9 => (4487 / 500000000000 : ℝ)
  | 10 => (9267 / 1000000000000 : ℝ)
  | 11 => (299 / 31250000000 : ℝ)
  | 12 => (2469 / 250000000000 : ℝ)
  | 13 => (637 / 62500000000 : ℝ)
  | 14 => (2629 / 250000000000 : ℝ)
  | 15 => (339 / 31250000000 : ℝ)
  | 16 => (11187 / 1000000000000 : ℝ)
  | 17 => (2307 / 200000000000 : ℝ)
  | 18 => (11891 / 1000000000000 : ℝ)
  | 19 => (2451 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch008Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3439 / 500000000000 : ℝ)
  | 1 => (7117 / 1000000000000 : ℝ)
  | 2 => (3681 / 500000000000 : ℝ)
  | 3 => (3807 / 500000000000 : ℝ)
  | 4 => (123 / 15625000000 : ℝ)
  | 5 => (8137 / 1000000000000 : ℝ)
  | 6 => (8409 / 1000000000000 : ℝ)
  | 7 => (8689 / 1000000000000 : ℝ)
  | 8 => (359 / 40000000000 : ℝ)
  | 9 => (2317 / 250000000000 : ℝ)
  | 10 => (9569 / 1000000000000 : ℝ)
  | 11 => (9877 / 1000000000000 : ℝ)
  | 12 => (10193 / 1000000000000 : ℝ)
  | 13 => (10517 / 1000000000000 : ℝ)
  | 14 => (10849 / 1000000000000 : ℝ)
  | 15 => (2797 / 250000000000 : ℝ)
  | 16 => (721 / 62500000000 : ℝ)
  | 17 => (2973 / 250000000000 : ℝ)
  | 18 => (383 / 31250000000 : ℝ)
  | 19 => (12629 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch008Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((160 : ℝ) + (j.val : ℝ)) / 1600)
      (((160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch008Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch008Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((160 : ℝ) + (j.val : ℝ)) / 1600)
    (((160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch008Neg100WeightLower j.val) (hpThetaShiftThreeBatch008Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch008Neg100WeightLower, hpThetaShiftThreeBatch008Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch008Neg100_integral_bounds :
    (184469 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (48147 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch008Lower hpThetaJensenCellsBatch008Upper
    hpThetaShiftThreeBatch008Neg100WeightLower hpThetaShiftThreeBatch008Neg100WeightUpper hpThetaJensenCellsBatch008_bounds hpThetaShiftThreeBatch008Neg100_weight_bounds
  have hl : (184469 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch008Lower j * hpThetaShiftThreeBatch008Neg100WeightLower j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftThreeBatch008Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftThreeBatch008Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch008Lower j * hpThetaShiftThreeBatch008Neg100WeightUpper j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftThreeBatch008Neg100WeightUpper j) / 1600) ≤ (48147 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftThreeBatch008Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (160 : ℝ) / 1600 = 8 / 80 by norm_num,
    show ((160 : ℝ) + 20) / 1600 = (8 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch008Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (7131 / 1000000000000 : ℝ)
  | 1 => (1847 / 250000000000 : ℝ)
  | 2 => (1913 / 250000000000 : ℝ)
  | 3 => (7923 / 1000000000000 : ℝ)
  | 4 => (4101 / 500000000000 : ℝ)
  | 5 => (8489 / 1000000000000 : ℝ)
  | 6 => (549 / 62500000000 : ℝ)
  | 7 => (9087 / 1000000000000 : ℝ)
  | 8 => (4699 / 500000000000 : ℝ)
  | 9 => (4859 / 500000000000 : ℝ)
  | 10 => (10047 / 1000000000000 : ℝ)
  | 11 => (649 / 62500000000 : ℝ)
  | 12 => (1073 / 100000000000 : ℝ)
  | 13 => (2217 / 200000000000 : ℝ)
  | 14 => (229 / 20000000000 : ℝ)
  | 15 => (739 / 62500000000 : ℝ)
  | 16 => (12207 / 1000000000000 : ℝ)
  | 17 => (12601 / 1000000000000 : ℝ)
  | 18 => (3251 / 250000000000 : ℝ)
  | 19 => (6709 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch008Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (7389 / 1000000000000 : ℝ)
  | 1 => (7653 / 1000000000000 : ℝ)
  | 2 => (1981 / 250000000000 : ℝ)
  | 3 => (8203 / 1000000000000 : ℝ)
  | 4 => (849 / 100000000000 : ℝ)
  | 5 => (1757 / 200000000000 : ℝ)
  | 6 => (71 / 7812500000 : ℝ)
  | 7 => (9399 / 1000000000000 : ℝ)
  | 8 => (9719 / 1000000000000 : ℝ)
  | 9 => (157 / 15625000000 : ℝ)
  | 10 => (2077 / 200000000000 : ℝ)
  | 11 => (10731 / 1000000000000 : ℝ)
  | 12 => (5543 / 500000000000 : ℝ)
  | 13 => (11451 / 1000000000000 : ℝ)
  | 14 => (473 / 40000000000 : ℝ)
  | 15 => (763 / 62500000000 : ℝ)
  | 16 => (6301 / 500000000000 : ℝ)
  | 17 => (2601 / 200000000000 : ℝ)
  | 18 => (13419 / 1000000000000 : ℝ)
  | 19 => (13843 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch008Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((160 : ℝ) + (j.val : ℝ)) / 1600)
      (((160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch008Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch008Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((160 : ℝ) + (j.val : ℝ)) / 1600)
    (((160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch008Neg70WeightLower j.val) (hpThetaShiftThreeBatch008Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch008Neg70WeightLower, hpThetaShiftThreeBatch008Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch008Neg70_integral_bounds :
    (200129 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (52289 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch008Lower hpThetaJensenCellsBatch008Upper
    hpThetaShiftThreeBatch008Neg70WeightLower hpThetaShiftThreeBatch008Neg70WeightUpper hpThetaJensenCellsBatch008_bounds hpThetaShiftThreeBatch008Neg70_weight_bounds
  have hl : (200129 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch008Lower j * hpThetaShiftThreeBatch008Neg70WeightLower j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftThreeBatch008Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftThreeBatch008Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch008Lower j * hpThetaShiftThreeBatch008Neg70WeightUpper j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftThreeBatch008Neg70WeightUpper j) / 1600) ≤ (52289 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftThreeBatch008Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (160 : ℝ) / 1600 = 8 / 80 by norm_num,
    show ((160 : ℝ) + 20) / 1600 = (8 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch008Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (7549 / 1000000000000 : ℝ)
  | 1 => (7827 / 1000000000000 : ℝ)
  | 2 => (8113 / 1000000000000 : ℝ)
  | 3 => (8407 / 1000000000000 : ℝ)
  | 4 => (871 / 100000000000 : ℝ)
  | 5 => (4511 / 500000000000 : ℝ)
  | 6 => (9343 / 1000000000000 : ℝ)
  | 7 => (9673 / 1000000000000 : ℝ)
  | 8 => (2503 / 250000000000 : ℝ)
  | 9 => (10361 / 1000000000000 : ℝ)
  | 10 => (67 / 6250000000 : ℝ)
  | 11 => (11089 / 1000000000000 : ℝ)
  | 12 => (2867 / 250000000000 : ℝ)
  | 13 => (5929 / 500000000000 : ℝ)
  | 14 => (6129 / 500000000000 : ℝ)
  | 15 => (12669 / 1000000000000 : ℝ)
  | 16 => (3273 / 250000000000 : ℝ)
  | 17 => (541 / 40000000000 : ℝ)
  | 18 => (1397 / 100000000000 : ℝ)
  | 19 => (14427 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch008Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1957 / 250000000000 : ℝ)
  | 1 => (4057 / 500000000000 : ℝ)
  | 2 => (1051 / 125000000000 : ℝ)
  | 3 => (8711 / 1000000000000 : ℝ)
  | 4 => (9023 / 1000000000000 : ℝ)
  | 5 => (73 / 7812500000 : ℝ)
  | 6 => (4837 / 500000000000 : ℝ)
  | 7 => (10013 / 1000000000000 : ℝ)
  | 8 => (5181 / 500000000000 : ℝ)
  | 9 => (10721 / 1000000000000 : ℝ)
  | 10 => (1109 / 100000000000 : ℝ)
  | 11 => (11469 / 1000000000000 : ℝ)
  | 12 => (11859 / 1000000000000 : ℝ)
  | 13 => (12259 / 1000000000000 : ℝ)
  | 14 => (1267 / 100000000000 : ℝ)
  | 15 => (13093 / 1000000000000 : ℝ)
  | 16 => (6763 / 500000000000 : ℝ)
  | 17 => (13971 / 1000000000000 : ℝ)
  | 18 => (3607 / 250000000000 : ℝ)
  | 19 => (14897 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch008Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((160 : ℝ) + (j.val : ℝ)) / 1600)
      (((160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch008Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch008Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((160 : ℝ) + (j.val : ℝ)) / 1600)
    (((160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch008Neg45WeightLower j.val) (hpThetaShiftThreeBatch008Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch008Neg45WeightLower, hpThetaShiftThreeBatch008Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch008Neg45_integral_bounds :
    (106833 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (111743 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch008Lower hpThetaJensenCellsBatch008Upper
    hpThetaShiftThreeBatch008Neg45WeightLower hpThetaShiftThreeBatch008Neg45WeightUpper hpThetaJensenCellsBatch008_bounds hpThetaShiftThreeBatch008Neg45_weight_bounds
  have hl : (106833 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch008Lower j * hpThetaShiftThreeBatch008Neg45WeightLower j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftThreeBatch008Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftThreeBatch008Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch008Lower j * hpThetaShiftThreeBatch008Neg45WeightUpper j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftThreeBatch008Neg45WeightUpper j) / 1600) ≤ (111743 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftThreeBatch008Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (160 : ℝ) / 1600 = 8 / 80 by norm_num,
    show ((160 : ℝ) + 20) / 1600 = (8 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch008Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (7893 / 1000000000000 : ℝ)
  | 1 => (2047 / 250000000000 : ℝ)
  | 2 => (2123 / 250000000000 : ℝ)
  | 3 => (1761 / 200000000000 : ℝ)
  | 4 => (1141 / 125000000000 : ℝ)
  | 5 => (473 / 50000000000 : ℝ)
  | 6 => (4901 / 500000000000 : ℝ)
  | 7 => (2031 / 200000000000 : ℝ)
  | 8 => (10517 / 1000000000000 : ℝ)
  | 9 => (10891 / 1000000000000 : ℝ)
  | 10 => (451 / 40000000000 : ℝ)
  | 11 => (1167 / 100000000000 : ℝ)
  | 12 => (12077 / 1000000000000 : ℝ)
  | 13 => (2499 / 200000000000 : ℝ)
  | 14 => (517 / 40000000000 : ℝ)
  | 15 => (13367 / 1000000000000 : ℝ)
  | 16 => (6911 / 500000000000 : ℝ)
  | 17 => (14289 / 1000000000000 : ℝ)
  | 18 => (14769 / 1000000000000 : ℝ)
  | 19 => (7631 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch008Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (8189 / 1000000000000 : ℝ)
  | 1 => (8493 / 1000000000000 : ℝ)
  | 2 => (4403 / 500000000000 : ℝ)
  | 3 => (9129 / 1000000000000 : ℝ)
  | 4 => (9461 / 1000000000000 : ℝ)
  | 5 => (9803 / 1000000000000 : ℝ)
  | 6 => (2539 / 250000000000 : ℝ)
  | 7 => (5259 / 500000000000 : ℝ)
  | 8 => (2723 / 250000000000 : ℝ)
  | 9 => (2819 / 250000000000 : ℝ)
  | 10 => (11671 / 1000000000000 : ℝ)
  | 11 => (6039 / 500000000000 : ℝ)
  | 12 => (781 / 62500000000 : ℝ)
  | 13 => (6463 / 500000000000 : ℝ)
  | 14 => (1671 / 125000000000 : ℝ)
  | 15 => (13823 / 1000000000000 : ℝ)
  | 16 => (1429 / 100000000000 : ℝ)
  | 17 => (1477 / 100000000000 : ℝ)
  | 18 => (15263 / 1000000000000 : ℝ)
  | 19 => (15769 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch008Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((160 : ℝ) + (j.val : ℝ)) / 1600)
      (((160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch008Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch008Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((160 : ℝ) + (j.val : ℝ)) / 1600)
    (((160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch008Neg25WeightLower j.val) (hpThetaShiftThreeBatch008Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch008Neg25WeightLower, hpThetaShiftThreeBatch008Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch008Neg25_integral_bounds :
    (224827 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (8 / 80 : ℝ) ((8 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (47061 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch008Lower hpThetaJensenCellsBatch008Upper
    hpThetaShiftThreeBatch008Neg25WeightLower hpThetaShiftThreeBatch008Neg25WeightUpper hpThetaJensenCellsBatch008_bounds hpThetaShiftThreeBatch008Neg25_weight_bounds
  have hl : (224827 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch008Lower j * hpThetaShiftThreeBatch008Neg25WeightLower j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftThreeBatch008Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftThreeBatch008Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch008Lower j * hpThetaShiftThreeBatch008Neg25WeightUpper j)
        (hpThetaJensenCellsBatch008Upper j * hpThetaShiftThreeBatch008Neg25WeightUpper j) / 1600) ≤ (47061 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch008Lower, hpThetaJensenCellsBatch008Upper,
      hpThetaShiftThreeBatch008Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (160 : ℝ) / 1600 = 8 / 80 by norm_num,
    show ((160 : ℝ) + 20) / 1600 = (8 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch008Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch008Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch008Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch008Neg25_integral_bounds
end HodgeProofHP
