/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch015

/-! Exact signed weight and batch integral certificates, batch 15 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch015Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (17469 / 125000000000 : ℝ)
  | 1 => (70691 / 500000000000 : ℝ)
  | 2 => (35753 / 250000000000 : ℝ)
  | 3 => (144641 / 1000000000000 : ℝ)
  | 4 => (36567 / 250000000000 : ℝ)
  | 5 => (147893 / 1000000000000 : ℝ)
  | 6 => (37379 / 250000000000 : ℝ)
  | 7 => (30227 / 200000000000 : ℝ)
  | 8 => (152751 / 1000000000000 : ℝ)
  | 9 => (77181 / 500000000000 : ℝ)
  | 10 => (155969 / 1000000000000 : ℝ)
  | 11 => (157569 / 1000000000000 : ℝ)
  | 12 => (39791 / 250000000000 : ℝ)
  | 13 => (10047 / 62500000000 : ℝ)
  | 14 => (162333 / 1000000000000 : ℝ)
  | 15 => (32781 / 200000000000 : ℝ)
  | 16 => (165469 / 1000000000000 : ℝ)
  | 17 => (167023 / 1000000000000 : ℝ)
  | 18 => (84283 / 500000000000 : ℝ)
  | 19 => (170099 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch015Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (141383 / 1000000000000 : ℝ)
  | 1 => (143013 / 1000000000000 : ℝ)
  | 2 => (72321 / 500000000000 : ℝ)
  | 3 => (146269 / 1000000000000 : ℝ)
  | 4 => (73947 / 500000000000 : ℝ)
  | 5 => (149517 / 1000000000000 : ℝ)
  | 6 => (4723 / 31250000000 : ℝ)
  | 7 => (9547 / 62500000000 : ℝ)
  | 8 => (154363 / 1000000000000 : ℝ)
  | 9 => (15597 / 100000000000 : ℝ)
  | 10 => (15757 / 100000000000 : ℝ)
  | 11 => (31833 / 200000000000 : ℝ)
  | 12 => (160753 / 1000000000000 : ℝ)
  | 13 => (81167 / 500000000000 : ℝ)
  | 14 => (81953 / 500000000000 : ℝ)
  | 15 => (16547 / 100000000000 : ℝ)
  | 16 => (10439 / 62500000000 : ℝ)
  | 17 => (168567 / 1000000000000 : ℝ)
  | 18 => (1701 / 10000000000 : ℝ)
  | 19 => (171621 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch015Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((300 : ℝ) + (j.val : ℝ)) / 1600)
      (((300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch015Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch015Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((300 : ℝ) + (j.val : ℝ)) / 1600)
    (((300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch015Neg100WeightLower j.val) (hpThetaShiftThreeBatch015Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch015Neg100WeightLower, hpThetaShiftThreeBatch015Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch015Neg100_integral_bounds :
    (2403797 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (614361 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch015Lower hpThetaJensenCellsBatch015Upper
    hpThetaShiftThreeBatch015Neg100WeightLower hpThetaShiftThreeBatch015Neg100WeightUpper hpThetaJensenCellsBatch015_bounds hpThetaShiftThreeBatch015Neg100_weight_bounds
  have hl : (2403797 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch015Lower j * hpThetaShiftThreeBatch015Neg100WeightLower j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftThreeBatch015Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftThreeBatch015Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch015Lower j * hpThetaShiftThreeBatch015Neg100WeightUpper j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftThreeBatch015Neg100WeightUpper j) / 1600) ≤ (614361 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftThreeBatch015Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (300 : ℝ) / 1600 = 15 / 80 by norm_num,
    show ((300 : ℝ) + 20) / 1600 = (15 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch015Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (196281 / 1000000000000 : ℝ)
  | 1 => (7971 / 40000000000 : ℝ)
  | 2 => (25287 / 125000000000 : ℝ)
  | 3 => (205343 / 1000000000000 : ℝ)
  | 4 => (208417 / 1000000000000 : ℝ)
  | 5 => (52879 / 250000000000 : ℝ)
  | 6 => (214641 / 1000000000000 : ℝ)
  | 7 => (3403 / 15625000000 : ℝ)
  | 8 => (220969 / 1000000000000 : ℝ)
  | 9 => (224171 / 1000000000000 : ℝ)
  | 10 => (113699 / 500000000000 : ℝ)
  | 11 => (4613 / 20000000000 : ℝ)
  | 12 => (116963 / 500000000000 : ℝ)
  | 13 => (237227 / 1000000000000 : ℝ)
  | 14 => (240553 / 1000000000000 : ℝ)
  | 15 => (121951 / 500000000000 : ℝ)
  | 16 => (9891 / 40000000000 : ℝ)
  | 17 => (250671 / 1000000000000 : ℝ)
  | 18 => (254091 / 1000000000000 : ℝ)
  | 19 => (128767 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch015Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (49819 / 250000000000 : ℝ)
  | 1 => (202297 / 1000000000000 : ℝ)
  | 2 => (6417 / 31250000000 : ℝ)
  | 3 => (104209 / 500000000000 : ℝ)
  | 4 => (211517 / 1000000000000 : ℝ)
  | 5 => (107321 / 500000000000 : ℝ)
  | 6 => (217793 / 1000000000000 : ℝ)
  | 7 => (22097 / 100000000000 : ℝ)
  | 8 => (56043 / 250000000000 : ℝ)
  | 9 => (227399 / 1000000000000 : ℝ)
  | 10 => (230651 / 1000000000000 : ℝ)
  | 11 => (233927 / 1000000000000 : ℝ)
  | 12 => (59307 / 250000000000 : ℝ)
  | 13 => (120277 / 500000000000 : ℝ)
  | 14 => (243903 / 1000000000000 : ℝ)
  | 15 => (61819 / 250000000000 : ℝ)
  | 16 => (15667 / 62500000000 : ℝ)
  | 17 => (63523 / 250000000000 : ℝ)
  | 18 => (51507 / 200000000000 : ℝ)
  | 19 => (261 / 1000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch015Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((300 : ℝ) + (j.val : ℝ)) / 1600)
      (((300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch015Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch015Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((300 : ℝ) + (j.val : ℝ)) / 1600)
    (((300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch015Neg70WeightLower j.val) (hpThetaShiftThreeBatch015Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch015Neg70WeightLower, hpThetaShiftThreeBatch015Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch015Neg70_integral_bounds :
    (87627 / 25000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (1798791 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch015Lower hpThetaJensenCellsBatch015Upper
    hpThetaShiftThreeBatch015Neg70WeightLower hpThetaShiftThreeBatch015Neg70WeightUpper hpThetaJensenCellsBatch015_bounds hpThetaShiftThreeBatch015Neg70_weight_bounds
  have hl : (87627 / 25000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch015Lower j * hpThetaShiftThreeBatch015Neg70WeightLower j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftThreeBatch015Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftThreeBatch015Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch015Lower j * hpThetaShiftThreeBatch015Neg70WeightUpper j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftThreeBatch015Neg70WeightUpper j) / 1600) ≤ (1798791 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftThreeBatch015Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (300 : ℝ) / 1600 = 15 / 80 by norm_num,
    show ((300 : ℝ) + 20) / 1600 = (15 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch015Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (124937 / 500000000000 : ℝ)
  | 1 => (12711 / 50000000000 : ℝ)
  | 2 => (12931 / 50000000000 : ℝ)
  | 3 => (65769 / 250000000000 : ℝ)
  | 4 => (267587 / 1000000000000 : ℝ)
  | 5 => (54431 / 200000000000 : ℝ)
  | 6 => (276779 / 1000000000000 : ℝ)
  | 7 => (14073 / 50000000000 : ℝ)
  | 8 => (143099 / 500000000000 : ℝ)
  | 9 => (145497 / 500000000000 : ℝ)
  | 10 => (295847 / 1000000000000 : ℝ)
  | 11 => (300759 / 1000000000000 : ℝ)
  | 12 => (4777 / 15625000000 : ℝ)
  | 13 => (310757 / 1000000000000 : ℝ)
  | 14 => (63169 / 200000000000 : ℝ)
  | 15 => (10031 / 31250000000 : ℝ)
  | 16 => (326199 / 1000000000000 : ℝ)
  | 17 => (165733 / 500000000000 : ℝ)
  | 18 => (336793 / 1000000000000 : ℝ)
  | 19 => (17109 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch015Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (254221 / 1000000000000 : ℝ)
  | 1 => (258621 / 1000000000000 : ℝ)
  | 2 => (263077 / 1000000000000 : ℝ)
  | 3 => (66897 / 250000000000 : ℝ)
  | 4 => (68039 / 250000000000 : ℝ)
  | 5 => (13839 / 50000000000 : ℝ)
  | 6 => (281461 / 1000000000000 : ℝ)
  | 7 => (286199 / 1000000000000 : ℝ)
  | 8 => (58199 / 200000000000 : ℝ)
  | 9 => (36981 / 125000000000 : ℝ)
  | 10 => (7519 / 25000000000 : ℝ)
  | 11 => (305729 / 1000000000000 : ℝ)
  | 12 => (155379 / 500000000000 : ℝ)
  | 13 => (157923 / 500000000000 : ℝ)
  | 14 => (320993 / 1000000000000 : ℝ)
  | 15 => (1631 / 5000000000 : ℝ)
  | 16 => (331467 / 1000000000000 : ℝ)
  | 17 => (168397 / 500000000000 : ℝ)
  | 18 => (342181 / 1000000000000 : ℝ)
  | 19 => (34763 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch015Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((300 : ℝ) + (j.val : ℝ)) / 1600)
      (((300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch015Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch015Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((300 : ℝ) + (j.val : ℝ)) / 1600)
    (((300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch015Neg45WeightLower j.val) (hpThetaShiftThreeBatch015Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch015Neg45WeightLower, hpThetaShiftThreeBatch015Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch015Neg45_integral_bounds :
    (4560771 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (4691731 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch015Lower hpThetaJensenCellsBatch015Upper
    hpThetaShiftThreeBatch015Neg45WeightLower hpThetaShiftThreeBatch015Neg45WeightUpper hpThetaJensenCellsBatch015_bounds hpThetaShiftThreeBatch015Neg45_weight_bounds
  have hl : (4560771 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch015Lower j * hpThetaShiftThreeBatch015Neg45WeightLower j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftThreeBatch015Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftThreeBatch015Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch015Lower j * hpThetaShiftThreeBatch015Neg45WeightUpper j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftThreeBatch015Neg45WeightUpper j) / 1600) ≤ (4691731 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftThreeBatch015Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (300 : ℝ) / 1600 = 15 / 80 by norm_num,
    show ((300 : ℝ) + 20) / 1600 = (15 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch015Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (297187 / 1000000000000 : ℝ)
  | 1 => (7569 / 25000000000 : ℝ)
  | 2 => (4819 / 15625000000 : ℝ)
  | 3 => (62831 / 200000000000 : ℝ)
  | 4 => (319979 / 1000000000000 : ℝ)
  | 5 => (325887 / 1000000000000 : ℝ)
  | 6 => (331881 / 1000000000000 : ℝ)
  | 7 => (337961 / 1000000000000 : ℝ)
  | 8 => (34413 / 100000000000 : ℝ)
  | 9 => (175193 / 500000000000 : ℝ)
  | 10 => (89183 / 250000000000 : ℝ)
  | 11 => (11349 / 31250000000 : ℝ)
  | 12 => (11553 / 31250000000 : ℝ)
  | 13 => (75263 / 200000000000 : ℝ)
  | 14 => (383027 / 1000000000000 : ℝ)
  | 15 => (389833 / 1000000000000 : ℝ)
  | 16 => (396733 / 1000000000000 : ℝ)
  | 17 => (403729 / 1000000000000 : ℝ)
  | 18 => (205411 / 500000000000 : ℝ)
  | 19 => (104503 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch015Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (302761 / 1000000000000 : ℝ)
  | 1 => (308417 / 1000000000000 : ℝ)
  | 2 => (78539 / 250000000000 : ℝ)
  | 3 => (15999 / 50000000000 : ℝ)
  | 4 => (1273 / 3906250000 : ℝ)
  | 5 => (165941 / 500000000000 : ℝ)
  | 6 => (168981 / 500000000000 : ℝ)
  | 7 => (344131 / 1000000000000 : ℝ)
  | 8 => (350387 / 1000000000000 : ℝ)
  | 9 => (356733 / 1000000000000 : ℝ)
  | 10 => (363169 / 1000000000000 : ℝ)
  | 11 => (369697 / 1000000000000 : ℝ)
  | 12 => (94079 / 250000000000 : ℝ)
  | 13 => (95757 / 250000000000 : ℝ)
  | 14 => (194917 / 500000000000 : ℝ)
  | 15 => (198367 / 500000000000 : ℝ)
  | 16 => (40373 / 100000000000 : ℝ)
  | 17 => (410823 / 1000000000000 : ℝ)
  | 18 => (418013 / 1000000000000 : ℝ)
  | 19 => (425301 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch015Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((300 : ℝ) + (j.val : ℝ)) / 1600)
      (((300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch015Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch015Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((300 : ℝ) + (j.val : ℝ)) / 1600)
    (((300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch015Neg25WeightLower j.val) (hpThetaShiftThreeBatch015Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch015Neg25WeightLower, hpThetaShiftThreeBatch015Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch015Neg25_integral_bounds :
    (1375007 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (5665957 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch015Lower hpThetaJensenCellsBatch015Upper
    hpThetaShiftThreeBatch015Neg25WeightLower hpThetaShiftThreeBatch015Neg25WeightUpper hpThetaJensenCellsBatch015_bounds hpThetaShiftThreeBatch015Neg25_weight_bounds
  have hl : (1375007 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch015Lower j * hpThetaShiftThreeBatch015Neg25WeightLower j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftThreeBatch015Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftThreeBatch015Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch015Lower j * hpThetaShiftThreeBatch015Neg25WeightUpper j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftThreeBatch015Neg25WeightUpper j) / 1600) ≤ (5665957 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftThreeBatch015Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (300 : ℝ) / 1600 = 15 / 80 by norm_num,
    show ((300 : ℝ) + 20) / 1600 = (15 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch015Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch015Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch015Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch015Neg25_integral_bounds
end HodgeProofHP
