/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch042

/-! Exact signed weight and batch integral certificates, batch 42 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch042Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3148007 / 50000000000 : ℝ)
  | 1 => (6376521 / 100000000000 : ℝ)
  | 2 => (12914761 / 200000000000 : ℝ)
  | 3 => (32692909 / 500000000000 : ℝ)
  | 4 => (33100571 / 500000000000 : ℝ)
  | 5 => (16754917 / 250000000000 : ℝ)
  | 6 => (53001 / 781250000 : ℝ)
  | 7 => (68665861 / 1000000000000 : ℝ)
  | 8 => (6949329 / 100000000000 : ℝ)
  | 9 => (70323443 / 1000000000000 : ℝ)
  | 10 => (2223631 / 31250000000 : ℝ)
  | 11 => (14398281 / 200000000000 : ℝ)
  | 12 => (18207237 / 250000000000 : ℝ)
  | 13 => (1841717 / 25000000000 : ℝ)
  | 14 => (74510461 / 1000000000000 : ℝ)
  | 15 => (75354143 / 1000000000000 : ℝ)
  | 16 => (3047983 / 40000000000 : ℝ)
  | 17 => (19261651 / 250000000000 : ℝ)
  | 18 => (2434221 / 31250000000 : ℝ)
  | 19 => (39372407 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch042Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (63765211 / 1000000000000 : ℝ)
  | 1 => (32286903 / 500000000000 : ℝ)
  | 2 => (65385819 / 1000000000000 : ℝ)
  | 3 => (66201143 / 1000000000000 : ℝ)
  | 4 => (67019669 / 1000000000000 : ℝ)
  | 5 => (67841281 / 1000000000000 : ℝ)
  | 6 => (34332931 / 500000000000 : ℝ)
  | 7 => (69493291 / 1000000000000 : ℝ)
  | 8 => (17580861 / 250000000000 : ℝ)
  | 9 => (71156193 / 1000000000000 : ℝ)
  | 10 => (35995703 / 500000000000 : ℝ)
  | 11 => (72828949 / 1000000000000 : ℝ)
  | 12 => (73668681 / 1000000000000 : ℝ)
  | 13 => (37255231 / 500000000000 : ℝ)
  | 14 => (2354817 / 31250000000 : ℝ)
  | 15 => (9524947 / 125000000000 : ℝ)
  | 16 => (15409321 / 200000000000 : ℝ)
  | 17 => (77895073 / 1000000000000 : ℝ)
  | 18 => (15748963 / 200000000000 : ℝ)
  | 19 => (19898917 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch042Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((840 : ℝ) + (j.val : ℝ)) / 1600)
      (((840 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch042Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch042Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((840 : ℝ) + (j.val : ℝ)) / 1600)
    (((840 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch042Neg100WeightLower j.val) (hpThetaShiftThreeBatch042Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch042Neg100WeightLower, hpThetaShiftThreeBatch042Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch042Neg100_integral_bounds :
    (17781613 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (36601219 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (840 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch042Lower hpThetaJensenCellsBatch042Upper
    hpThetaShiftThreeBatch042Neg100WeightLower hpThetaShiftThreeBatch042Neg100WeightUpper hpThetaJensenCellsBatch042_bounds hpThetaShiftThreeBatch042Neg100_weight_bounds
  have hl : (17781613 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch042Lower j * hpThetaShiftThreeBatch042Neg100WeightLower j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftThreeBatch042Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftThreeBatch042Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch042Lower j * hpThetaShiftThreeBatch042Neg100WeightUpper j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftThreeBatch042Neg100WeightUpper j) / 1600) ≤ (36601219 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftThreeBatch042Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (840 : ℝ) / 1600 = 42 / 80 by norm_num,
    show ((840 : ℝ) + 20) / 1600 = (42 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch042Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (294911 / 1000000000000 : ℝ)
  | 1 => (325107 / 500000000000 : ℝ)
  | 2 => (1012087 / 1000000000000 : ℝ)
  | 3 => (1380591 / 1000000000000 : ℝ)
  | 4 => (1755789 / 1000000000000 : ℝ)
  | 5 => (133609 / 62500000000 : ℝ)
  | 6 => (1263259 / 500000000000 : ℝ)
  | 7 => (116887 / 40000000000 : ℝ)
  | 8 => (415597 / 125000000000 : ℝ)
  | 9 => (3734387 / 1000000000000 : ℝ)
  | 10 => (1037767 / 250000000000 : ℝ)
  | 11 => (1143721 / 250000000000 : ℝ)
  | 12 => (2502949 / 500000000000 : ℝ)
  | 13 => (1361043 / 250000000000 : ℝ)
  | 14 => (5889771 / 1000000000000 : ℝ)
  | 15 => (3171379 / 500000000000 : ℝ)
  | 16 => (1360639 / 200000000000 : ℝ)
  | 17 => (3635573 / 500000000000 : ℝ)
  | 18 => (309867 / 40000000000 : ℝ)
  | 19 => (1645969 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch042Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (130043 / 200000000000 : ℝ)
  | 1 => (126511 / 125000000000 : ℝ)
  | 2 => (86287 / 62500000000 : ℝ)
  | 3 => (175579 / 100000000000 : ℝ)
  | 4 => (427549 / 200000000000 : ℝ)
  | 5 => (2526519 / 1000000000000 : ℝ)
  | 6 => (45659 / 15625000000 : ℝ)
  | 7 => (3324777 / 1000000000000 : ℝ)
  | 8 => (933597 / 250000000000 : ℝ)
  | 9 => (4151069 / 1000000000000 : ℝ)
  | 10 => (914977 / 200000000000 : ℝ)
  | 11 => (5005899 / 1000000000000 : ℝ)
  | 12 => (5444173 / 1000000000000 : ℝ)
  | 13 => (1472443 / 250000000000 : ℝ)
  | 14 => (6342759 / 1000000000000 : ℝ)
  | 15 => (1700799 / 250000000000 : ℝ)
  | 16 => (7271147 / 1000000000000 : ℝ)
  | 17 => (1936669 / 250000000000 : ℝ)
  | 18 => (4114923 / 500000000000 : ℝ)
  | 19 => (109009 / 12500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch042Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((840 : ℝ) + (j.val : ℝ)) / 1600)
      (((840 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch042Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch042Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((840 : ℝ) + (j.val : ℝ)) / 1600)
    (((840 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch042Neg70WeightLower j.val) (hpThetaShiftThreeBatch042Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch042Neg70WeightLower, hpThetaShiftThreeBatch042Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch042Neg70_integral_bounds :
    (3976911 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (6993 / 1562500000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (840 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch042Lower hpThetaJensenCellsBatch042Upper
    hpThetaShiftThreeBatch042Neg70WeightLower hpThetaShiftThreeBatch042Neg70WeightUpper hpThetaJensenCellsBatch042_bounds hpThetaShiftThreeBatch042Neg70_weight_bounds
  have hl : (3976911 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch042Lower j * hpThetaShiftThreeBatch042Neg70WeightLower j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftThreeBatch042Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftThreeBatch042Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch042Lower j * hpThetaShiftThreeBatch042Neg70WeightUpper j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftThreeBatch042Neg70WeightUpper j) / 1600) ≤ (6993 / 1562500000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftThreeBatch042Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (840 : ℝ) / 1600 = 42 / 80 by norm_num,
    show ((840 : ℝ) + 20) / 1600 = (42 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch042Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-14994487 / 500000000000 : ℝ)
  | 1 => (-1208511 / 40000000000 : ℝ)
  | 2 => (-30436383 / 1000000000000 : ℝ)
  | 3 => (-30659771 / 1000000000000 : ℝ)
  | 4 => (-30882911 / 1000000000000 : ℝ)
  | 5 => (-31105773 / 1000000000000 : ℝ)
  | 6 => (-3132833 / 100000000000 : ℝ)
  | 7 => (-31550551 / 1000000000000 : ℝ)
  | 8 => (-3971551 / 125000000000 : ℝ)
  | 9 => (-31993869 / 1000000000000 : ℝ)
  | 10 => (-6442981 / 200000000000 : ℝ)
  | 11 => (-6487097 / 200000000000 : ℝ)
  | 12 => (-16327789 / 500000000000 : ℝ)
  | 13 => (-32875151 / 1000000000000 : ℝ)
  | 14 => (-16547087 / 500000000000 : ℝ)
  | 15 => (-33312613 / 1000000000000 : ℝ)
  | 16 => (-33530437 / 1000000000000 : ℝ)
  | 17 => (-33747611 / 1000000000000 : ℝ)
  | 18 => (-16982051 / 500000000000 : ℝ)
  | 19 => (-8544969 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch042Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-29765007 / 1000000000000 : ℝ)
  | 1 => (-29988973 / 1000000000000 : ℝ)
  | 2 => (-15106387 / 500000000000 : ℝ)
  | 3 => (-15218191 / 500000000000 : ℝ)
  | 4 => (-3065977 / 100000000000 : ℝ)
  | 5 => (-3088291 / 100000000000 : ℝ)
  | 6 => (-7776443 / 250000000000 : ℝ)
  | 7 => (-31328329 / 1000000000000 : ℝ)
  | 8 => (-631011 / 20000000000 : ℝ)
  | 9 => (-31772407 / 1000000000000 : ℝ)
  | 10 => (-7998467 / 250000000000 : ℝ)
  | 11 => (-4026863 / 125000000000 : ℝ)
  | 12 => (-8108871 / 250000000000 : ℝ)
  | 13 => (-32655577 / 1000000000000 : ℝ)
  | 14 => (-657503 / 20000000000 : ℝ)
  | 15 => (-33094173 / 1000000000000 : ℝ)
  | 16 => (-8328153 / 250000000000 : ℝ)
  | 17 => (-8382609 / 250000000000 : ℝ)
  | 18 => (-3374761 / 100000000000 : ℝ)
  | 19 => (-33964101 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch042Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((840 : ℝ) + (j.val : ℝ)) / 1600)
      (((840 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch042Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch042Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((840 : ℝ) + (j.val : ℝ)) / 1600)
    (((840 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch042Neg45WeightLower j.val) (hpThetaShiftThreeBatch042Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch042Neg45WeightLower, hpThetaShiftThreeBatch042Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch042Neg45_integral_bounds :
    (-32852689 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-32074443 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (840 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch042Lower hpThetaJensenCellsBatch042Upper
    hpThetaShiftThreeBatch042Neg45WeightLower hpThetaShiftThreeBatch042Neg45WeightUpper hpThetaJensenCellsBatch042_bounds hpThetaShiftThreeBatch042Neg45_weight_bounds
  have hl : (-32852689 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch042Lower j * hpThetaShiftThreeBatch042Neg45WeightLower j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftThreeBatch042Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftThreeBatch042Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch042Lower j * hpThetaShiftThreeBatch042Neg45WeightUpper j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftThreeBatch042Neg45WeightUpper j) / 1600) ≤ (-32074443 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftThreeBatch042Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (840 : ℝ) / 1600 = 42 / 80 by norm_num,
    show ((840 : ℝ) + 20) / 1600 = (42 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch042Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4995699 / 1000000000000 : ℝ)
  | 1 => (481177 / 100000000000 : ℝ)
  | 2 => (4625439 / 1000000000000 : ℝ)
  | 3 => (4436691 / 1000000000000 : ℝ)
  | 4 => (530689 / 125000000000 : ℝ)
  | 5 => (4051889 / 1000000000000 : ℝ)
  | 6 => (60247 / 15625000000 : ℝ)
  | 7 => (731451 / 200000000000 : ℝ)
  | 8 => (432027 / 125000000000 : ℝ)
  | 9 => (3252677 / 1000000000000 : ℝ)
  | 10 => (1523313 / 500000000000 : ℝ)
  | 11 => (2838047 / 1000000000000 : ℝ)
  | 12 => (164183 / 62500000000 : ℝ)
  | 13 => (482651 / 200000000000 : ℝ)
  | 14 => (1098507 / 500000000000 : ℝ)
  | 15 => (123637 / 62500000000 : ℝ)
  | 16 => (878387 / 500000000000 : ℝ)
  | 17 => (383187 / 250000000000 : ℝ)
  | 18 => (13061 / 10000000000 : ℝ)
  | 19 => (1076817 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch042Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5177239 / 1000000000000 : ℝ)
  | 1 => (49957 / 10000000000 : ℝ)
  | 2 => (4811771 / 1000000000000 : ℝ)
  | 3 => (28909 / 6250000000 : ℝ)
  | 4 => (1109173 / 250000000000 : ℝ)
  | 5 => (4245513 / 1000000000000 : ℝ)
  | 6 => (405189 / 100000000000 : ℝ)
  | 7 => (3855809 / 1000000000000 : ℝ)
  | 8 => (457157 / 125000000000 : ℝ)
  | 9 => (3456217 / 1000000000000 : ℝ)
  | 10 => (1626339 / 500000000000 : ℝ)
  | 11 => (3046627 / 1000000000000 : ℝ)
  | 12 => (88689 / 31250000000 : ℝ)
  | 13 => (2626929 / 1000000000000 : ℝ)
  | 14 => (301657 / 125000000000 : ℝ)
  | 15 => (439403 / 200000000000 : ℝ)
  | 16 => (1978193 / 1000000000000 : ℝ)
  | 17 => (70271 / 40000000000 : ℝ)
  | 18 => (1532749 / 1000000000000 : ℝ)
  | 19 => (1306101 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch042Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((840 : ℝ) + (j.val : ℝ)) / 1600)
      (((840 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch042Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch042Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((840 : ℝ) + (j.val : ℝ)) / 1600)
    (((840 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch042Neg25WeightLower j.val) (hpThetaShiftThreeBatch042Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch042Neg25WeightLower, hpThetaShiftThreeBatch042Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch042Neg25_integral_bounds :
    (797691 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (3455083 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (840 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch042Lower hpThetaJensenCellsBatch042Upper
    hpThetaShiftThreeBatch042Neg25WeightLower hpThetaShiftThreeBatch042Neg25WeightUpper hpThetaJensenCellsBatch042_bounds hpThetaShiftThreeBatch042Neg25_weight_bounds
  have hl : (797691 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch042Lower j * hpThetaShiftThreeBatch042Neg25WeightLower j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftThreeBatch042Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftThreeBatch042Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch042Lower j * hpThetaShiftThreeBatch042Neg25WeightUpper j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftThreeBatch042Neg25WeightUpper j) / 1600) ≤ (3455083 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftThreeBatch042Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (840 : ℝ) / 1600 = 42 / 80 by norm_num,
    show ((840 : ℝ) + 20) / 1600 = (42 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch042Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch042Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch042Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch042Neg25_integral_bounds
end HodgeProofHP
