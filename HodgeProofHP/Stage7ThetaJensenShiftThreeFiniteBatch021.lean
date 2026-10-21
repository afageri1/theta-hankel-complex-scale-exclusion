/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch021

/-! Exact signed weight and batch integral certificates, batch 21 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch021Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (75183 / 1000000000000 : ℝ)
  | 1 => (69323 / 1000000000000 : ℝ)
  | 2 => (6331 / 100000000000 : ℝ)
  | 3 => (7143 / 125000000000 : ℝ)
  | 4 => (50823 / 1000000000000 : ℝ)
  | 5 => (5543 / 125000000000 : ℝ)
  | 6 => (37707 / 1000000000000 : ℝ)
  | 7 => (30909 / 1000000000000 : ℝ)
  | 8 => (23949 / 1000000000000 : ℝ)
  | 9 => (673 / 40000000000 : ℝ)
  | 10 => (1907 / 200000000000 : ℝ)
  | 11 => (2079 / 1000000000000 : ℝ)
  | 12 => (-5547 / 1000000000000 : ℝ)
  | 13 => (-13343 / 1000000000000 : ℝ)
  | 14 => (-333 / 15625000000 : ℝ)
  | 15 => (-14727 / 500000000000 : ℝ)
  | 16 => (-9443 / 250000000000 : ℝ)
  | 17 => (-46267 / 1000000000000 : ℝ)
  | 18 => (-54941 / 1000000000000 : ℝ)
  | 19 => (-12759 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch021Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (16179 / 200000000000 : ℝ)
  | 1 => (4699 / 62500000000 : ℝ)
  | 2 => (17331 / 250000000000 : ℝ)
  | 3 => (63311 / 1000000000000 : ℝ)
  | 4 => (11429 / 200000000000 : ℝ)
  | 5 => (6353 / 125000000000 : ℝ)
  | 6 => (8869 / 200000000000 : ℝ)
  | 7 => (9427 / 250000000000 : ℝ)
  | 8 => (3091 / 100000000000 : ℝ)
  | 9 => (479 / 20000000000 : ℝ)
  | 10 => (8413 / 500000000000 : ℝ)
  | 11 => (149 / 15625000000 : ℝ)
  | 12 => (13 / 6250000000 : ℝ)
  | 13 => (-2773 / 500000000000 : ℝ)
  | 14 => (-6671 / 500000000000 : ℝ)
  | 15 => (-21311 / 1000000000000 : ℝ)
  | 16 => (-29453 / 1000000000000 : ℝ)
  | 17 => (-37771 / 1000000000000 : ℝ)
  | 18 => (-23133 / 500000000000 : ℝ)
  | 19 => (-2747 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch021Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((420 : ℝ) + (j.val : ℝ)) / 1600)
      (((420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch021Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch021Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((420 : ℝ) + (j.val : ℝ)) / 1600)
    (((420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch021Neg100WeightLower j.val) (hpThetaShiftThreeBatch021Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch021Neg100WeightLower, hpThetaShiftThreeBatch021Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch021Neg100_integral_bounds :
    (121661 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (206619 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch021Lower hpThetaJensenCellsBatch021Upper
    hpThetaShiftThreeBatch021Neg100WeightLower hpThetaShiftThreeBatch021Neg100WeightUpper hpThetaJensenCellsBatch021_bounds hpThetaShiftThreeBatch021Neg100_weight_bounds
  have hl : (121661 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch021Lower j * hpThetaShiftThreeBatch021Neg100WeightLower j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftThreeBatch021Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftThreeBatch021Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch021Lower j * hpThetaShiftThreeBatch021Neg100WeightUpper j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftThreeBatch021Neg100WeightUpper j) / 1600) ≤ (206619 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftThreeBatch021Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (420 : ℝ) / 1600 = 21 / 80 by norm_num,
    show ((420 : ℝ) + 20) / 1600 = (21 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch021Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (608363 / 1000000000000 : ℝ)
  | 1 => (304997 / 500000000000 : ℝ)
  | 2 => (611537 / 1000000000000 : ℝ)
  | 3 => (153247 / 250000000000 : ℝ)
  | 4 => (307173 / 500000000000 : ℝ)
  | 5 => (61561 / 100000000000 : ℝ)
  | 6 => (24671 / 40000000000 : ℝ)
  | 7 => (308921 / 500000000000 : ℝ)
  | 8 => (618807 / 1000000000000 : ℝ)
  | 9 => (619669 / 1000000000000 : ℝ)
  | 10 => (77553 / 125000000000 : ℝ)
  | 11 => (38817 / 62500000000 : ℝ)
  | 12 => (621609 / 1000000000000 : ℝ)
  | 13 => (311017 / 500000000000 : ℝ)
  | 14 => (124469 / 200000000000 : ℝ)
  | 15 => (311269 / 500000000000 : ℝ)
  | 16 => (124513 / 200000000000 : ℝ)
  | 17 => (311197 / 500000000000 : ℝ)
  | 18 => (38881 / 62500000000 : ℝ)
  | 19 => (62167 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch021Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (121999 / 200000000000 : ℝ)
  | 1 => (305769 / 500000000000 : ℝ)
  | 2 => (612989 / 1000000000000 : ℝ)
  | 3 => (614347 / 1000000000000 : ℝ)
  | 4 => (615611 / 1000000000000 : ℝ)
  | 5 => (77097 / 125000000000 : ℝ)
  | 6 => (617843 / 1000000000000 : ℝ)
  | 7 => (77351 / 125000000000 : ℝ)
  | 8 => (61967 / 100000000000 : ℝ)
  | 9 => (24817 / 40000000000 : ℝ)
  | 10 => (621073 / 1000000000000 : ℝ)
  | 11 => (62161 / 100000000000 : ℝ)
  | 12 => (124407 / 200000000000 : ℝ)
  | 13 => (311173 / 500000000000 : ℝ)
  | 14 => (622539 / 1000000000000 : ℝ)
  | 15 => (622613 / 1000000000000 : ℝ)
  | 16 => (124523 / 200000000000 : ℝ)
  | 17 => (311283 / 500000000000 : ℝ)
  | 18 => (124479 / 200000000000 : ℝ)
  | 19 => (622097 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch021Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((420 : ℝ) + (j.val : ℝ)) / 1600)
      (((420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch021Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch021Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((420 : ℝ) + (j.val : ℝ)) / 1600)
    (((420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch021Neg70WeightLower j.val) (hpThetaShiftThreeBatch021Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch021Neg70WeightLower, hpThetaShiftThreeBatch021Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch021Neg70_integral_bounds :
    (6776423 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (3435621 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch021Lower hpThetaJensenCellsBatch021Upper
    hpThetaShiftThreeBatch021Neg70WeightLower hpThetaShiftThreeBatch021Neg70WeightUpper hpThetaJensenCellsBatch021_bounds hpThetaShiftThreeBatch021Neg70_weight_bounds
  have hl : (6776423 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch021Lower j * hpThetaShiftThreeBatch021Neg70WeightLower j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftThreeBatch021Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftThreeBatch021Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch021Lower j * hpThetaShiftThreeBatch021Neg70WeightUpper j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftThreeBatch021Neg70WeightUpper j) / 1600) ≤ (3435621 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftThreeBatch021Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (420 : ℝ) / 1600 = 21 / 80 by norm_num,
    show ((420 : ℝ) + 20) / 1600 = (21 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch021Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1212257 / 1000000000000 : ℝ)
  | 1 => (122373 / 100000000000 : ℝ)
  | 2 => (617619 / 500000000000 : ℝ)
  | 3 => (1246781 / 1000000000000 : ℝ)
  | 4 => (1258357 / 1000000000000 : ℝ)
  | 5 => (634983 / 500000000000 : ℝ)
  | 6 => (640803 / 500000000000 : ℝ)
  | 7 => (1293277 / 1000000000000 : ℝ)
  | 8 => (1304977 / 1000000000000 : ℝ)
  | 9 => (41147 / 31250000000 : ℝ)
  | 10 => (1328459 / 1000000000000 : ℝ)
  | 11 => (670119 / 500000000000 : ℝ)
  | 12 => (676021 / 500000000000 : ℝ)
  | 13 => (1363869 / 1000000000000 : ℝ)
  | 14 => (687859 / 500000000000 : ℝ)
  | 15 => (693793 / 500000000000 : ℝ)
  | 16 => (699737 / 500000000000 : ℝ)
  | 17 => (1411379 / 1000000000000 : ℝ)
  | 18 => (14233 / 10000000000 : ℝ)
  | 19 => (358809 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch021Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1223731 / 1000000000000 : ℝ)
  | 1 => (1235239 / 1000000000000 : ℝ)
  | 2 => (623391 / 500000000000 : ℝ)
  | 3 => (629179 / 500000000000 : ℝ)
  | 4 => (1269967 / 1000000000000 : ℝ)
  | 5 => (1281607 / 1000000000000 : ℝ)
  | 6 => (646639 / 500000000000 : ℝ)
  | 7 => (652489 / 500000000000 : ℝ)
  | 8 => (263341 / 200000000000 : ℝ)
  | 9 => (66423 / 50000000000 : ℝ)
  | 10 => (1340239 / 1000000000000 : ℝ)
  | 11 => (1352043 / 1000000000000 : ℝ)
  | 12 => (136387 / 100000000000 : ℝ)
  | 13 => (1375719 / 1000000000000 : ℝ)
  | 14 => (1387587 / 1000000000000 : ℝ)
  | 15 => (55979 / 40000000000 : ℝ)
  | 16 => (70569 / 50000000000 : ℝ)
  | 17 => (1423301 / 1000000000000 : ℝ)
  | 18 => (1435237 / 1000000000000 : ℝ)
  | 19 => (723593 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch021Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((420 : ℝ) + (j.val : ℝ)) / 1600)
      (((420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch021Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch021Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((420 : ℝ) + (j.val : ℝ)) / 1600)
    (((420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch021Neg45WeightLower j.val) (hpThetaShiftThreeBatch021Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch021Neg45WeightLower, hpThetaShiftThreeBatch021Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch021Neg45_integral_bounds :
    (14488683 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (3700887 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch021Lower hpThetaJensenCellsBatch021Upper
    hpThetaShiftThreeBatch021Neg45WeightLower hpThetaShiftThreeBatch021Neg45WeightUpper hpThetaJensenCellsBatch021_bounds hpThetaShiftThreeBatch021Neg45_weight_bounds
  have hl : (14488683 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch021Lower j * hpThetaShiftThreeBatch021Neg45WeightLower j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftThreeBatch021Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftThreeBatch021Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch021Lower j * hpThetaShiftThreeBatch021Neg45WeightUpper j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftThreeBatch021Neg45WeightUpper j) / 1600) ≤ (3700887 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftThreeBatch021Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (420 : ℝ) / 1600 = 21 / 80 by norm_num,
    show ((420 : ℝ) + 20) / 1600 = (21 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch021Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (9069 / 5000000000 : ℝ)
  | 1 => (229487 / 125000000000 : ℝ)
  | 2 => (232273 / 125000000000 : ℝ)
  | 3 => (376133 / 200000000000 : ℝ)
  | 4 => (95167 / 50000000000 : ℝ)
  | 5 => (1926209 / 1000000000000 : ℝ)
  | 6 => (1949273 / 1000000000000 : ℝ)
  | 7 => (1972533 / 1000000000000 : ℝ)
  | 8 => (199599 / 100000000000 : ℝ)
  | 9 => (2019643 / 1000000000000 : ℝ)
  | 10 => (1021747 / 500000000000 : ℝ)
  | 11 => (258443 / 125000000000 : ℝ)
  | 12 => (2091793 / 1000000000000 : ℝ)
  | 13 => (2116241 / 1000000000000 : ℝ)
  | 14 => (214089 / 100000000000 : ℝ)
  | 15 => (108287 / 50000000000 : ℝ)
  | 16 => (2190791 / 1000000000000 : ℝ)
  | 17 => (443209 / 200000000000 : ℝ)
  | 18 => (2241501 / 1000000000000 : ℝ)
  | 19 => (2267161 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch021Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1835897 / 1000000000000 : ℝ)
  | 1 => (371637 / 200000000000 : ℝ)
  | 2 => (940333 / 500000000000 : ℝ)
  | 3 => (1903341 / 1000000000000 : ℝ)
  | 4 => (192621 / 100000000000 : ℝ)
  | 5 => (974637 / 500000000000 : ℝ)
  | 6 => (986267 / 500000000000 : ℝ)
  | 7 => (1995991 / 1000000000000 : ℝ)
  | 8 => (504911 / 250000000000 : ℝ)
  | 9 => (408699 / 200000000000 : ℝ)
  | 10 => (413509 / 200000000000 : ℝ)
  | 11 => (1045897 / 500000000000 : ℝ)
  | 12 => (1058121 / 500000000000 : ℝ)
  | 13 => (2140891 / 1000000000000 : ℝ)
  | 14 => (2165741 / 1000000000000 : ℝ)
  | 15 => (273849 / 125000000000 : ℝ)
  | 16 => (1108023 / 500000000000 : ℝ)
  | 17 => (1120751 / 500000000000 : ℝ)
  | 18 => (1133581 / 500000000000 : ℝ)
  | 19 => (91721 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch021Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((420 : ℝ) + (j.val : ℝ)) / 1600)
      (((420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch021Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch021Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((420 : ℝ) + (j.val : ℝ)) / 1600)
    (((420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch021Neg25WeightLower j.val) (hpThetaShiftThreeBatch021Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch021Neg25WeightLower, hpThetaShiftThreeBatch021Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch021Neg25_integral_bounds :
    (2784609 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (4565261 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch021Lower hpThetaJensenCellsBatch021Upper
    hpThetaShiftThreeBatch021Neg25WeightLower hpThetaShiftThreeBatch021Neg25WeightUpper hpThetaJensenCellsBatch021_bounds hpThetaShiftThreeBatch021Neg25_weight_bounds
  have hl : (2784609 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch021Lower j * hpThetaShiftThreeBatch021Neg25WeightLower j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftThreeBatch021Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftThreeBatch021Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch021Lower j * hpThetaShiftThreeBatch021Neg25WeightUpper j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftThreeBatch021Neg25WeightUpper j) / 1600) ≤ (4565261 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftThreeBatch021Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (420 : ℝ) / 1600 = 21 / 80 by norm_num,
    show ((420 : ℝ) + 20) / 1600 = (21 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch021Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch021Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch021Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch021Neg25_integral_bounds
end HodgeProofHP
