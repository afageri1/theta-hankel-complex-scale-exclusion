/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch057

/-! Exact signed weight and batch integral certificates, batch 57 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch057Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-77607331 / 25000000000 : ℝ)
  | 1 => (-1580189773 / 500000000000 : ℝ)
  | 2 => (-804316817 / 250000000000 : ℝ)
  | 3 => (-818741477 / 250000000000 : ℝ)
  | 4 => (-666697013 / 200000000000 : ℝ)
  | 5 => (-3392834433 / 1000000000000 : ℝ)
  | 6 => (-863255951 / 250000000000 : ℝ)
  | 7 => (-439257883 / 125000000000 : ℝ)
  | 8 => (-1787981101 / 500000000000 : ℝ)
  | 9 => (-454841413 / 125000000000 : ℝ)
  | 10 => (-740476111 / 200000000000 : ℝ)
  | 11 => (-1883460121 / 500000000000 : ℝ)
  | 12 => (-766472151 / 200000000000 : ℝ)
  | 13 => (-3898712583 / 1000000000000 : ℝ)
  | 14 => (-3965986323 / 1000000000000 : ℝ)
  | 15 => (-126068521 / 31250000000 : ℝ)
  | 16 => (-820668487 / 200000000000 : ℝ)
  | 17 => (-4173446523 / 1000000000000 : ℝ)
  | 18 => (-4244515951 / 1000000000000 : ℝ)
  | 19 => (-1079140461 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch057Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1524499469 / 500000000000 : ℝ)
  | 1 => (-3104293239 / 1000000000000 : ℝ)
  | 2 => (-632075909 / 200000000000 : ℝ)
  | 3 => (-3217267267 / 1000000000000 : ℝ)
  | 4 => (-3274965907 / 1000000000000 : ℝ)
  | 5 => (-416685633 / 125000000000 : ℝ)
  | 6 => (-26506519 / 7812500000 : ℝ)
  | 7 => (-3453023803 / 1000000000000 : ℝ)
  | 8 => (-3514063063 / 1000000000000 : ℝ)
  | 9 => (-3575962201 / 1000000000000 : ℝ)
  | 10 => (-3638731303 / 1000000000000 : ℝ)
  | 11 => (-1851190277 / 500000000000 : ℝ)
  | 12 => (-3766920241 / 1000000000000 : ℝ)
  | 13 => (-1916180377 / 500000000000 : ℝ)
  | 14 => (-1949356291 / 500000000000 : ℝ)
  | 15 => (-1982993161 / 500000000000 : ℝ)
  | 16 => (-4034192671 / 1000000000000 : ℝ)
  | 17 => (-2051671217 / 500000000000 : ℝ)
  | 18 => (-2086723261 / 500000000000 : ℝ)
  | 19 => (-84890319 / 20000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch057Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1140 : ℝ) + (j.val : ℝ)) / 1600)
      (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch057Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch057Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1140 : ℝ) + (j.val : ℝ)) / 1600)
    (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch057Neg100WeightLower j.val) (hpThetaShiftThreeBatch057Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch057Neg100WeightLower, hpThetaShiftThreeBatch057Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch057Neg100_integral_bounds :
    (-29723907 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-71430437 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch057Lower hpThetaJensenCellsBatch057Upper
    hpThetaShiftThreeBatch057Neg100WeightLower hpThetaShiftThreeBatch057Neg100WeightUpper hpThetaJensenCellsBatch057_bounds hpThetaShiftThreeBatch057Neg100_weight_bounds
  have hl : (-29723907 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch057Lower j * hpThetaShiftThreeBatch057Neg100WeightLower j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftThreeBatch057Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftThreeBatch057Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch057Lower j * hpThetaShiftThreeBatch057Neg100WeightUpper j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftThreeBatch057Neg100WeightUpper j) / 1600) ≤ (-71430437 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftThreeBatch057Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1140 : ℝ) / 1600 = 57 / 80 by norm_num,
    show ((1140 : ℝ) + 20) / 1600 = (57 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch057Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (43972571 / 125000000000 : ℝ)
  | 1 => (69999171 / 200000000000 : ℝ)
  | 2 => (174056929 / 500000000000 : ℝ)
  | 3 => (346132831 / 1000000000000 : ℝ)
  | 4 => (344051007 / 1000000000000 : ℝ)
  | 5 => (341866597 / 1000000000000 : ℝ)
  | 6 => (339577789 / 1000000000000 : ℝ)
  | 7 => (337182749 / 1000000000000 : ℝ)
  | 8 => (16733981 / 50000000000 : ℝ)
  | 9 => (332066523 / 1000000000000 : ℝ)
  | 10 => (164670777 / 500000000000 : ℝ)
  | 11 => (326502789 / 1000000000000 : ℝ)
  | 12 => (80887069 / 250000000000 : ℝ)
  | 13 => (320476043 / 1000000000000 : ℝ)
  | 14 => (317284093 / 1000000000000 : ℝ)
  | 15 => (156985201 / 500000000000 : ℝ)
  | 16 => (155266463 / 500000000000 : ℝ)
  | 17 => (153484797 / 500000000000 : ℝ)
  | 18 => (303278309 / 1000000000000 : ℝ)
  | 19 => (299456951 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch057Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (353469721 / 1000000000000 : ℝ)
  | 1 => (351780569 / 1000000000000 : ℝ)
  | 2 => (21874741 / 62500000000 : ℝ)
  | 3 => (348113859 / 1000000000000 : ℝ)
  | 4 => (10816651 / 31250000000 : ℝ)
  | 5 => (5375797 / 15625000000 : ℝ)
  | 6 => (170933299 / 500000000000 : ℝ)
  | 7 => (33957779 / 100000000000 : ℝ)
  | 8 => (1348731 / 4000000000 : ℝ)
  | 9 => (334679621 / 1000000000000 : ℝ)
  | 10 => (83016631 / 250000000000 : ℝ)
  | 11 => (65868311 / 200000000000 : ℝ)
  | 12 => (32650279 / 100000000000 : ℝ)
  | 13 => (323548277 / 1000000000000 : ℝ)
  | 14 => (80119011 / 250000000000 : ℝ)
  | 15 => (158642047 / 500000000000 : ℝ)
  | 16 => (313970403 / 1000000000000 : ℝ)
  | 17 => (310532927 / 1000000000000 : ℝ)
  | 18 => (61393919 / 200000000000 : ℝ)
  | 19 => (30327831 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch057Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1140 : ℝ) + (j.val : ℝ)) / 1600)
      (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch057Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch057Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1140 : ℝ) + (j.val : ℝ)) / 1600)
    (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch057Neg70WeightLower j.val) (hpThetaShiftThreeBatch057Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch057Neg70WeightLower, hpThetaShiftThreeBatch057Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch057Neg70_integral_bounds :
    (1312217 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (845217 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch057Lower hpThetaJensenCellsBatch057Upper
    hpThetaShiftThreeBatch057Neg70WeightLower hpThetaShiftThreeBatch057Neg70WeightUpper hpThetaJensenCellsBatch057_bounds hpThetaShiftThreeBatch057Neg70_weight_bounds
  have hl : (1312217 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch057Lower j * hpThetaShiftThreeBatch057Neg70WeightLower j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftThreeBatch057Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftThreeBatch057Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch057Lower j * hpThetaShiftThreeBatch057Neg70WeightUpper j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftThreeBatch057Neg70WeightUpper j) / 1600) ≤ (845217 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftThreeBatch057Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1140 : ℝ) / 1600 = 57 / 80 by norm_num,
    show ((1140 : ℝ) + 20) / 1600 = (57 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch057Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (91086011 / 500000000000 : ℝ)
  | 1 => (185207773 / 1000000000000 : ℝ)
  | 2 => (11766859 / 62500000000 : ℝ)
  | 3 => (95679007 / 500000000000 : ℝ)
  | 4 => (9723633 / 50000000000 : ℝ)
  | 5 => (197613757 / 1000000000000 : ℝ)
  | 6 => (100390691 / 500000000000 : ℝ)
  | 7 => (40795121 / 200000000000 : ℝ)
  | 8 => (414393 / 2000000000 : ℝ)
  | 9 => (42088827 / 200000000000 : ℝ)
  | 10 => (10685929 / 50000000000 : ℝ)
  | 11 => (217019899 / 1000000000000 : ℝ)
  | 12 => (172147 / 781250000 : ℝ)
  | 13 => (1747683 / 7812500000 : ℝ)
  | 14 => (113542877 / 500000000000 : ℝ)
  | 15 => (23049521 / 100000000000 : ℝ)
  | 16 => (233931849 / 1000000000000 : ℝ)
  | 17 => (237395729 / 1000000000000 : ℝ)
  | 18 => (120443451 / 500000000000 : ℝ)
  | 19 => (244405423 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch057Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (92603887 / 500000000000 : ℝ)
  | 1 => (37653949 / 200000000000 : ℝ)
  | 2 => (38271603 / 200000000000 : ℝ)
  | 3 => (194472661 / 1000000000000 : ℝ)
  | 4 => (98806879 / 500000000000 : ℝ)
  | 5 => (200781383 / 1000000000000 : ℝ)
  | 6 => (101987803 / 500000000000 : ℝ)
  | 7 => (207196501 / 1000000000000 : ℝ)
  | 8 => (26305517 / 125000000000 : ℝ)
  | 9 => (213718581 / 1000000000000 : ℝ)
  | 10 => (2170199 / 10000000000 : ℝ)
  | 11 => (220348161 / 1000000000000 : ℝ)
  | 12 => (8948137 / 40000000000 : ℝ)
  | 13 => (45417151 / 200000000000 : ℝ)
  | 14 => (230495211 / 1000000000000 : ℝ)
  | 15 => (4678637 / 20000000000 : ℝ)
  | 16 => (23739573 / 100000000000 : ℝ)
  | 17 => (240886903 / 1000000000000 : ℝ)
  | 18 => (15275339 / 62500000000 : ℝ)
  | 19 => (247951343 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch057Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1140 : ℝ) + (j.val : ℝ)) / 1600)
      (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch057Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch057Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1140 : ℝ) + (j.val : ℝ)) / 1600)
    (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch057Neg45WeightLower j.val) (hpThetaShiftThreeBatch057Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch057Neg45WeightLower, hpThetaShiftThreeBatch057Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch057Neg45_integral_bounds :
    (8390351 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (2177849 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch057Lower hpThetaJensenCellsBatch057Upper
    hpThetaShiftThreeBatch057Neg45WeightLower hpThetaShiftThreeBatch057Neg45WeightUpper hpThetaJensenCellsBatch057_bounds hpThetaShiftThreeBatch057Neg45_weight_bounds
  have hl : (8390351 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch057Lower j * hpThetaShiftThreeBatch057Neg45WeightLower j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftThreeBatch057Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftThreeBatch057Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch057Lower j * hpThetaShiftThreeBatch057Neg45WeightUpper j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftThreeBatch057Neg45WeightUpper j) / 1600) ≤ (2177849 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftThreeBatch057Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1140 : ℝ) / 1600 = 57 / 80 by norm_num,
    show ((1140 : ℝ) + 20) / 1600 = (57 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch057Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-93585089 / 500000000000 : ℝ)
  | 1 => (-188130379 / 1000000000000 : ℝ)
  | 2 => (-94544541 / 500000000000 : ℝ)
  | 3 => (-190046211 / 1000000000000 : ℝ)
  | 4 => (-47750423 / 250000000000 : ℝ)
  | 5 => (-95977723 / 500000000000 : ℝ)
  | 6 => (-192907397 / 1000000000000 : ℝ)
  | 7 => (-96928733 / 500000000000 : ℝ)
  | 8 => (-97402787 / 500000000000 : ℝ)
  | 9 => (-195751641 / 1000000000000 : ℝ)
  | 10 => (-49173897 / 250000000000 : ℝ)
  | 11 => (-49409333 / 250000000000 : ℝ)
  | 12 => (-198576793 / 1000000000000 : ℝ)
  | 13 => (-199513887 / 1000000000000 : ℝ)
  | 14 => (-200448531 / 1000000000000 : ℝ)
  | 15 => (-100690321 / 500000000000 : ℝ)
  | 16 => (-202310133 / 1000000000000 : ℝ)
  | 17 => (-203236921 / 1000000000000 : ℝ)
  | 18 => (-102080459 / 500000000000 : ℝ)
  | 19 => (-102541019 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch057Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-93104277 / 500000000000 : ℝ)
  | 1 => (-187170177 / 1000000000000 : ℝ)
  | 2 => (-94065189 / 500000000000 : ℝ)
  | 3 => (-189089081 / 1000000000000 : ℝ)
  | 4 => (-19004621 / 100000000000 : ℝ)
  | 5 => (-191001691 / 1000000000000 : ℝ)
  | 6 => (-38391089 / 200000000000 : ℝ)
  | 7 => (-48226849 / 250000000000 : ℝ)
  | 8 => (-38771493 / 200000000000 : ℝ)
  | 9 => (-194805573 / 1000000000000 : ℝ)
  | 10 => (-4893791 / 25000000000 : ℝ)
  | 11 => (-196695587 / 1000000000000 : ℝ)
  | 12 => (-197637331 / 1000000000000 : ℝ)
  | 13 => (-24822099 / 125000000000 : ℝ)
  | 14 => (-99756943 / 500000000000 : ℝ)
  | 15 => (-20044853 / 100000000000 : ℝ)
  | 16 => (-201380641 / 1000000000000 : ℝ)
  | 17 => (-50577533 / 250000000000 : ℝ)
  | 18 => (-5080923 / 25000000000 : ℝ)
  | 19 => (-204160917 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch057Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1140 : ℝ) + (j.val : ℝ)) / 1600)
      (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch057Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch057Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1140 : ℝ) + (j.val : ℝ)) / 1600)
    (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch057Neg25WeightLower j.val) (hpThetaShiftThreeBatch057Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch057Neg25WeightLower, hpThetaShiftThreeBatch057Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch057Neg25_integral_bounds :
    (-7956819 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-3872537 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch057Lower hpThetaJensenCellsBatch057Upper
    hpThetaShiftThreeBatch057Neg25WeightLower hpThetaShiftThreeBatch057Neg25WeightUpper hpThetaJensenCellsBatch057_bounds hpThetaShiftThreeBatch057Neg25_weight_bounds
  have hl : (-7956819 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch057Lower j * hpThetaShiftThreeBatch057Neg25WeightLower j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftThreeBatch057Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftThreeBatch057Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch057Lower j * hpThetaShiftThreeBatch057Neg25WeightUpper j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftThreeBatch057Neg25WeightUpper j) / 1600) ≤ (-3872537 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftThreeBatch057Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1140 : ℝ) / 1600 = 57 / 80 by norm_num,
    show ((1140 : ℝ) + 20) / 1600 = (57 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch057Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch057Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch057Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch057Neg25_integral_bounds
end HodgeProofHP
