/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch015

/-! Exact signed weight and batch integral certificates, batch 15 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch015Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (19735291 / 1000000000000 : ℝ)
  | 1 => (19593189 / 1000000000000 : ℝ)
  | 2 => (19443609 / 1000000000000 : ℝ)
  | 3 => (4821613 / 250000000000 : ℝ)
  | 4 => (956081 / 50000000000 : ℝ)
  | 5 => (9474507 / 500000000000 : ℝ)
  | 6 => (3753707 / 200000000000 : ℝ)
  | 7 => (4645021 / 250000000000 : ℝ)
  | 8 => (18383563 / 1000000000000 : ℝ)
  | 9 => (145431 / 8000000000 : ℝ)
  | 10 => (112287 / 6250000000 : ℝ)
  | 11 => (17744603 / 1000000000000 : ℝ)
  | 12 => (700593 / 40000000000 : ℝ)
  | 13 => (17276489 / 1000000000000 : ℝ)
  | 14 => (17029499 / 1000000000000 : ℝ)
  | 15 => (8386879 / 500000000000 : ℝ)
  | 16 => (16509171 / 1000000000000 : ℝ)
  | 17 => (16235641 / 1000000000000 : ℝ)
  | 18 => (7976537 / 500000000000 : ℝ)
  | 19 => (125291 / 8000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch015Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3974003 / 200000000000 : ℝ)
  | 1 => (4933823 / 250000000000 : ℝ)
  | 2 => (1959319 / 100000000000 : ℝ)
  | 3 => (1944361 / 100000000000 : ℝ)
  | 4 => (19286453 / 1000000000000 : ℝ)
  | 5 => (19121621 / 1000000000000 : ℝ)
  | 6 => (3789803 / 200000000000 : ℝ)
  | 7 => (2346067 / 125000000000 : ℝ)
  | 8 => (3716017 / 200000000000 : ℝ)
  | 9 => (4595891 / 250000000000 : ℝ)
  | 10 => (4544719 / 250000000000 : ℝ)
  | 11 => (17965921 / 1000000000000 : ℝ)
  | 12 => (4436151 / 250000000000 : ℝ)
  | 13 => (8757413 / 500000000000 : ℝ)
  | 14 => (1727649 / 100000000000 : ℝ)
  | 15 => (34059 / 2000000000 : ℝ)
  | 16 => (16773759 / 1000000000000 : ℝ)
  | 17 => (4127293 / 250000000000 : ℝ)
  | 18 => (8117821 / 500000000000 : ℝ)
  | 19 => (638123 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch015Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((300 : ℝ) + (j.val : ℝ)) / 1600)
      (((300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch015Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch015Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((300 : ℝ) + (j.val : ℝ)) / 1600)
    (((300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch015Neg100WeightLower j.val) (hpThetaShiftTwoBatch015Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch015Neg100WeightLower, hpThetaShiftTwoBatch015Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch015Neg100_integral_bounds :
    (278495427 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (142550939 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch015Lower hpThetaJensenCellsBatch015Upper
    hpThetaShiftTwoBatch015Neg100WeightLower hpThetaShiftTwoBatch015Neg100WeightUpper hpThetaJensenCellsBatch015_bounds hpThetaShiftTwoBatch015Neg100_weight_bounds
  have hl : (278495427 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch015Lower j * hpThetaShiftTwoBatch015Neg100WeightLower j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftTwoBatch015Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftTwoBatch015Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch015Lower j * hpThetaShiftTwoBatch015Neg100WeightUpper j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftTwoBatch015Neg100WeightUpper j) / 1600) ≤ (142550939 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftTwoBatch015Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (300 : ℝ) / 1600 = 15 / 80 by norm_num,
    show ((300 : ℝ) + 20) / 1600 = (15 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch015Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (43425163 / 1000000000000 : ℝ)
  | 1 => (21837889 / 500000000000 : ℝ)
  | 2 => (2196159 / 50000000000 : ℝ)
  | 3 => (11041819 / 250000000000 : ℝ)
  | 4 => (22203987 / 500000000000 : ℝ)
  | 5 => (44645179 / 1000000000000 : ℝ)
  | 6 => (8975759 / 200000000000 : ℝ)
  | 7 => (45108727 / 1000000000000 : ℝ)
  | 8 => (22667439 / 500000000000 : ℝ)
  | 9 => (911143 / 20000000000 : ℝ)
  | 10 => (45775447 / 1000000000000 : ℝ)
  | 11 => (11497417 / 250000000000 : ℝ)
  | 12 => (11549929 / 250000000000 : ℝ)
  | 13 => (46405489 / 1000000000000 : ℝ)
  | 14 => (23303443 / 500000000000 : ℝ)
  | 15 => (1462619 / 31250000000 : ℝ)
  | 16 => (46996151 / 1000000000000 : ℝ)
  | 17 => (11795953 / 250000000000 : ℝ)
  | 18 => (47366689 / 1000000000000 : ℝ)
  | 19 => (47544677 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch015Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (43675779 / 1000000000000 : ℝ)
  | 1 => (43923181 / 1000000000000 : ℝ)
  | 2 => (44167277 / 1000000000000 : ℝ)
  | 3 => (1776319 / 40000000000 : ℝ)
  | 4 => (2232259 / 50000000000 : ℝ)
  | 5 => (11219699 / 250000000000 : ℝ)
  | 6 => (5638591 / 125000000000 : ℝ)
  | 7 => (45334879 / 1000000000000 : ℝ)
  | 8 => (45557151 / 1000000000000 : ℝ)
  | 9 => (5721931 / 125000000000 : ℝ)
  | 10 => (45989669 / 1000000000000 : ℝ)
  | 11 => (46199717 / 1000000000000 : ℝ)
  | 12 => (4640549 / 100000000000 : ℝ)
  | 13 => (46606887 / 1000000000000 : ℝ)
  | 14 => (46803809 / 1000000000000 : ℝ)
  | 15 => (5874519 / 125000000000 : ℝ)
  | 16 => (47183813 / 1000000000000 : ℝ)
  | 17 => (4736669 / 100000000000 : ℝ)
  | 18 => (23772339 / 500000000000 : ℝ)
  | 19 => (5964709 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch015Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((300 : ℝ) + (j.val : ℝ)) / 1600)
      (((300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch015Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch015Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((300 : ℝ) + (j.val : ℝ)) / 1600)
    (((300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch015Neg65WeightLower j.val) (hpThetaShiftTwoBatch015Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch015Neg65WeightLower, hpThetaShiftTwoBatch015Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch015Neg65_integral_bounds :
    (707133597 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (718923207 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch015Lower hpThetaJensenCellsBatch015Upper
    hpThetaShiftTwoBatch015Neg65WeightLower hpThetaShiftTwoBatch015Neg65WeightUpper hpThetaJensenCellsBatch015_bounds hpThetaShiftTwoBatch015Neg65_weight_bounds
  have hl : (707133597 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch015Lower j * hpThetaShiftTwoBatch015Neg65WeightLower j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftTwoBatch015Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftTwoBatch015Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch015Lower j * hpThetaShiftTwoBatch015Neg65WeightUpper j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftTwoBatch015Neg65WeightUpper j) / 1600) ≤ (718923207 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftTwoBatch015Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (300 : ℝ) / 1600 = 15 / 80 by norm_num,
    show ((300 : ℝ) + 20) / 1600 = (15 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch015Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1189513 / 20000000000 : ℝ)
  | 1 => (60013533 / 1000000000000 : ℝ)
  | 2 => (60552067 / 1000000000000 : ℝ)
  | 3 => (61091191 / 1000000000000 : ℝ)
  | 4 => (61630841 / 1000000000000 : ℝ)
  | 5 => (62170953 / 1000000000000 : ℝ)
  | 6 => (31355731 / 500000000000 : ℝ)
  | 7 => (63252303 / 1000000000000 : ℝ)
  | 8 => (249193 / 3906250000 : ℝ)
  | 9 => (64334709 / 1000000000000 : ℝ)
  | 10 => (3243807 / 50000000000 : ℝ)
  | 11 => (6541763 / 100000000000 : ℝ)
  | 12 => (6595911 / 100000000000 : ℝ)
  | 13 => (16625127 / 250000000000 : ℝ)
  | 14 => (33520877 / 500000000000 : ℝ)
  | 15 => (2703311 / 40000000000 : ℝ)
  | 16 => (68123497 / 1000000000000 : ℝ)
  | 17 => (34331923 / 500000000000 : ℝ)
  | 18 => (17300937 / 250000000000 : ℝ)
  | 19 => (34871563 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch015Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (30006767 / 500000000000 : ℝ)
  | 1 => (15138017 / 250000000000 : ℝ)
  | 2 => (7636399 / 125000000000 : ℝ)
  | 3 => (30815421 / 500000000000 : ℝ)
  | 4 => (31085477 / 500000000000 : ℝ)
  | 5 => (62711463 / 1000000000000 : ℝ)
  | 6 => (3953269 / 62500000000 : ℝ)
  | 7 => (63793409 / 1000000000000 : ℝ)
  | 8 => (6433471 / 100000000000 : ℝ)
  | 9 => (64876141 / 1000000000000 : ℝ)
  | 10 => (65417631 / 1000000000000 : ℝ)
  | 11 => (65959111 / 1000000000000 : ℝ)
  | 12 => (66500509 / 1000000000000 : ℝ)
  | 13 => (13408351 / 200000000000 : ℝ)
  | 14 => (8447847 / 125000000000 : ℝ)
  | 15 => (34061749 / 500000000000 : ℝ)
  | 16 => (68663847 / 1000000000000 : ℝ)
  | 17 => (69203749 / 1000000000000 : ℝ)
  | 18 => (69743127 / 1000000000000 : ℝ)
  | 19 => (14056381 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch015Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((300 : ℝ) + (j.val : ℝ)) / 1600)
      (((300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch015Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch015Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((300 : ℝ) + (j.val : ℝ)) / 1600)
    (((300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch015Neg45WeightLower j.val) (hpThetaShiftTwoBatch015Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch015Neg45WeightLower, hpThetaShiftTwoBatch015Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch015Neg45_integral_bounds :
    (1001598213 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (255500093 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch015Lower hpThetaJensenCellsBatch015Upper
    hpThetaShiftTwoBatch015Neg45WeightLower hpThetaShiftTwoBatch015Neg45WeightUpper hpThetaJensenCellsBatch015_bounds hpThetaShiftTwoBatch015Neg45_weight_bounds
  have hl : (1001598213 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch015Lower j * hpThetaShiftTwoBatch015Neg45WeightLower j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftTwoBatch015Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftTwoBatch015Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch015Lower j * hpThetaShiftTwoBatch015Neg45WeightUpper j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftTwoBatch015Neg45WeightUpper j) / 1600) ≤ (255500093 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftTwoBatch015Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (300 : ℝ) / 1600 = 15 / 80 by norm_num,
    show ((300 : ℝ) + 20) / 1600 = (15 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch015Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (77516623 / 1000000000000 : ℝ)
  | 1 => (78394161 / 1000000000000 : ℝ)
  | 2 => (19819351 / 250000000000 : ℝ)
  | 3 => (40083171 / 500000000000 : ℝ)
  | 4 => (16212193 / 200000000000 : ℝ)
  | 5 => (40980631 / 500000000000 : ℝ)
  | 6 => (41433611 / 500000000000 : ℝ)
  | 7 => (83778833 / 1000000000000 : ℝ)
  | 8 => (84696083 / 1000000000000 : ℝ)
  | 9 => (85618959 / 1000000000000 : ℝ)
  | 10 => (86547447 / 1000000000000 : ℝ)
  | 11 => (87481533 / 1000000000000 : ℝ)
  | 12 => (88421201 / 1000000000000 : ℝ)
  | 13 => (44683219 / 500000000000 : ℝ)
  | 14 => (45158613 / 500000000000 : ℝ)
  | 15 => (91273549 / 1000000000000 : ℝ)
  | 16 => (9223539 / 100000000000 : ℝ)
  | 17 => (93202731 / 1000000000000 : ℝ)
  | 18 => (47087777 / 500000000000 : ℝ)
  | 19 => (47576919 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch015Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (39197081 / 500000000000 : ℝ)
  | 1 => (15855481 / 200000000000 : ℝ)
  | 2 => (80166343 / 1000000000000 : ℝ)
  | 3 => (40530483 / 500000000000 : ℝ)
  | 4 => (81961263 / 1000000000000 : ℝ)
  | 5 => (82867223 / 1000000000000 : ℝ)
  | 6 => (41889417 / 500000000000 : ℝ)
  | 7 => (21174021 / 250000000000 : ℝ)
  | 8 => (1070237 / 12500000000 : ℝ)
  | 9 => (10818431 / 125000000000 : ℝ)
  | 10 => (43740767 / 500000000000 : ℝ)
  | 11 => (44210601 / 500000000000 : ℝ)
  | 12 => (89366439 / 1000000000000 : ℝ)
  | 13 => (90317227 / 1000000000000 : ℝ)
  | 14 => (1825471 / 20000000000 : ℝ)
  | 15 => (92235391 / 1000000000000 : ℝ)
  | 16 => (23300683 / 250000000000 : ℝ)
  | 17 => (18835111 / 200000000000 : ℝ)
  | 18 => (95153839 / 1000000000000 : ℝ)
  | 19 => (96137567 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch015Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((300 : ℝ) + (j.val : ℝ)) / 1600)
      (((300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch015Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch015Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((300 : ℝ) + (j.val : ℝ)) / 1600)
    (((300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch015Neg25WeightLower j.val) (hpThetaShiftTwoBatch015Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch015Neg25WeightLower, hpThetaShiftTwoBatch015Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch015Neg25_integral_bounds :
    (1335723351 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (1366229569 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch015Lower hpThetaJensenCellsBatch015Upper
    hpThetaShiftTwoBatch015Neg25WeightLower hpThetaShiftTwoBatch015Neg25WeightUpper hpThetaJensenCellsBatch015_bounds hpThetaShiftTwoBatch015Neg25_weight_bounds
  have hl : (1335723351 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch015Lower j * hpThetaShiftTwoBatch015Neg25WeightLower j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftTwoBatch015Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftTwoBatch015Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch015Lower j * hpThetaShiftTwoBatch015Neg25WeightUpper j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftTwoBatch015Neg25WeightUpper j) / 1600) ≤ (1366229569 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftTwoBatch015Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (300 : ℝ) / 1600 = 15 / 80 by norm_num,
    show ((300 : ℝ) + 20) / 1600 = (15 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch015Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch015Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch015Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch015Neg25_integral_bounds
end HodgeProofHP
