/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch007

/-! Exact signed weight and batch integral certificates, batch 7 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch007Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (197 / 62500000000 : ℝ)
  | 1 => (3281 / 1000000000000 : ℝ)
  | 2 => (1707 / 500000000000 : ℝ)
  | 3 => (111 / 31250000000 : ℝ)
  | 4 => (1847 / 500000000000 : ℝ)
  | 5 => (3 / 781250000 : ℝ)
  | 6 => (3991 / 1000000000000 : ℝ)
  | 7 => (4147 / 1000000000000 : ℝ)
  | 8 => (4307 / 1000000000000 : ℝ)
  | 9 => (4473 / 1000000000000 : ℝ)
  | 10 => (4643 / 1000000000000 : ℝ)
  | 11 => (4819 / 1000000000000 : ℝ)
  | 12 => (4999 / 1000000000000 : ℝ)
  | 13 => (1037 / 200000000000 : ℝ)
  | 14 => (5377 / 1000000000000 : ℝ)
  | 15 => (5573 / 1000000000000 : ℝ)
  | 16 => (361 / 62500000000 : ℝ)
  | 17 => (187 / 31250000000 : ℝ)
  | 18 => (3099 / 500000000000 : ℝ)
  | 19 => (6419 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch007Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1641 / 500000000000 : ℝ)
  | 1 => (683 / 200000000000 : ℝ)
  | 2 => (3553 / 1000000000000 : ℝ)
  | 3 => (739 / 200000000000 : ℝ)
  | 4 => (3841 / 1000000000000 : ℝ)
  | 5 => (499 / 125000000000 : ℝ)
  | 6 => (1037 / 250000000000 : ℝ)
  | 7 => (1077 / 250000000000 : ℝ)
  | 8 => (2237 / 500000000000 : ℝ)
  | 9 => (1161 / 250000000000 : ℝ)
  | 10 => (241 / 50000000000 : ℝ)
  | 11 => (1 / 200000000 : ℝ)
  | 12 => (2593 / 500000000000 : ℝ)
  | 13 => (2689 / 500000000000 : ℝ)
  | 14 => (2787 / 500000000000 : ℝ)
  | 15 => (5777 / 1000000000000 : ℝ)
  | 16 => (1197 / 200000000000 : ℝ)
  | 17 => (6199 / 1000000000000 : ℝ)
  | 18 => (321 / 50000000000 : ℝ)
  | 19 => (3323 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch007Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((140 : ℝ) + (j.val : ℝ)) / 1600)
      (((140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch007Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch007Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((140 : ℝ) + (j.val : ℝ)) / 1600)
    (((140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch007Neg100WeightLower j.val) (hpThetaShiftThreeBatch007Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch007Neg100WeightLower, hpThetaShiftThreeBatch007Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch007Neg100_integral_bounds :
    (94863 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (12443 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch007Lower hpThetaJensenCellsBatch007Upper
    hpThetaShiftThreeBatch007Neg100WeightLower hpThetaShiftThreeBatch007Neg100WeightUpper hpThetaJensenCellsBatch007_bounds hpThetaShiftThreeBatch007Neg100_weight_bounds
  have hl : (94863 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch007Lower j * hpThetaShiftThreeBatch007Neg100WeightLower j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftThreeBatch007Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftThreeBatch007Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch007Lower j * hpThetaShiftThreeBatch007Neg100WeightUpper j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftThreeBatch007Neg100WeightUpper j) / 1600) ≤ (12443 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftThreeBatch007Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (140 : ℝ) / 1600 = 7 / 80 by norm_num,
    show ((140 : ℝ) + 20) / 1600 = (7 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch007Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3323 / 1000000000000 : ℝ)
  | 1 => (1731 / 500000000000 : ℝ)
  | 2 => (721 / 200000000000 : ℝ)
  | 3 => (1877 / 500000000000 : ℝ)
  | 4 => (3907 / 1000000000000 : ℝ)
  | 5 => (813 / 200000000000 : ℝ)
  | 6 => (4229 / 1000000000000 : ℝ)
  | 7 => (4397 / 1000000000000 : ℝ)
  | 8 => (1143 / 250000000000 : ℝ)
  | 9 => (4751 / 1000000000000 : ℝ)
  | 10 => (4937 / 1000000000000 : ℝ)
  | 11 => (641 / 125000000000 : ℝ)
  | 12 => (213 / 40000000000 : ℝ)
  | 13 => (691 / 125000000000 : ℝ)
  | 14 => (5737 / 1000000000000 : ℝ)
  | 15 => (5953 / 1000000000000 : ℝ)
  | 16 => (247 / 40000000000 : ℝ)
  | 17 => (1601 / 250000000000 : ℝ)
  | 18 => (6639 / 1000000000000 : ℝ)
  | 19 => (3441 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch007Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3463 / 1000000000000 : ℝ)
  | 1 => (1803 / 500000000000 : ℝ)
  | 2 => (751 / 200000000000 : ℝ)
  | 3 => (977 / 250000000000 : ℝ)
  | 4 => (2033 / 500000000000 : ℝ)
  | 5 => (423 / 100000000000 : ℝ)
  | 6 => (2199 / 500000000000 : ℝ)
  | 7 => (4573 / 1000000000000 : ℝ)
  | 8 => (297 / 62500000000 : ℝ)
  | 9 => (2469 / 500000000000 : ℝ)
  | 10 => (5129 / 1000000000000 : ℝ)
  | 11 => (2663 / 500000000000 : ℝ)
  | 12 => (5529 / 1000000000000 : ℝ)
  | 13 => (2869 / 500000000000 : ℝ)
  | 14 => (2977 / 500000000000 : ℝ)
  | 15 => (193 / 31250000000 : ℝ)
  | 16 => (1281 / 200000000000 : ℝ)
  | 17 => (83 / 12500000000 : ℝ)
  | 18 => (6883 / 1000000000000 : ℝ)
  | 19 => (1783 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch007Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((140 : ℝ) + (j.val : ℝ)) / 1600)
      (((140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch007Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch007Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((140 : ℝ) + (j.val : ℝ)) / 1600)
    (((140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch007Neg70WeightLower j.val) (hpThetaShiftThreeBatch007Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch007Neg70WeightLower, hpThetaShiftThreeBatch007Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch007Neg70_integral_bounds :
    (100939 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (53007 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch007Lower hpThetaJensenCellsBatch007Upper
    hpThetaShiftThreeBatch007Neg70WeightLower hpThetaShiftThreeBatch007Neg70WeightUpper hpThetaJensenCellsBatch007_bounds hpThetaShiftThreeBatch007Neg70_weight_bounds
  have hl : (100939 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch007Lower j * hpThetaShiftThreeBatch007Neg70WeightLower j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftThreeBatch007Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftThreeBatch007Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch007Lower j * hpThetaShiftThreeBatch007Neg70WeightUpper j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftThreeBatch007Neg70WeightUpper j) / 1600) ≤ (53007 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftThreeBatch007Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (140 : ℝ) / 1600 = 7 / 80 by norm_num,
    show ((140 : ℝ) + 20) / 1600 = (7 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch007Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3469 / 1000000000000 : ℝ)
  | 1 => (113 / 31250000000 : ℝ)
  | 2 => (471 / 125000000000 : ℝ)
  | 3 => (1963 / 500000000000 : ℝ)
  | 4 => (4089 / 1000000000000 : ℝ)
  | 5 => (2129 / 500000000000 : ℝ)
  | 6 => (277 / 62500000000 : ℝ)
  | 7 => (1153 / 250000000000 : ℝ)
  | 8 => (2399 / 500000000000 : ℝ)
  | 9 => (499 / 100000000000 : ℝ)
  | 10 => (1297 / 250000000000 : ℝ)
  | 11 => (5393 / 1000000000000 : ℝ)
  | 12 => (1401 / 250000000000 : ℝ)
  | 13 => (2911 / 500000000000 : ℝ)
  | 14 => (6047 / 1000000000000 : ℝ)
  | 15 => (6279 / 1000000000000 : ℝ)
  | 16 => (3259 / 500000000000 : ℝ)
  | 17 => (1691 / 250000000000 : ℝ)
  | 18 => (3509 / 500000000000 : ℝ)
  | 19 => (91 / 12500000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch007Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3617 / 1000000000000 : ℝ)
  | 1 => (3769 / 1000000000000 : ℝ)
  | 2 => (3927 / 1000000000000 : ℝ)
  | 3 => (409 / 100000000000 : ℝ)
  | 4 => (4259 / 1000000000000 : ℝ)
  | 5 => (4433 / 1000000000000 : ℝ)
  | 6 => (4613 / 1000000000000 : ℝ)
  | 7 => (4799 / 1000000000000 : ℝ)
  | 8 => (4991 / 1000000000000 : ℝ)
  | 9 => (5189 / 1000000000000 : ℝ)
  | 10 => (2697 / 500000000000 : ℝ)
  | 11 => (1121 / 200000000000 : ℝ)
  | 12 => (5823 / 1000000000000 : ℝ)
  | 13 => (189 / 31250000000 : ℝ)
  | 14 => (157 / 25000000000 : ℝ)
  | 15 => (6519 / 1000000000000 : ℝ)
  | 16 => (1353 / 200000000000 : ℝ)
  | 17 => (7019 / 1000000000000 : ℝ)
  | 18 => (7281 / 1000000000000 : ℝ)
  | 19 => (151 / 20000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch007Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((140 : ℝ) + (j.val : ℝ)) / 1600)
      (((140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch007Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch007Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((140 : ℝ) + (j.val : ℝ)) / 1600)
    (((140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch007Neg45WeightLower j.val) (hpThetaShiftThreeBatch007Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch007Neg45WeightLower, hpThetaShiftThreeBatch007Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch007Neg45_integral_bounds :
    (53073 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (111559 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch007Lower hpThetaJensenCellsBatch007Upper
    hpThetaShiftThreeBatch007Neg45WeightLower hpThetaShiftThreeBatch007Neg45WeightUpper hpThetaJensenCellsBatch007_bounds hpThetaShiftThreeBatch007Neg45_weight_bounds
  have hl : (53073 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch007Lower j * hpThetaShiftThreeBatch007Neg45WeightLower j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftThreeBatch007Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftThreeBatch007Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch007Lower j * hpThetaShiftThreeBatch007Neg45WeightUpper j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftThreeBatch007Neg45WeightUpper j) / 1600) ≤ (111559 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftThreeBatch007Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (140 : ℝ) / 1600 = 7 / 80 by norm_num,
    show ((140 : ℝ) + 20) / 1600 = (7 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch007Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (897 / 250000000000 : ℝ)
  | 1 => (1871 / 500000000000 : ℝ)
  | 2 => (1951 / 500000000000 : ℝ)
  | 3 => (4067 / 1000000000000 : ℝ)
  | 4 => (2119 / 500000000000 : ℝ)
  | 5 => (883 / 200000000000 : ℝ)
  | 6 => (2299 / 500000000000 : ℝ)
  | 7 => (4787 / 1000000000000 : ℝ)
  | 8 => (4983 / 1000000000000 : ℝ)
  | 9 => (1037 / 200000000000 : ℝ)
  | 10 => (2697 / 500000000000 : ℝ)
  | 11 => (561 / 100000000000 : ℝ)
  | 12 => (5833 / 1000000000000 : ℝ)
  | 13 => (6063 / 1000000000000 : ℝ)
  | 14 => (63 / 10000000000 : ℝ)
  | 15 => (3273 / 500000000000 : ℝ)
  | 16 => (6799 / 1000000000000 : ℝ)
  | 17 => (353 / 50000000000 : ℝ)
  | 18 => (7329 / 1000000000000 : ℝ)
  | 19 => (3803 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch007Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3743 / 1000000000000 : ℝ)
  | 1 => (3903 / 1000000000000 : ℝ)
  | 2 => (1017 / 250000000000 : ℝ)
  | 3 => (4239 / 1000000000000 : ℝ)
  | 4 => (69 / 15625000000 : ℝ)
  | 5 => (4599 / 1000000000000 : ℝ)
  | 6 => (1197 / 250000000000 : ℝ)
  | 7 => (623 / 125000000000 : ℝ)
  | 8 => (2593 / 500000000000 : ℝ)
  | 9 => (1079 / 200000000000 : ℝ)
  | 10 => (5611 / 1000000000000 : ℝ)
  | 11 => (2917 / 500000000000 : ℝ)
  | 12 => (379 / 62500000000 : ℝ)
  | 13 => (6301 / 1000000000000 : ℝ)
  | 14 => (6547 / 1000000000000 : ℝ)
  | 15 => (17 / 2500000000 : ℝ)
  | 16 => (7061 / 1000000000000 : ℝ)
  | 17 => (733 / 100000000000 : ℝ)
  | 18 => (7607 / 1000000000000 : ℝ)
  | 19 => (3947 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch007Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((140 : ℝ) + (j.val : ℝ)) / 1600)
      (((140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch007Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch007Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((140 : ℝ) + (j.val : ℝ)) / 1600)
    (((140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch007Neg25WeightLower j.val) (hpThetaShiftThreeBatch007Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch007Neg25WeightLower, hpThetaShiftThreeBatch007Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch007Neg25_integral_bounds :
    (11041 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (58051 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch007Lower hpThetaJensenCellsBatch007Upper
    hpThetaShiftThreeBatch007Neg25WeightLower hpThetaShiftThreeBatch007Neg25WeightUpper hpThetaJensenCellsBatch007_bounds hpThetaShiftThreeBatch007Neg25_weight_bounds
  have hl : (11041 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch007Lower j * hpThetaShiftThreeBatch007Neg25WeightLower j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftThreeBatch007Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftThreeBatch007Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch007Lower j * hpThetaShiftThreeBatch007Neg25WeightUpper j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftThreeBatch007Neg25WeightUpper j) / 1600) ≤ (58051 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftThreeBatch007Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (140 : ℝ) / 1600 = 7 / 80 by norm_num,
    show ((140 : ℝ) + 20) / 1600 = (7 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch007Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch007Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch007Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch007Neg25_integral_bounds
end HodgeProofHP
