/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch020

/-! Exact signed weight and batch integral certificates, batch 20 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch020Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (163163 / 1000000000000 : ℝ)
  | 1 => (19997 / 125000000000 : ℝ)
  | 2 => (156673 / 1000000000000 : ℝ)
  | 3 => (613 / 4000000000 : ℝ)
  | 4 => (149707 / 1000000000000 : ℝ)
  | 5 => (146041 / 1000000000000 : ℝ)
  | 6 => (142251 / 1000000000000 : ℝ)
  | 7 => (4323 / 31250000000 : ℝ)
  | 8 => (33573 / 250000000000 : ℝ)
  | 9 => (130119 / 1000000000000 : ℝ)
  | 10 => (25163 / 200000000000 : ℝ)
  | 11 => (121379 / 1000000000000 : ℝ)
  | 12 => (116807 / 1000000000000 : ℝ)
  | 13 => (1121 / 10000000000 : ℝ)
  | 14 => (53627 / 500000000000 : ℝ)
  | 15 => (25567 / 250000000000 : ℝ)
  | 16 => (97141 / 1000000000000 : ℝ)
  | 17 => (91871 / 1000000000000 : ℝ)
  | 18 => (10807 / 125000000000 : ℝ)
  | 19 => (40447 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch020Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (83117 / 500000000000 : ℝ)
  | 1 => (40791 / 250000000000 : ℝ)
  | 2 => (159977 / 1000000000000 : ℝ)
  | 3 => (78337 / 500000000000 : ℝ)
  | 4 => (153251 / 1000000000000 : ℝ)
  | 5 => (37427 / 250000000000 : ℝ)
  | 6 => (73021 / 500000000000 : ℝ)
  | 7 => (35563 / 250000000000 : ℝ)
  | 8 => (138337 / 1000000000000 : ℝ)
  | 9 => (134293 / 1000000000000 : ℝ)
  | 10 => (3253 / 25000000000 : ℝ)
  | 11 => (15727 / 125000000000 : ℝ)
  | 12 => (6069 / 50000000000 : ℝ)
  | 13 => (14601 / 125000000000 : ℝ)
  | 14 => (112101 / 1000000000000 : ℝ)
  | 15 => (21451 / 200000000000 : ℝ)
  | 16 => (102269 / 1000000000000 : ℝ)
  | 17 => (48571 / 500000000000 : ℝ)
  | 18 => (2871 / 31250000000 : ℝ)
  | 19 => (86457 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch020Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((400 : ℝ) + (j.val : ℝ)) / 1600)
      (((400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch020Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch020Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((400 : ℝ) + (j.val : ℝ)) / 1600)
    (((400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch020Neg100WeightLower j.val) (hpThetaShiftThreeBatch020Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch020Neg100WeightLower, hpThetaShiftThreeBatch020Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch020Neg100_integral_bounds :
    (1479589 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (387167 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch020Lower hpThetaJensenCellsBatch020Upper
    hpThetaShiftThreeBatch020Neg100WeightLower hpThetaShiftThreeBatch020Neg100WeightUpper hpThetaJensenCellsBatch020_bounds hpThetaShiftThreeBatch020Neg100_weight_bounds
  have hl : (1479589 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch020Lower j * hpThetaShiftThreeBatch020Neg100WeightLower j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftThreeBatch020Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftThreeBatch020Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch020Lower j * hpThetaShiftThreeBatch020Neg100WeightUpper j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftThreeBatch020Neg100WeightUpper j) / 1600) ≤ (387167 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftThreeBatch020Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (400 : ℝ) / 1600 = 20 / 80 by norm_num,
    show ((400 : ℝ) + 20) / 1600 = (20 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch020Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (560017 / 1000000000000 : ℝ)
  | 1 => (56303 / 100000000000 : ℝ)
  | 2 => (565991 / 1000000000000 : ℝ)
  | 3 => (568897 / 1000000000000 : ℝ)
  | 4 => (142937 / 250000000000 : ℝ)
  | 5 => (287271 / 500000000000 : ℝ)
  | 6 => (577277 / 1000000000000 : ℝ)
  | 7 => (11599 / 20000000000 : ℝ)
  | 8 => (291281 / 500000000000 : ℝ)
  | 9 => (585109 / 1000000000000 : ℝ)
  | 10 => (58759 / 100000000000 : ℝ)
  | 11 => (590003 / 1000000000000 : ℝ)
  | 12 => (592347 / 1000000000000 : ℝ)
  | 13 => (594619 / 1000000000000 : ℝ)
  | 14 => (298409 / 500000000000 : ℝ)
  | 15 => (598941 / 1000000000000 : ℝ)
  | 16 => (150247 / 250000000000 : ℝ)
  | 17 => (120591 / 200000000000 : ℝ)
  | 18 => (604841 / 1000000000000 : ℝ)
  | 19 => (121329 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch020Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (563031 / 1000000000000 : ℝ)
  | 1 => (70749 / 125000000000 : ℝ)
  | 2 => (284449 / 500000000000 : ℝ)
  | 3 => (571749 / 1000000000000 : ℝ)
  | 4 => (574543 / 1000000000000 : ℝ)
  | 5 => (288639 / 500000000000 : ℝ)
  | 6 => (579951 / 1000000000000 : ℝ)
  | 7 => (582563 / 1000000000000 : ℝ)
  | 8 => (58511 / 100000000000 : ℝ)
  | 9 => (587591 / 1000000000000 : ℝ)
  | 10 => (147501 / 250000000000 : ℝ)
  | 11 => (148087 / 250000000000 : ℝ)
  | 12 => (29731 / 50000000000 : ℝ)
  | 13 => (596819 / 1000000000000 : ℝ)
  | 14 => (299471 / 500000000000 : ℝ)
  | 15 => (600989 / 1000000000000 : ℝ)
  | 16 => (150739 / 250000000000 : ℝ)
  | 17 => (302421 / 500000000000 : ℝ)
  | 18 => (303323 / 500000000000 : ℝ)
  | 19 => (152091 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch020Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((400 : ℝ) + (j.val : ℝ)) / 1600)
      (((400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch020Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch020Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((400 : ℝ) + (j.val : ℝ)) / 1600)
    (((400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch020Neg70WeightLower j.val) (hpThetaShiftThreeBatch020Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch020Neg70WeightLower, hpThetaShiftThreeBatch020Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch020Neg70_integral_bounds :
    (1713833 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (6970361 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch020Lower hpThetaJensenCellsBatch020Upper
    hpThetaShiftThreeBatch020Neg70WeightLower hpThetaShiftThreeBatch020Neg70WeightUpper hpThetaJensenCellsBatch020_bounds hpThetaShiftThreeBatch020Neg70_weight_bounds
  have hl : (1713833 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch020Lower j * hpThetaShiftThreeBatch020Neg70WeightLower j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftThreeBatch020Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftThreeBatch020Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch020Lower j * hpThetaShiftThreeBatch020Neg70WeightUpper j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftThreeBatch020Neg70WeightUpper j) / 1600) ≤ (6970361 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftThreeBatch020Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (400 : ℝ) / 1600 = 20 / 80 by norm_num,
    show ((400 : ℝ) + 20) / 1600 = (20 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch020Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (495887 / 500000000000 : ℝ)
  | 1 => (50117 / 50000000000 : ℝ)
  | 2 => (1012959 / 1000000000000 : ℝ)
  | 3 => (1023629 / 1000000000000 : ℝ)
  | 4 => (1034351 / 1000000000000 : ℝ)
  | 5 => (261281 / 250000000000 : ℝ)
  | 6 => (527973 / 500000000000 : ℝ)
  | 7 => (533409 / 500000000000 : ℝ)
  | 8 => (538869 / 500000000000 : ℝ)
  | 9 => (544353 / 500000000000 : ℝ)
  | 10 => (1099721 / 1000000000000 : ℝ)
  | 11 => (1110781 / 1000000000000 : ℝ)
  | 12 => (1121887 / 1000000000000 : ℝ)
  | 13 => (566519 / 500000000000 : ℝ)
  | 14 => (143029 / 125000000000 : ℝ)
  | 15 => (288867 / 250000000000 : ℝ)
  | 16 => (583373 / 500000000000 : ℝ)
  | 17 => (235613 / 200000000000 : ℝ)
  | 18 => (74339 / 62500000000 : ℝ)
  | 19 => (600411 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch020Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1002341 / 1000000000000 : ℝ)
  | 1 => (6331 / 6250000000 : ℝ)
  | 2 => (102363 / 100000000000 : ℝ)
  | 3 => (64647 / 62500000000 : ℝ)
  | 4 => (8361 / 8000000000 : ℝ)
  | 5 => (1055947 / 1000000000000 : ℝ)
  | 6 => (1066819 / 1000000000000 : ℝ)
  | 7 => (1077739 / 1000000000000 : ℝ)
  | 8 => (1088707 / 1000000000000 : ℝ)
  | 9 => (549861 / 500000000000 : ℝ)
  | 10 => (555391 / 500000000000 : ℝ)
  | 11 => (35059 / 31250000000 : ℝ)
  | 12 => (1133039 / 1000000000000 : ℝ)
  | 13 => (1144233 / 1000000000000 : ℝ)
  | 14 => (1155469 / 1000000000000 : ℝ)
  | 15 => (1166747 / 1000000000000 : ℝ)
  | 16 => (589033 / 500000000000 : ℝ)
  | 17 => (47577 / 40000000000 : ℝ)
  | 18 => (1200823 / 1000000000000 : ℝ)
  | 19 => (606129 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch020Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((400 : ℝ) + (j.val : ℝ)) / 1600)
      (((400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch020Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch020Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((400 : ℝ) + (j.val : ℝ)) / 1600)
    (((400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch020Neg45WeightLower j.val) (hpThetaShiftThreeBatch020Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch020Neg45WeightLower, hpThetaShiftThreeBatch020Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch020Neg45_integral_bounds :
    (6409047 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (6555071 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch020Lower hpThetaJensenCellsBatch020Upper
    hpThetaShiftThreeBatch020Neg45WeightLower hpThetaShiftThreeBatch020Neg45WeightUpper hpThetaJensenCellsBatch020_bounds hpThetaShiftThreeBatch020Neg45_weight_bounds
  have hl : (6409047 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch020Lower j * hpThetaShiftThreeBatch020Neg45WeightLower j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftThreeBatch020Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftThreeBatch020Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch020Lower j * hpThetaShiftThreeBatch020Neg45WeightUpper j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftThreeBatch020Neg45WeightUpper j) / 1600) ≤ (6555071 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftThreeBatch020Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (400 : ℝ) / 1600 = 20 / 80 by norm_num,
    show ((400 : ℝ) + 20) / 1600 = (20 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch020Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (8819 / 6250000000 : ℝ)
  | 1 => (714729 / 500000000000 : ℝ)
  | 2 => (362013 / 250000000000 : ℝ)
  | 3 => (733411 / 500000000000 : ℝ)
  | 4 => (1485771 / 1000000000000 : ℝ)
  | 5 => (752449 / 500000000000 : ℝ)
  | 6 => (381051 / 250000000000 : ℝ)
  | 7 => (1543691 / 1000000000000 : ℝ)
  | 8 => (1563359 / 1000000000000 : ℝ)
  | 9 => (1583209 / 1000000000000 : ℝ)
  | 10 => (1603241 / 1000000000000 : ℝ)
  | 11 => (811729 / 500000000000 : ℝ)
  | 12 => (821929 / 500000000000 : ℝ)
  | 13 => (416111 / 250000000000 : ℝ)
  | 14 => (1685217 / 1000000000000 : ℝ)
  | 15 => (68247 / 40000000000 : ℝ)
  | 16 => (863661 / 500000000000 : ℝ)
  | 17 => (1748657 / 1000000000000 : ℝ)
  | 18 => (1770181 / 1000000000000 : ℝ)
  | 19 => (358379 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch020Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1429459 / 1000000000000 : ℝ)
  | 1 => (1448053 / 1000000000000 : ℝ)
  | 2 => (1466823 / 1000000000000 : ℝ)
  | 3 => (371443 / 250000000000 : ℝ)
  | 4 => (1504899 / 1000000000000 : ℝ)
  | 5 => (304841 / 200000000000 : ℝ)
  | 6 => (385923 / 250000000000 : ℝ)
  | 7 => (9771 / 6250000000 : ℝ)
  | 8 => (158321 / 100000000000 : ℝ)
  | 9 => (801621 / 500000000000 : ℝ)
  | 10 => (1623459 / 1000000000000 : ℝ)
  | 11 => (1643859 / 1000000000000 : ℝ)
  | 12 => (332889 / 200000000000 : ℝ)
  | 13 => (842609 / 500000000000 : ℝ)
  | 14 => (26659 / 15625000000 : ℝ)
  | 15 => (1727323 / 1000000000000 : ℝ)
  | 16 => (874329 / 500000000000 : ℝ)
  | 17 => (885091 / 500000000000 : ℝ)
  | 18 => (223987 / 125000000000 : ℝ)
  | 19 => (1813801 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch020Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((400 : ℝ) + (j.val : ℝ)) / 1600)
      (((400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch020Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch020Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((400 : ℝ) + (j.val : ℝ)) / 1600)
    (((400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch020Neg25WeightLower j.val) (hpThetaShiftThreeBatch020Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch020Neg25WeightLower, hpThetaShiftThreeBatch020Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch020Neg25_integral_bounds :
    (291891 / 15625000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (2394353 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch020Lower hpThetaJensenCellsBatch020Upper
    hpThetaShiftThreeBatch020Neg25WeightLower hpThetaShiftThreeBatch020Neg25WeightUpper hpThetaJensenCellsBatch020_bounds hpThetaShiftThreeBatch020Neg25_weight_bounds
  have hl : (291891 / 15625000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch020Lower j * hpThetaShiftThreeBatch020Neg25WeightLower j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftThreeBatch020Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftThreeBatch020Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch020Lower j * hpThetaShiftThreeBatch020Neg25WeightUpper j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftThreeBatch020Neg25WeightUpper j) / 1600) ≤ (2394353 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftThreeBatch020Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (400 : ℝ) / 1600 = 20 / 80 by norm_num,
    show ((400 : ℝ) + 20) / 1600 = (20 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch020Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch020Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch020Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch020Neg25_integral_bounds
end HodgeProofHP
