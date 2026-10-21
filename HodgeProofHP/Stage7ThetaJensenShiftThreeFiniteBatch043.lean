/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch043

/-! Exact signed weight and batch integral certificates, batch 43 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch043Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (79595667 / 1000000000000 : ℝ)
  | 1 => (80447457 / 1000000000000 : ℝ)
  | 2 => (81300011 / 1000000000000 : ℝ)
  | 3 => (20538287 / 250000000000 : ℝ)
  | 4 => (41503343 / 500000000000 : ℝ)
  | 5 => (20965109 / 250000000000 : ℝ)
  | 6 => (21178551 / 250000000000 : ℝ)
  | 7 => (17113559 / 200000000000 : ℝ)
  | 8 => (21605251 / 250000000000 : ℝ)
  | 9 => (43636813 / 500000000000 : ℝ)
  | 10 => (1762509 / 20000000000 : ℝ)
  | 11 => (88976257 / 1000000000000 : ℝ)
  | 12 => (89825827 / 1000000000000 : ℝ)
  | 13 => (45336967 / 500000000000 : ℝ)
  | 14 => (18304069 / 200000000000 : ℝ)
  | 15 => (92364823 / 1000000000000 : ℝ)
  | 16 => (93207127 / 1000000000000 : ℝ)
  | 17 => (94047009 / 1000000000000 : ℝ)
  | 18 => (18976843 / 200000000000 : ℝ)
  | 19 => (11964811 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch043Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (40223729 / 500000000000 : ℝ)
  | 1 => (20325003 / 250000000000 : ℝ)
  | 2 => (82153149 / 1000000000000 : ℝ)
  | 3 => (83006687 / 1000000000000 : ℝ)
  | 4 => (83860437 / 1000000000000 : ℝ)
  | 5 => (16942841 / 200000000000 : ℝ)
  | 6 => (21391949 / 250000000000 : ℝ)
  | 7 => (17284201 / 200000000000 : ℝ)
  | 8 => (87273627 / 1000000000000 : ℝ)
  | 9 => (88125451 / 1000000000000 : ℝ)
  | 10 => (44488129 / 500000000000 : ℝ)
  | 11 => (22456457 / 250000000000 : ℝ)
  | 12 => (18134787 / 200000000000 : ℝ)
  | 13 => (45760173 / 500000000000 : ℝ)
  | 14 => (11545603 / 125000000000 : ℝ)
  | 15 => (11650891 / 125000000000 : ℝ)
  | 16 => (9404701 / 100000000000 : ℝ)
  | 17 => (11860527 / 125000000000 : ℝ)
  | 18 => (95718489 / 1000000000000 : ℝ)
  | 19 => (19309913 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch043Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((860 : ℝ) + (j.val : ℝ)) / 1600)
      (((860 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch043Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch043Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((860 : ℝ) + (j.val : ℝ)) / 1600)
    (((860 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch043Neg100WeightLower j.val) (hpThetaShiftThreeBatch043Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch043Neg100WeightLower, hpThetaShiftThreeBatch043Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch043Neg100_integral_bounds :
    (37220511 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (76477449 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (860 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch043Lower hpThetaJensenCellsBatch043Upper
    hpThetaShiftThreeBatch043Neg100WeightLower hpThetaShiftThreeBatch043Neg100WeightUpper hpThetaJensenCellsBatch043_bounds hpThetaShiftThreeBatch043Neg100_weight_bounds
  have hl : (37220511 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch043Lower j * hpThetaShiftThreeBatch043Neg100WeightLower j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftThreeBatch043Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftThreeBatch043Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch043Lower j * hpThetaShiftThreeBatch043Neg100WeightUpper j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftThreeBatch043Neg100WeightUpper j) / 1600) ≤ (76477449 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftThreeBatch043Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (860 : ℝ) / 1600 = 43 / 80 by norm_num,
    show ((860 : ℝ) + 20) / 1600 = (43 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch043Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (8720719 / 1000000000000 : ℝ)
  | 1 => (57621 / 6250000000 : ℝ)
  | 2 => (9725831 / 1000000000000 : ℝ)
  | 3 => (10240197 / 1000000000000 : ℝ)
  | 4 => (10762519 / 1000000000000 : ℝ)
  | 5 => (5646431 / 500000000000 : ℝ)
  | 6 => (11831287 / 1000000000000 : ℝ)
  | 7 => (6188929 / 500000000000 : ℝ)
  | 8 => (6466319 / 500000000000 : ℝ)
  | 9 => (13495689 / 1000000000000 : ℝ)
  | 10 => (7033537 / 500000000000 : ℝ)
  | 11 => (2929371 / 200000000000 : ℝ)
  | 12 => (7617547 / 500000000000 : ℝ)
  | 13 => (3166371 / 200000000000 : ℝ)
  | 14 => (16437197 / 1000000000000 : ℝ)
  | 15 => (1065699 / 62500000000 : ℝ)
  | 16 => (17673877 / 1000000000000 : ℝ)
  | 17 => (18305337 / 1000000000000 : ℝ)
  | 18 => (9472813 / 500000000000 : ℝ)
  | 19 => (4898701 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch043Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (9219361 / 1000000000000 : ℝ)
  | 1 => (1215729 / 125000000000 : ℝ)
  | 2 => (5120099 / 500000000000 : ℝ)
  | 3 => (269063 / 25000000000 : ℝ)
  | 4 => (11292863 / 1000000000000 : ℝ)
  | 5 => (1478911 / 125000000000 : ℝ)
  | 6 => (12377859 / 1000000000000 : ℝ)
  | 7 => (12932639 / 1000000000000 : ℝ)
  | 8 => (1349569 / 100000000000 : ℝ)
  | 9 => (562683 / 40000000000 : ℝ)
  | 10 => (1830857 / 125000000000 : ℝ)
  | 11 => (3047019 / 200000000000 : ℝ)
  | 12 => (989491 / 62500000000 : ℝ)
  | 13 => (8218599 / 500000000000 : ℝ)
  | 14 => (3410237 / 200000000000 : ℝ)
  | 15 => (8836939 / 500000000000 : ℝ)
  | 16 => (9152669 / 500000000000 : ℝ)
  | 17 => (18945627 / 1000000000000 : ℝ)
  | 18 => (3918961 / 200000000000 : ℝ)
  | 19 => (5063233 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch043Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((860 : ℝ) + (j.val : ℝ)) / 1600)
      (((860 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch043Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch043Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((860 : ℝ) + (j.val : ℝ)) / 1600)
    (((860 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch043Neg70WeightLower j.val) (hpThetaShiftThreeBatch043Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch043Neg70WeightLower, hpThetaShiftThreeBatch043Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch043Neg70_integral_bounds :
    (11710797 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (12413177 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (860 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch043Lower hpThetaJensenCellsBatch043Upper
    hpThetaShiftThreeBatch043Neg70WeightLower hpThetaShiftThreeBatch043Neg70WeightUpper hpThetaJensenCellsBatch043_bounds hpThetaShiftThreeBatch043Neg70_weight_bounds
  have hl : (11710797 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch043Lower j * hpThetaShiftThreeBatch043Neg70WeightLower j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftThreeBatch043Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftThreeBatch043Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch043Lower j * hpThetaShiftThreeBatch043Neg70WeightUpper j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftThreeBatch043Neg70WeightUpper j) / 1600) ≤ (12413177 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftThreeBatch043Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (860 : ℝ) / 1600 = 43 / 80 by norm_num,
    show ((860 : ℝ) + 20) / 1600 = (43 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch043Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-34394899 / 1000000000000 : ℝ)
  | 1 => (-2163071 / 62500000000 : ℝ)
  | 2 => (-34822551 / 1000000000000 : ℝ)
  | 3 => (-3503511 / 100000000000 : ℝ)
  | 4 => (-4405847 / 125000000000 : ℝ)
  | 5 => (-4432189 / 125000000000 : ℝ)
  | 6 => (-17833641 / 500000000000 : ℝ)
  | 7 => (-35876049 / 1000000000000 : ℝ)
  | 8 => (-18041887 / 500000000000 : ℝ)
  | 9 => (-1814521 / 50000000000 : ℝ)
  | 10 => (-9123987 / 250000000000 : ℝ)
  | 11 => (-36700319 / 1000000000000 : ℝ)
  | 12 => (-36903493 / 1000000000000 : ℝ)
  | 13 => (-4638179 / 125000000000 : ℝ)
  | 14 => (-37306093 / 1000000000000 : ℝ)
  | 15 => (-37505437 / 1000000000000 : ℝ)
  | 16 => (-37703423 / 1000000000000 : ℝ)
  | 17 => (-4737501 / 125000000000 : ℝ)
  | 18 => (-2380947 / 62500000000 : ℝ)
  | 19 => (-3828881 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch043Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-273439 / 8000000000 : ℝ)
  | 1 => (-17197449 / 500000000000 : ℝ)
  | 2 => (-6921827 / 200000000000 : ℝ)
  | 3 => (-696451 / 20000000000 : ℝ)
  | 4 => (-35035109 / 1000000000000 : ℝ)
  | 5 => (-1409871 / 40000000000 : ℝ)
  | 6 => (-35457511 / 1000000000000 : ℝ)
  | 7 => (-35667281 / 1000000000000 : ℝ)
  | 8 => (-2242253 / 62500000000 : ℝ)
  | 9 => (-36083773 / 1000000000000 : ℝ)
  | 10 => (-36290419 / 1000000000000 : ℝ)
  | 11 => (-36495947 / 1000000000000 : ℝ)
  | 12 => (-18350159 / 500000000000 : ℝ)
  | 13 => (-9225873 / 250000000000 : ℝ)
  | 14 => (-37105431 / 1000000000000 : ℝ)
  | 15 => (-9326523 / 250000000000 : ℝ)
  | 16 => (-9376359 / 250000000000 : ℝ)
  | 17 => (-18851711 / 500000000000 : ℝ)
  | 18 => (-37900007 / 1000000000000 : ℝ)
  | 19 => (-38095151 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch043Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((860 : ℝ) + (j.val : ℝ)) / 1600)
      (((860 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch043Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch043Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((860 : ℝ) + (j.val : ℝ)) / 1600)
    (((860 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch043Neg45WeightLower j.val) (hpThetaShiftThreeBatch043Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch043Neg45WeightLower, hpThetaShiftThreeBatch043Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch043Neg45_integral_bounds :
    (-786429 / 25000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-30741351 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (860 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch043Lower hpThetaJensenCellsBatch043Upper
    hpThetaShiftThreeBatch043Neg45WeightLower hpThetaShiftThreeBatch043Neg45WeightUpper hpThetaJensenCellsBatch043_bounds hpThetaShiftThreeBatch043Neg45_weight_bounds
  have hl : (-786429 / 25000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch043Lower j * hpThetaShiftThreeBatch043Neg45WeightLower j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftThreeBatch043Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftThreeBatch043Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch043Lower j * hpThetaShiftThreeBatch043Neg45WeightUpper j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftThreeBatch043Neg45WeightUpper j) / 1600) ≤ (-30741351 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftThreeBatch043Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (860 : ℝ) / 1600 = 43 / 80 by norm_num,
    show ((860 : ℝ) + 20) / 1600 = (43 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch043Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (211221 / 250000000000 : ℝ)
  | 1 => (610289 / 1000000000000 : ℝ)
  | 2 => (186509 / 500000000000 : ℝ)
  | 3 => (133057 / 1000000000000 : ℝ)
  | 4 => (-54803 / 500000000000 : ℝ)
  | 5 => (-70997 / 200000000000 : ℝ)
  | 6 => (-603093 / 1000000000000 : ℝ)
  | 7 => (-106743 / 125000000000 : ℝ)
  | 8 => (-1107551 / 1000000000000 : ℝ)
  | 9 => (-681963 / 500000000000 : ℝ)
  | 10 => (-1623083 / 1000000000000 : ℝ)
  | 11 => (-377007 / 200000000000 : ℝ)
  | 12 => (-537449 / 250000000000 : ℝ)
  | 13 => (-2417377 / 1000000000000 : ℝ)
  | 14 => (-167987 / 62500000000 : ℝ)
  | 15 => (-592211 / 200000000000 : ℝ)
  | 16 => (-404647 / 125000000000 : ℝ)
  | 17 => (-3516171 / 1000000000000 : ℝ)
  | 18 => (-3798051 / 1000000000000 : ℝ)
  | 19 => (-1020707 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch043Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (538409 / 500000000000 : ℝ)
  | 1 => (168977 / 200000000000 : ℝ)
  | 2 => (61029 / 100000000000 : ℝ)
  | 3 => (373019 / 1000000000000 : ℝ)
  | 4 => (66529 / 500000000000 : ℝ)
  | 5 => (-21921 / 200000000000 : ℝ)
  | 6 => (-44373 / 125000000000 : ℝ)
  | 7 => (-150773 / 250000000000 : ℝ)
  | 8 => (-853943 / 1000000000000 : ℝ)
  | 9 => (-22151 / 20000000000 : ℝ)
  | 10 => (-54557 / 40000000000 : ℝ)
  | 11 => (-811541 / 500000000000 : ℝ)
  | 12 => (-942517 / 500000000000 : ℝ)
  | 13 => (-429959 / 200000000000 : ℝ)
  | 14 => (-75543 / 31250000000 : ℝ)
  | 15 => (-2687791 / 1000000000000 : ℝ)
  | 16 => (-1480527 / 500000000000 : ℝ)
  | 17 => (-129487 / 40000000000 : ℝ)
  | 18 => (-351617 / 100000000000 : ℝ)
  | 19 => (-75961 / 20000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch043Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((860 : ℝ) + (j.val : ℝ)) / 1600)
      (((860 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch043Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch043Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((860 : ℝ) + (j.val : ℝ)) / 1600)
    (((860 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch043Neg25WeightLower j.val) (hpThetaShiftThreeBatch043Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch043Neg25WeightLower, hpThetaShiftThreeBatch043Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch043Neg25_integral_bounds :
    (-158877 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-1026179 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (860 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch043Lower hpThetaJensenCellsBatch043Upper
    hpThetaShiftThreeBatch043Neg25WeightLower hpThetaShiftThreeBatch043Neg25WeightUpper hpThetaJensenCellsBatch043_bounds hpThetaShiftThreeBatch043Neg25_weight_bounds
  have hl : (-158877 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch043Lower j * hpThetaShiftThreeBatch043Neg25WeightLower j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftThreeBatch043Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftThreeBatch043Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch043Lower j * hpThetaShiftThreeBatch043Neg25WeightUpper j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftThreeBatch043Neg25WeightUpper j) / 1600) ≤ (-1026179 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftThreeBatch043Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (860 : ℝ) / 1600 = 43 / 80 by norm_num,
    show ((860 : ℝ) + 20) / 1600 = (43 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch043Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch043Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch043Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch043Neg25_integral_bounds
end HodgeProofHP
