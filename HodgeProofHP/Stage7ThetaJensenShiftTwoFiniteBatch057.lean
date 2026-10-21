/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch057

/-! Exact signed weight and batch integral certificates, batch 57 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch057Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-118841583851 / 500000000000 : ℝ)
  | 1 => (-120418702353 / 500000000000 : ℝ)
  | 2 => (-48805141059 / 200000000000 : ℝ)
  | 3 => (-247248374079 / 1000000000000 : ℝ)
  | 4 => (-125252858963 / 500000000000 : ℝ)
  | 5 => (-253798045977 / 1000000000000 : ℝ)
  | 6 => (-128562834827 / 500000000000 : ℝ)
  | 7 => (-130244451341 / 500000000000 : ℝ)
  | 8 => (-131944030549 / 500000000000 : ℝ)
  | 9 => (-8353858227 / 31250000000 : ℝ)
  | 10 => (-135397714943 / 500000000000 : ℝ)
  | 11 => (-34288035503 / 125000000000 : ℝ)
  | 12 => (-138925175553 / 500000000000 : ℝ)
  | 13 => (-140716979473 / 500000000000 : ℝ)
  | 14 => (-142527718877 / 500000000000 : ℝ)
  | 15 => (-144357560077 / 500000000000 : ℝ)
  | 16 => (-58482668239 / 200000000000 : ℝ)
  | 17 => (-296150438369 / 1000000000000 : ℝ)
  | 18 => (-37490843953 / 125000000000 : ℝ)
  | 19 => (-151871311689 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch057Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-46912538383 / 200000000000 : ℝ)
  | 1 => (-237683167701 / 1000000000000 : ℝ)
  | 2 => (-48167480941 / 200000000000 : ℝ)
  | 3 => (-122012852647 / 500000000000 : ℝ)
  | 4 => (-123624187039 / 500000000000 : ℝ)
  | 5 => (-10020228717 / 40000000000 : ℝ)
  | 6 => (-31724755747 / 125000000000 : ℝ)
  | 7 => (-257125669653 / 1000000000000 : ℝ)
  | 8 => (-260488902681 / 1000000000000 : ℝ)
  | 9 => (-263888061097 / 1000000000000 : ℝ)
  | 10 => (-267323463263 / 1000000000000 : ℝ)
  | 11 => (-54159085977 / 200000000000 : ℝ)
  | 12 => (-274304284023 / 1000000000000 : ℝ)
  | 13 => (-55570070221 / 200000000000 : ℝ)
  | 14 => (-56286791789 / 200000000000 : ℝ)
  | 15 => (-285055437753 / 1000000000000 : ℝ)
  | 16 => (-288715120153 / 1000000000000 : ℝ)
  | 17 => (-146206670597 / 500000000000 : ℝ)
  | 18 => (-9254701199 / 31250000000 : ℝ)
  | 19 => (-299926751623 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch057Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1140 : ℝ) + (j.val : ℝ)) / 1600)
      (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch057Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch057Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1140 : ℝ) + (j.val : ℝ)) / 1600)
    (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch057Neg100WeightLower j.val) (hpThetaShiftTwoBatch057Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch057Neg100WeightLower, hpThetaShiftTwoBatch057Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch057Neg100_integral_bounds :
    (-2179416187 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-5260802661 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch057Lower hpThetaJensenCellsBatch057Upper
    hpThetaShiftTwoBatch057Neg100WeightLower hpThetaShiftTwoBatch057Neg100WeightUpper hpThetaJensenCellsBatch057_bounds hpThetaShiftTwoBatch057Neg100_weight_bounds
  have hl : (-2179416187 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch057Lower j * hpThetaShiftTwoBatch057Neg100WeightLower j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftTwoBatch057Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftTwoBatch057Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch057Lower j * hpThetaShiftTwoBatch057Neg100WeightUpper j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftTwoBatch057Neg100WeightUpper j) / 1600) ≤ (-5260802661 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftTwoBatch057Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1140 : ℝ) / 1600 = 57 / 80 by norm_num,
    show ((1140 : ℝ) + 20) / 1600 = (57 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch057Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3552208149 / 1000000000000 : ℝ)
  | 1 => (3332533851 / 1000000000000 : ℝ)
  | 2 => (3108432243 / 1000000000000 : ℝ)
  | 3 => (179990633 / 62500000000 : ℝ)
  | 4 => (1323366919 / 500000000000 : ℝ)
  | 5 => (1204514617 / 500000000000 : ℝ)
  | 6 => (1083340849 / 500000000000 : ℝ)
  | 7 => (383927227 / 200000000000 : ℝ)
  | 8 => (833918483 / 500000000000 : ℝ)
  | 9 => (451593 / 320000000 : ℝ)
  | 10 => (57487653 / 50000000000 : ℝ)
  | 11 => (883354723 / 1000000000000 : ℝ)
  | 12 => (611975573 / 1000000000000 : ℝ)
  | 13 => (335557567 / 1000000000000 : ℝ)
  | 14 => (27021081 / 500000000000 : ℝ)
  | 15 => (-232629693 / 1000000000000 : ℝ)
  | 16 => (-524517557 / 1000000000000 : ℝ)
  | 17 => (-821681501 / 1000000000000 : ℝ)
  | 18 => (-224836423 / 200000000000 : ℝ)
  | 19 => (-286416101 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch057Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (376750787 / 100000000000 : ℝ)
  | 1 => (71044163 / 20000000000 : ℝ)
  | 2 => (833133463 / 250000000000 : ℝ)
  | 3 => (777108061 / 250000000000 : ℝ)
  | 4 => (2879850129 / 1000000000000 : ℝ)
  | 5 => (2646733839 / 1000000000000 : ℝ)
  | 6 => (481805847 / 200000000000 : ℝ)
  | 7 => (2166681699 / 1000000000000 : ℝ)
  | 8 => (239954517 / 125000000000 : ℝ)
  | 9 => (1667836967 / 1000000000000 : ℝ)
  | 10 => (705614063 / 500000000000 : ℝ)
  | 11 => (1149753061 / 1000000000000 : ℝ)
  | 12 => (220838681 / 250000000000 : ℝ)
  | 13 => (305987787 / 500000000000 : ℝ)
  | 14 => (5243087 / 15625000000 : ℝ)
  | 15 => (54042163 / 1000000000000 : ℝ)
  | 16 => (-58157423 / 250000000000 : ℝ)
  | 17 => (-131129389 / 250000000000 : ℝ)
  | 18 => (-1643363 / 2000000000 : ℝ)
  | 19 => (-562091057 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch057Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1140 : ℝ) + (j.val : ℝ)) / 1600)
      (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch057Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch057Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1140 : ℝ) + (j.val : ℝ)) / 1600)
    (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch057Neg65WeightLower j.val) (hpThetaShiftTwoBatch057Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch057Neg65WeightLower, hpThetaShiftTwoBatch057Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch057Neg65_integral_bounds :
    (52215597 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (32065707 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch057Lower hpThetaJensenCellsBatch057Upper
    hpThetaShiftTwoBatch057Neg65WeightLower hpThetaShiftTwoBatch057Neg65WeightUpper hpThetaJensenCellsBatch057_bounds hpThetaShiftTwoBatch057Neg65_weight_bounds
  have hl : (52215597 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch057Lower j * hpThetaShiftTwoBatch057Neg65WeightLower j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftTwoBatch057Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftTwoBatch057Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch057Lower j * hpThetaShiftTwoBatch057Neg65WeightUpper j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftTwoBatch057Neg65WeightUpper j) / 1600) ≤ (32065707 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftTwoBatch057Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1140 : ℝ) / 1600 = 57 / 80 by norm_num,
    show ((1140 : ℝ) + 20) / 1600 = (57 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch057Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (12857791111 / 1000000000000 : ℝ)
  | 1 => (647634491 / 50000000000 : ℝ)
  | 2 => (6523847701 / 500000000000 : ℝ)
  | 3 => (821425077 / 62500000000 : ℝ)
  | 4 => (2647600117 / 200000000000 : ℝ)
  | 5 => (6666643321 / 500000000000 : ℝ)
  | 6 => (6714326241 / 500000000000 : ℝ)
  | 7 => (2704818217 / 200000000000 : ℝ)
  | 8 => (3404898833 / 250000000000 : ℝ)
  | 9 => (6857579001 / 500000000000 : ℝ)
  | 10 => (13810771771 / 1000000000000 : ℝ)
  | 11 => (434575913 / 31250000000 : ℝ)
  | 12 => (3500530701 / 250000000000 : ℝ)
  | 13 => (1762230613 / 125000000000 : ℝ)
  | 14 => (7096793887 / 500000000000 : ℝ)
  | 15 => (1428934357 / 100000000000 : ℝ)
  | 16 => (14385104337 / 1000000000000 : ℝ)
  | 17 => (2896172403 / 200000000000 : ℝ)
  | 18 => (14576608433 / 1000000000000 : ℝ)
  | 19 => (917020957 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch057Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (12952689821 / 1000000000000 : ℝ)
  | 1 => (13047695403 / 1000000000000 : ℝ)
  | 2 => (13142801233 / 1000000000000 : ℝ)
  | 3 => (6619000293 / 500000000000 : ℝ)
  | 4 => (13333286643 / 1000000000000 : ℝ)
  | 5 => (13428652483 / 1000000000000 : ℝ)
  | 6 => (6762045543 / 500000000000 : ℝ)
  | 7 => (13619595333 / 1000000000000 : ℝ)
  | 8 => (13715158003 / 1000000000000 : ℝ)
  | 9 => (3452692943 / 250000000000 : ℝ)
  | 10 => (13906429217 / 1000000000000 : ℝ)
  | 11 => (2800424561 / 200000000000 : ℝ)
  | 12 => (2819568981 / 200000000000 : ℝ)
  | 13 => (567743511 / 40000000000 : ℝ)
  | 14 => (14289343571 / 1000000000000 : ℝ)
  | 15 => (7192552169 / 500000000000 : ℝ)
  | 16 => (226263469 / 15625000000 : ℝ)
  | 17 => (7288304217 / 500000000000 : ℝ)
  | 18 => (14672335313 / 1000000000000 : ℝ)
  | 19 => (14768034261 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch057Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1140 : ℝ) + (j.val : ℝ)) / 1600)
      (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch057Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch057Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1140 : ℝ) + (j.val : ℝ)) / 1600)
    (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch057Neg45WeightLower j.val) (hpThetaShiftTwoBatch057Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch057Neg45WeightLower, hpThetaShiftTwoBatch057Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch057Neg45_integral_bounds :
    (27273573 / 50000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (22462491 / 40000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch057Lower hpThetaJensenCellsBatch057Upper
    hpThetaShiftTwoBatch057Neg45WeightLower hpThetaShiftTwoBatch057Neg45WeightUpper hpThetaJensenCellsBatch057_bounds hpThetaShiftTwoBatch057Neg45_weight_bounds
  have hl : (27273573 / 50000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch057Lower j * hpThetaShiftTwoBatch057Neg45WeightLower j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftTwoBatch057Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftTwoBatch057Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch057Lower j * hpThetaShiftTwoBatch057Neg45WeightUpper j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftTwoBatch057Neg45WeightUpper j) / 1600) ≤ (22462491 / 40000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftTwoBatch057Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1140 : ℝ) / 1600 = 57 / 80 by norm_num,
    show ((1140 : ℝ) + 20) / 1600 = (57 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch057Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3588354667 / 1000000000000 : ℝ)
  | 1 => (-715170273 / 200000000000 : ℝ)
  | 2 => (-3563047621 / 1000000000000 : ℝ)
  | 3 => (-3549941359 / 1000000000000 : ℝ)
  | 4 => (-3536530497 / 1000000000000 : ℝ)
  | 5 => (-3522812951 / 1000000000000 : ℝ)
  | 6 => (-3508786631 / 1000000000000 : ℝ)
  | 7 => (-3494449443 / 1000000000000 : ℝ)
  | 8 => (-3479799287 / 1000000000000 : ℝ)
  | 9 => (-1732417031 / 500000000000 : ℝ)
  | 10 => (-3449551661 / 1000000000000 : ℝ)
  | 11 => (-3433949971 / 1000000000000 : ℝ)
  | 12 => (-3418026879 / 1000000000000 : ℝ)
  | 13 => (-3401780263 / 1000000000000 : ℝ)
  | 14 => (-1692604001 / 500000000000 : ℝ)
  | 15 => (-3368307967 / 1000000000000 : ℝ)
  | 16 => (-1675539013 / 500000000000 : ℝ)
  | 17 => (-1666758023 / 500000000000 : ℝ)
  | 18 => (-1657809943 / 500000000000 : ℝ)
  | 19 => (-824346851 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch057Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-893962841 / 250000000000 : ℝ)
  | 1 => (-178152381 / 50000000000 : ℝ)
  | 2 => (-1774970679 / 500000000000 : ℝ)
  | 3 => (-55258289 / 15625000000 : ℝ)
  | 4 => (-70456259 / 20000000000 : ℝ)
  | 5 => (-350878663 / 100000000000 : ℝ)
  | 6 => (-1747224721 / 500000000000 : ℝ)
  | 7 => (-1739899643 / 500000000000 : ℝ)
  | 8 => (-3464834061 / 1000000000000 : ℝ)
  | 9 => (-172477583 / 50000000000 : ℝ)
  | 10 => (-343394997 / 100000000000 : ℝ)
  | 11 => (-1709013439 / 500000000000 : ℝ)
  | 12 => (-1700890131 / 500000000000 : ℝ)
  | 13 => (-3385208001 / 1000000000000 : ℝ)
  | 14 => (-1684153983 / 500000000000 : ℝ)
  | 15 => (-134043121 / 40000000000 : ℝ)
  | 16 => (-666703209 / 200000000000 : ℝ)
  | 17 => (-663123977 / 200000000000 : ℝ)
  | 18 => (-3297387403 / 1000000000000 : ℝ)
  | 19 => (-3278816453 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch057Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1140 : ℝ) + (j.val : ℝ)) / 1600)
      (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch057Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch057Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1140 : ℝ) + (j.val : ℝ)) / 1600)
    (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch057Neg25WeightLower j.val) (hpThetaShiftTwoBatch057Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch057Neg25WeightLower, hpThetaShiftTwoBatch057Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch057Neg25_integral_bounds :
    (-7029187 / 50000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-68448687 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch057Lower hpThetaJensenCellsBatch057Upper
    hpThetaShiftTwoBatch057Neg25WeightLower hpThetaShiftTwoBatch057Neg25WeightUpper hpThetaJensenCellsBatch057_bounds hpThetaShiftTwoBatch057Neg25_weight_bounds
  have hl : (-7029187 / 50000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch057Lower j * hpThetaShiftTwoBatch057Neg25WeightLower j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftTwoBatch057Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftTwoBatch057Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch057Lower j * hpThetaShiftTwoBatch057Neg25WeightUpper j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftTwoBatch057Neg25WeightUpper j) / 1600) ≤ (-68448687 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftTwoBatch057Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1140 : ℝ) / 1600 = 57 / 80 by norm_num,
    show ((1140 : ℝ) + 20) / 1600 = (57 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch057Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch057Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch057Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch057Neg25_integral_bounds
end HodgeProofHP
