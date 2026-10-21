/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch009

/-! Exact signed weight and batch integral certificates, batch 9 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch009Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (8727609 / 1000000000000 : ℝ)
  | 1 => (8875569 / 1000000000000 : ℝ)
  | 2 => (9024517 / 1000000000000 : ℝ)
  | 3 => (2293607 / 250000000000 : ℝ)
  | 4 => (2331319 / 250000000000 : ℝ)
  | 5 => (9477033 / 1000000000000 : ℝ)
  | 6 => (9629673 / 1000000000000 : ℝ)
  | 7 => (9783167 / 1000000000000 : ℝ)
  | 8 => (1987497 / 200000000000 : ℝ)
  | 9 => (10092597 / 1000000000000 : ℝ)
  | 10 => (10248473 / 1000000000000 : ℝ)
  | 11 => (10405081 / 1000000000000 : ℝ)
  | 12 => (10562389 / 1000000000000 : ℝ)
  | 13 => (5360181 / 500000000000 : ℝ)
  | 14 => (10878969 / 1000000000000 : ℝ)
  | 15 => (2759543 / 250000000000 : ℝ)
  | 16 => (5598969 / 500000000000 : ℝ)
  | 17 => (11358229 / 1000000000000 : ℝ)
  | 18 => (11519009 / 1000000000000 : ℝ)
  | 19 => (5840119 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch009Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (887557 / 100000000000 : ℝ)
  | 1 => (4512259 / 500000000000 : ℝ)
  | 2 => (9174429 / 1000000000000 : ℝ)
  | 3 => (9325277 / 1000000000000 : ℝ)
  | 4 => (4738517 / 500000000000 : ℝ)
  | 5 => (4814837 / 500000000000 : ℝ)
  | 6 => (76431 / 7812500000 : ℝ)
  | 7 => (4968743 / 500000000000 : ℝ)
  | 8 => (5046299 / 500000000000 : ℝ)
  | 9 => (5124237 / 500000000000 : ℝ)
  | 10 => (5202541 / 500000000000 : ℝ)
  | 11 => (1056239 / 100000000000 : ℝ)
  | 12 => (10720363 / 1000000000000 : ℝ)
  | 13 => (1087897 / 100000000000 : ℝ)
  | 14 => (11038173 / 1000000000000 : ℝ)
  | 15 => (11197939 / 1000000000000 : ℝ)
  | 16 => (1135823 / 100000000000 : ℝ)
  | 17 => (1151901 / 100000000000 : ℝ)
  | 18 => (11680239 / 1000000000000 : ℝ)
  | 19 => (296047 / 25000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch009Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((180 : ℝ) + (j.val : ℝ)) / 1600)
      (((180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch009Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch009Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((180 : ℝ) + (j.val : ℝ)) / 1600)
    (((180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch009Neg100WeightLower j.val) (hpThetaShiftTwoBatch009Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch009Neg100WeightLower, hpThetaShiftTwoBatch009Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch009Neg100_integral_bounds :
    (49506127 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (8132597 / 40000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch009Lower hpThetaJensenCellsBatch009Upper
    hpThetaShiftTwoBatch009Neg100WeightLower hpThetaShiftTwoBatch009Neg100WeightUpper hpThetaJensenCellsBatch009_bounds hpThetaShiftTwoBatch009Neg100_weight_bounds
  have hl : (49506127 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch009Lower j * hpThetaShiftTwoBatch009Neg100WeightLower j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftTwoBatch009Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftTwoBatch009Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch009Lower j * hpThetaShiftTwoBatch009Neg100WeightUpper j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftTwoBatch009Neg100WeightUpper j) / 1600) ≤ (8132597 / 40000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftTwoBatch009Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (180 : ℝ) / 1600 = 9 / 80 by norm_num,
    show ((180 : ℝ) + 20) / 1600 = (9 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch009Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (5122339 / 500000000000 : ℝ)
  | 1 => (10441047 / 1000000000000 : ℝ)
  | 2 => (10639633 / 1000000000000 : ℝ)
  | 3 => (5420217 / 500000000000 : ℝ)
  | 4 => (5521723 / 500000000000 : ℝ)
  | 5 => (5624333 / 500000000000 : ℝ)
  | 6 => (1432011 / 125000000000 : ℝ)
  | 7 => (2916427 / 250000000000 : ℝ)
  | 8 => (11877521 / 1000000000000 : ℝ)
  | 9 => (12091519 / 1000000000000 : ℝ)
  | 10 => (769231 / 62500000000 : ℝ)
  | 11 => (2505209 / 200000000000 : ℝ)
  | 12 => (6373279 / 500000000000 : ℝ)
  | 13 => (12969227 / 1000000000000 : ℝ)
  | 14 => (13194041 / 1000000000000 : ℝ)
  | 15 => (209703 / 15625000000 : ℝ)
  | 16 => (3412517 / 250000000000 : ℝ)
  | 17 => (694063 / 50000000000 : ℝ)
  | 18 => (2822911 / 200000000000 : ℝ)
  | 19 => (7174971 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch009Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1305131 / 125000000000 : ℝ)
  | 1 => (5319817 / 500000000000 : ℝ)
  | 2 => (2168087 / 200000000000 : ℝ)
  | 3 => (11043447 / 1000000000000 : ℝ)
  | 4 => (11248667 / 1000000000000 : ℝ)
  | 5 => (11456089 / 1000000000000 : ℝ)
  | 6 => (11665709 / 1000000000000 : ℝ)
  | 7 => (5938761 / 500000000000 : ℝ)
  | 8 => (18893 / 1562500000 : ℝ)
  | 9 => (12307697 / 1000000000000 : ℝ)
  | 10 => (6263023 / 500000000000 : ℝ)
  | 11 => (12746559 / 1000000000000 : ℝ)
  | 12 => (3242307 / 250000000000 : ℝ)
  | 13 => (6597021 / 500000000000 : ℝ)
  | 14 => (13420993 / 1000000000000 : ℝ)
  | 15 => (13650069 / 1000000000000 : ℝ)
  | 16 => (13881261 / 1000000000000 : ℝ)
  | 17 => (3528639 / 250000000000 : ℝ)
  | 18 => (14349943 / 1000000000000 : ℝ)
  | 19 => (14587407 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch009Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((180 : ℝ) + (j.val : ℝ)) / 1600)
      (((180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch009Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch009Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((180 : ℝ) + (j.val : ℝ)) / 1600)
    (((180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch009Neg65WeightLower j.val) (hpThetaShiftTwoBatch009Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch009Neg65WeightLower, hpThetaShiftTwoBatch009Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch009Neg65_integral_bounds :
    (237915439 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (244861949 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch009Lower hpThetaJensenCellsBatch009Upper
    hpThetaShiftTwoBatch009Neg65WeightLower hpThetaShiftTwoBatch009Neg65WeightUpper hpThetaJensenCellsBatch009_bounds hpThetaShiftTwoBatch009Neg65_weight_bounds
  have hl : (237915439 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch009Lower j * hpThetaShiftTwoBatch009Neg65WeightLower j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftTwoBatch009Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftTwoBatch009Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch009Lower j * hpThetaShiftTwoBatch009Neg65WeightUpper j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftTwoBatch009Neg65WeightUpper j) / 1600) ≤ (244861949 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftTwoBatch009Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (180 : ℝ) / 1600 = 9 / 80 by norm_num,
    show ((180 : ℝ) + 20) / 1600 = (9 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch009Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (11159493 / 1000000000000 : ℝ)
  | 1 => (11385667 / 1000000000000 : ℝ)
  | 2 => (11614843 / 1000000000000 : ℝ)
  | 3 => (2961759 / 250000000000 : ℝ)
  | 4 => (755141 / 62500000000 : ℝ)
  | 5 => (2464103 / 200000000000 : ℝ)
  | 6 => (12561827 / 1000000000000 : ℝ)
  | 7 => (12806201 / 1000000000000 : ℝ)
  | 8 => (13053649 / 1000000000000 : ℝ)
  | 9 => (6652091 / 500000000000 : ℝ)
  | 10 => (13557809 / 1000000000000 : ℝ)
  | 11 => (13814541 / 1000000000000 : ℝ)
  | 12 => (7037193 / 500000000000 : ℝ)
  | 13 => (7168677 / 500000000000 : ℝ)
  | 14 => (7301727 / 500000000000 : ℝ)
  | 15 => (7436347 / 500000000000 : ℝ)
  | 16 => (15145081 / 1000000000000 : ℝ)
  | 17 => (7710311 / 500000000000 : ℝ)
  | 18 => (7849663 / 500000000000 : ℝ)
  | 19 => (15981199 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch009Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2846417 / 250000000000 : ℝ)
  | 1 => (2903711 / 250000000000 : ℝ)
  | 2 => (11847037 / 1000000000000 : ℝ)
  | 3 => (12082257 / 1000000000000 : ℝ)
  | 4 => (3080129 / 250000000000 : ℝ)
  | 5 => (3140457 / 250000000000 : ℝ)
  | 6 => (6403101 / 500000000000 : ℝ)
  | 7 => (261073 / 20000000000 : ℝ)
  | 8 => (13304183 / 1000000000000 : ℝ)
  | 9 => (1355781 / 100000000000 : ℝ)
  | 10 => (6907271 / 500000000000 : ℝ)
  | 11 => (14074387 / 1000000000000 : ℝ)
  | 12 => (2867471 / 200000000000 : ℝ)
  | 13 => (2920691 / 200000000000 : ℝ)
  | 14 => (2974539 / 200000000000 : ℝ)
  | 15 => (7572541 / 500000000000 : ℝ)
  | 16 => (15420623 / 1000000000000 : ℝ)
  | 17 => (15699327 / 1000000000000 : ℝ)
  | 18 => (39953 / 2500000000 : ℝ)
  | 19 => (8133123 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch009Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((180 : ℝ) + (j.val : ℝ)) / 1600)
      (((180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch009Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch009Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((180 : ℝ) + (j.val : ℝ)) / 1600)
    (((180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch009Neg45WeightLower j.val) (hpThetaShiftTwoBatch009Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch009Neg45WeightLower, hpThetaShiftTwoBatch009Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch009Neg45_integral_bounds :
    (52428391 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (270111861 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch009Lower hpThetaJensenCellsBatch009Upper
    hpThetaShiftTwoBatch009Neg45WeightLower hpThetaShiftTwoBatch009Neg45WeightUpper hpThetaJensenCellsBatch009_bounds hpThetaShiftTwoBatch009Neg45_weight_bounds
  have hl : (52428391 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch009Lower j * hpThetaShiftTwoBatch009Neg45WeightLower j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftTwoBatch009Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftTwoBatch009Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch009Lower j * hpThetaShiftTwoBatch009Neg45WeightUpper j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftTwoBatch009Neg45WeightUpper j) / 1600) ≤ (270111861 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftTwoBatch009Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (180 : ℝ) / 1600 = 9 / 80 by norm_num,
    show ((180 : ℝ) + 20) / 1600 = (9 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch009Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (6054901 / 500000000000 : ℝ)
  | 1 => (772961 / 62500000000 : ℝ)
  | 2 => (7893 / 625000000 : ℝ)
  | 3 => (2578821 / 200000000000 : ℝ)
  | 4 => (329083 / 25000000000 : ℝ)
  | 5 => (13436477 / 1000000000000 : ℝ)
  | 6 => (3428401 / 250000000000 : ℝ)
  | 7 => (3498683 / 250000000000 : ℝ)
  | 8 => (14279891 / 1000000000000 : ℝ)
  | 9 => (14569111 / 1000000000000 : ℝ)
  | 10 => (14862421 / 1000000000000 : ℝ)
  | 11 => (303197 / 20000000000 : ℝ)
  | 12 => (15461429 / 1000000000000 : ℝ)
  | 13 => (7883593 / 500000000000 : ℝ)
  | 14 => (321543 / 20000000000 : ℝ)
  | 15 => (16391351 / 1000000000000 : ℝ)
  | 16 => (16709817 / 1000000000000 : ℝ)
  | 17 => (17032577 / 1000000000000 : ℝ)
  | 18 => (867983 / 50000000000 : ℝ)
  | 19 => (8845547 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch009Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (12367377 / 1000000000000 : ℝ)
  | 1 => (12628801 / 1000000000000 : ℝ)
  | 2 => (6447053 / 500000000000 : ℝ)
  | 3 => (13163321 / 1000000000000 : ℝ)
  | 4 => (6718239 / 500000000000 : ℝ)
  | 5 => (2742721 / 200000000000 : ℝ)
  | 6 => (13994733 / 1000000000000 : ℝ)
  | 7 => (3569973 / 250000000000 : ℝ)
  | 8 => (1821139 / 125000000000 : ℝ)
  | 9 => (7431211 / 500000000000 : ℝ)
  | 10 => (15159851 / 1000000000000 : ℝ)
  | 11 => (1546143 / 100000000000 : ℝ)
  | 12 => (15767187 / 1000000000000 : ℝ)
  | 13 => (16077151 / 1000000000000 : ℝ)
  | 14 => (2048919 / 125000000000 : ℝ)
  | 15 => (8354909 / 500000000000 : ℝ)
  | 16 => (8516289 / 500000000000 : ℝ)
  | 17 => (17359661 / 1000000000000 : ℝ)
  | 18 => (3538219 / 200000000000 : ℝ)
  | 19 => (18026909 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch009Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((180 : ℝ) + (j.val : ℝ)) / 1600)
      (((180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch009Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch009Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((180 : ℝ) + (j.val : ℝ)) / 1600)
    (((180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch009Neg25WeightLower j.val) (hpThetaShiftTwoBatch009Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch009Neg25WeightLower, hpThetaShiftTwoBatch009Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch009Neg25_integral_bounds :
    (143715753 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (9 / 80 : ℝ) ((9 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (74120569 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch009Lower hpThetaJensenCellsBatch009Upper
    hpThetaShiftTwoBatch009Neg25WeightLower hpThetaShiftTwoBatch009Neg25WeightUpper hpThetaJensenCellsBatch009_bounds hpThetaShiftTwoBatch009Neg25_weight_bounds
  have hl : (143715753 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch009Lower j * hpThetaShiftTwoBatch009Neg25WeightLower j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftTwoBatch009Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftTwoBatch009Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch009Lower j * hpThetaShiftTwoBatch009Neg25WeightUpper j)
        (hpThetaJensenCellsBatch009Upper j * hpThetaShiftTwoBatch009Neg25WeightUpper j) / 1600) ≤ (74120569 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch009Lower, hpThetaJensenCellsBatch009Upper,
      hpThetaShiftTwoBatch009Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (180 : ℝ) / 1600 = 9 / 80 by norm_num,
    show ((180 : ℝ) + 20) / 1600 = (9 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch009Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch009Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch009Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch009Neg25_integral_bounds
end HodgeProofHP
