/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch028

/-! Exact signed weight and batch integral certificates, batch 28 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch028Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2636517 / 1000000000000 : ℝ)
  | 1 => (-266699 / 100000000000 : ℝ)
  | 2 => (-2697447 / 1000000000000 : ℝ)
  | 3 => (-2727881 / 1000000000000 : ℝ)
  | 4 => (-1379141 / 500000000000 : ℝ)
  | 5 => (-1394321 / 500000000000 : ℝ)
  | 6 => (-1409477 / 500000000000 : ℝ)
  | 7 => (-356151 / 125000000000 : ℝ)
  | 8 => (-719849 / 250000000000 : ℝ)
  | 9 => (-2909509 / 1000000000000 : ℝ)
  | 10 => (-1469769 / 500000000000 : ℝ)
  | 11 => (-2969473 / 1000000000000 : ℝ)
  | 12 => (-374913 / 125000000000 : ℝ)
  | 13 => (-3029023 / 1000000000000 : ℝ)
  | 14 => (-152931 / 50000000000 : ℝ)
  | 15 => (-772021 / 250000000000 : ℝ)
  | 16 => (-623481 / 200000000000 : ℝ)
  | 17 => (-3146573 / 1000000000000 : ℝ)
  | 18 => (-3175577 / 1000000000000 : ℝ)
  | 19 => (-3204407 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch028Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-521207 / 200000000000 : ℝ)
  | 1 => (-659129 / 250000000000 : ℝ)
  | 2 => (-2666989 / 1000000000000 : ℝ)
  | 3 => (-1348723 / 500000000000 : ℝ)
  | 4 => (-68197 / 25000000000 : ℝ)
  | 5 => (-2758281 / 1000000000000 : ℝ)
  | 6 => (-2788641 / 1000000000000 : ℝ)
  | 7 => (-2818953 / 1000000000000 : ℝ)
  | 8 => (-2849207 / 1000000000000 : ℝ)
  | 9 => (-575879 / 200000000000 : ℝ)
  | 10 => (-727377 / 250000000000 : ℝ)
  | 11 => (-2939537 / 1000000000000 : ℝ)
  | 12 => (-23199 / 7812500000 : ℝ)
  | 13 => (-2999303 / 1000000000000 : ℝ)
  | 14 => (-1514511 / 500000000000 : ℝ)
  | 15 => (-3058619 / 1000000000000 : ℝ)
  | 16 => (-3088083 / 1000000000000 : ℝ)
  | 17 => (-779351 / 250000000000 : ℝ)
  | 18 => (-786643 / 250000000000 : ℝ)
  | 19 => (-396947 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch028Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((560 : ℝ) + (j.val : ℝ)) / 1600)
      (((560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch028Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch028Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((560 : ℝ) + (j.val : ℝ)) / 1600)
    (((560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch028Neg100WeightLower j.val) (hpThetaShiftThreeBatch028Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch028Neg100WeightLower, hpThetaShiftThreeBatch028Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch028Neg100_integral_bounds :
    (-18254941 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-3563883 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch028Lower hpThetaJensenCellsBatch028Upper
    hpThetaShiftThreeBatch028Neg100WeightLower hpThetaShiftThreeBatch028Neg100WeightUpper hpThetaJensenCellsBatch028_bounds hpThetaShiftThreeBatch028Neg100_weight_bounds
  have hl : (-18254941 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch028Lower j * hpThetaShiftThreeBatch028Neg100WeightLower j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftThreeBatch028Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftThreeBatch028Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch028Lower j * hpThetaShiftThreeBatch028Neg100WeightUpper j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftThreeBatch028Neg100WeightUpper j) / 1600) ≤ (-3563883 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftThreeBatch028Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (560 : ℝ) / 1600 = 28 / 80 by norm_num,
    show ((560 : ℝ) + 20) / 1600 = (28 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch028Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-29957 / 25000000000 : ℝ)
  | 1 => (-9647 / 7812500000 : ℝ)
  | 2 => (-635901 / 500000000000 : ℝ)
  | 3 => (-654619 / 500000000000 : ℝ)
  | 4 => (-10777 / 8000000000 : ℝ)
  | 5 => (-692733 / 500000000000 : ℝ)
  | 6 => (-71213 / 50000000000 : ℝ)
  | 7 => (-1463509 / 1000000000000 : ℝ)
  | 8 => (-300643 / 200000000000 : ℝ)
  | 9 => (-771689 / 500000000000 : ℝ)
  | 10 => (-1583999 / 1000000000000 : ℝ)
  | 11 => (-1625079 / 1000000000000 : ℝ)
  | 12 => (-83331 / 50000000000 : ℝ)
  | 13 => (-1708621 / 1000000000000 : ℝ)
  | 14 => (-1751083 / 1000000000000 : ℝ)
  | 15 => (-224251 / 125000000000 : ℝ)
  | 16 => (-367479 / 200000000000 : ℝ)
  | 17 => (-376249 / 200000000000 : ℝ)
  | 18 => (-1925559 / 1000000000000 : ℝ)
  | 19 => (-61573 / 31250000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch028Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1162189 / 1000000000000 : ℝ)
  | 1 => (-1198279 / 1000000000000 : ℝ)
  | 2 => (-246963 / 200000000000 : ℝ)
  | 3 => (-1271801 / 1000000000000 : ℝ)
  | 4 => (-1309237 / 1000000000000 : ℝ)
  | 5 => (-336781 / 250000000000 : ℝ)
  | 6 => (-277093 / 200000000000 : ℝ)
  | 7 => (-1424259 / 1000000000000 : ℝ)
  | 8 => (-365877 / 250000000000 : ℝ)
  | 9 => (-751607 / 500000000000 : ℝ)
  | 10 => (-1543377 / 1000000000000 : ℝ)
  | 11 => (-791999 / 500000000000 : ℝ)
  | 12 => (-812539 / 500000000000 : ℝ)
  | 13 => (-1666619 / 1000000000000 : ℝ)
  | 14 => (-85431 / 50000000000 : ℝ)
  | 15 => (-875541 / 500000000000 : ℝ)
  | 16 => (-1794007 / 1000000000000 : ℝ)
  | 17 => (-918697 / 500000000000 : ℝ)
  | 18 => (-470311 / 250000000000 : ℝ)
  | 19 => (-962779 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch028Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((560 : ℝ) + (j.val : ℝ)) / 1600)
      (((560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch028Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch028Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((560 : ℝ) + (j.val : ℝ)) / 1600)
    (((560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch028Neg70WeightLower j.val) (hpThetaShiftThreeBatch028Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch028Neg70WeightLower, hpThetaShiftThreeBatch028Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch028Neg70_integral_bounds :
    (-9788237 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-9404837 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch028Lower hpThetaJensenCellsBatch028Upper
    hpThetaShiftThreeBatch028Neg70WeightLower hpThetaShiftThreeBatch028Neg70WeightUpper hpThetaJensenCellsBatch028_bounds hpThetaShiftThreeBatch028Neg70_weight_bounds
  have hl : (-9788237 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch028Lower j * hpThetaShiftThreeBatch028Neg70WeightLower j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftThreeBatch028Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftThreeBatch028Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch028Lower j * hpThetaShiftThreeBatch028Neg70WeightUpper j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftThreeBatch028Neg70WeightUpper j) / 1600) ≤ (-9404837 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftThreeBatch028Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (560 : ℝ) / 1600 = 28 / 80 by norm_num,
    show ((560 : ℝ) + 20) / 1600 = (28 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch028Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2296797 / 1000000000000 : ℝ)
  | 1 => (2290901 / 1000000000000 : ℝ)
  | 2 => (1142313 / 500000000000 : ℝ)
  | 3 => (455593 / 200000000000 : ℝ)
  | 4 => (1135457 / 500000000000 : ℝ)
  | 5 => (565867 / 250000000000 : ℝ)
  | 6 => (1127811 / 500000000000 : ℝ)
  | 7 => (224737 / 100000000000 : ℝ)
  | 8 => (559677 / 250000000000 : ℝ)
  | 9 => (2229631 / 1000000000000 : ℝ)
  | 10 => (2220133 / 1000000000000 : ℝ)
  | 11 => (2210209 / 1000000000000 : ℝ)
  | 12 => (439971 / 200000000000 : ℝ)
  | 13 => (273633 / 125000000000 : ℝ)
  | 14 => (272229 / 125000000000 : ℝ)
  | 15 => (2166153 / 1000000000000 : ℝ)
  | 16 => (1077011 / 500000000000 : ℝ)
  | 17 => (1070717 / 500000000000 : ℝ)
  | 18 => (4157 / 1953125000 : ℝ)
  | 19 => (422973 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch028Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1151159 / 500000000000 : ℝ)
  | 1 => (1148399 / 500000000000 : ℝ)
  | 2 => (1145451 / 500000000000 : ℝ)
  | 3 => (2284627 / 1000000000000 : ℝ)
  | 4 => (1138983 / 500000000000 : ℝ)
  | 5 => (454183 / 200000000000 : ℝ)
  | 6 => (2263469 / 1000000000000 : ℝ)
  | 7 => (2255623 / 1000000000000 : ℝ)
  | 8 => (2247371 / 1000000000000 : ℝ)
  | 9 => (2238709 / 1000000000000 : ℝ)
  | 10 => (17419 / 7812500000 : ℝ)
  | 11 => (1110067 / 500000000000 : ℝ)
  | 12 => (221021 / 100000000000 : ℝ)
  | 13 => (137491 / 62500000000 : ℝ)
  | 14 => (437813 / 200000000000 : ℝ)
  | 15 => (2177833 / 1000000000000 : ℝ)
  | 16 => (1083077 / 500000000000 : ℝ)
  | 17 => (2154023 / 1000000000000 : ℝ)
  | 18 => (428287 / 200000000000 : ℝ)
  | 19 => (425677 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch028Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((560 : ℝ) + (j.val : ℝ)) / 1600)
      (((560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch028Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch028Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((560 : ℝ) + (j.val : ℝ)) / 1600)
    (((560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch028Neg45WeightLower j.val) (hpThetaShiftThreeBatch028Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch028Neg45WeightLower, hpThetaShiftThreeBatch028Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch028Neg45_integral_bounds :
    (13692717 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (3485413 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch028Lower hpThetaJensenCellsBatch028Upper
    hpThetaShiftThreeBatch028Neg45WeightLower hpThetaShiftThreeBatch028Neg45WeightUpper hpThetaJensenCellsBatch028_bounds hpThetaShiftThreeBatch028Neg45_weight_bounds
  have hl : (13692717 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch028Lower j * hpThetaShiftThreeBatch028Neg45WeightLower j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftThreeBatch028Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftThreeBatch028Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch028Lower j * hpThetaShiftThreeBatch028Neg45WeightUpper j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftThreeBatch028Neg45WeightUpper j) / 1600) ≤ (3485413 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftThreeBatch028Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (560 : ℝ) / 1600 = 28 / 80 by norm_num,
    show ((560 : ℝ) + 20) / 1600 = (28 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch028Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1724227 / 250000000000 : ℝ)
  | 1 => (694633 / 100000000000 : ℝ)
  | 2 => (3497939 / 500000000000 : ℝ)
  | 3 => (1761387 / 250000000000 : ℝ)
  | 4 => (7095339 / 1000000000000 : ℝ)
  | 5 => (223289 / 31250000000 : ℝ)
  | 6 => (7195273 / 1000000000000 : ℝ)
  | 7 => (724541 / 100000000000 : ℝ)
  | 8 => (3647829 / 500000000000 : ℝ)
  | 9 => (7346013 / 1000000000000 : ℝ)
  | 10 => (3698237 / 500000000000 : ℝ)
  | 11 => (7447037 / 1000000000000 : ℝ)
  | 12 => (7497699 / 1000000000000 : ℝ)
  | 13 => (3774229 / 500000000000 : ℝ)
  | 14 => (7599311 / 1000000000000 : ℝ)
  | 15 => (1530051 / 200000000000 : ℝ)
  | 16 => (962661 / 125000000000 : ℝ)
  | 17 => (1550481 / 200000000000 : ℝ)
  | 18 => (1560721 / 200000000000 : ℝ)
  | 19 => (7854883 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch028Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (6946331 / 1000000000000 : ℝ)
  | 1 => (6995879 / 1000000000000 : ℝ)
  | 2 => (7045549 / 1000000000000 : ℝ)
  | 3 => (354767 / 50000000000 : ℝ)
  | 4 => (7145249 / 1000000000000 : ℝ)
  | 5 => (3597637 / 500000000000 : ℝ)
  | 6 => (7245411 / 1000000000000 : ℝ)
  | 7 => (7295659 / 1000000000000 : ℝ)
  | 8 => (3673007 / 500000000000 : ℝ)
  | 9 => (295859 / 40000000000 : ℝ)
  | 10 => (3723519 / 500000000000 : ℝ)
  | 11 => (74977 / 10000000000 : ℝ)
  | 12 => (7548459 / 1000000000000 : ℝ)
  | 13 => (474957 / 62500000000 : ℝ)
  | 14 => (478141 / 62500000000 : ℝ)
  | 15 => (7701289 / 1000000000000 : ℝ)
  | 16 => (3876203 / 500000000000 : ℝ)
  | 17 => (3901803 / 500000000000 : ℝ)
  | 18 => (1963721 / 250000000000 : ℝ)
  | 19 => (7906239 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch028Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((560 : ℝ) + (j.val : ℝ)) / 1600)
      (((560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch028Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch028Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((560 : ℝ) + (j.val : ℝ)) / 1600)
    (((560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch028Neg25WeightLower j.val) (hpThetaShiftThreeBatch028Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch028Neg25WeightLower, hpThetaShiftThreeBatch028Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch028Neg25_integral_bounds :
    (45437499 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (46386129 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch028Lower hpThetaJensenCellsBatch028Upper
    hpThetaShiftThreeBatch028Neg25WeightLower hpThetaShiftThreeBatch028Neg25WeightUpper hpThetaJensenCellsBatch028_bounds hpThetaShiftThreeBatch028Neg25_weight_bounds
  have hl : (45437499 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch028Lower j * hpThetaShiftThreeBatch028Neg25WeightLower j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftThreeBatch028Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftThreeBatch028Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch028Lower j * hpThetaShiftThreeBatch028Neg25WeightUpper j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftThreeBatch028Neg25WeightUpper j) / 1600) ≤ (46386129 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftThreeBatch028Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (560 : ℝ) / 1600 = 28 / 80 by norm_num,
    show ((560 : ℝ) + 20) / 1600 = (28 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch028Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch028Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch028Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch028Neg25_integral_bounds
end HodgeProofHP
