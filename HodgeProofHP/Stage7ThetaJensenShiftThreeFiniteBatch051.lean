/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch051

/-! Exact signed weight and batch integral certificates, batch 51 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch051Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-92804287 / 1000000000000 : ℝ)
  | 1 => (-24950579 / 250000000000 : ℝ)
  | 2 => (-21391839 / 200000000000 : ℝ)
  | 3 => (-114277443 / 1000000000000 : ℝ)
  | 4 => (-121759609 / 1000000000000 : ℝ)
  | 5 => (-32352069 / 250000000000 : ℝ)
  | 6 => (-17153257 / 125000000000 : ℝ)
  | 7 => (-145215597 / 1000000000000 : ℝ)
  | 8 => (-19172447 / 125000000000 : ℝ)
  | 9 => (-32344141 / 200000000000 : ℝ)
  | 10 => (-17024173 / 100000000000 : ℝ)
  | 11 => (-178945429 / 1000000000000 : ℝ)
  | 12 => (-23479327 / 125000000000 : ℝ)
  | 13 => (-98456069 / 500000000000 : ℝ)
  | 14 => (-206180877 / 1000000000000 : ℝ)
  | 15 => (-215643751 / 1000000000000 : ℝ)
  | 16 => (-7040741 / 31250000000 : ℝ)
  | 17 => (-235163749 / 1000000000000 : ℝ)
  | 18 => (-245226887 / 1000000000000 : ℝ)
  | 19 => (-255496187 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch051Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-85962621 / 1000000000000 : ℝ)
  | 1 => (-46402143 / 500000000000 : ℝ)
  | 2 => (-19960463 / 200000000000 : ℝ)
  | 3 => (-53479597 / 500000000000 : ℝ)
  | 4 => (-57138721 / 500000000000 : ℝ)
  | 5 => (-15219951 / 125000000000 : ℝ)
  | 6 => (-5176331 / 40000000000 : ℝ)
  | 7 => (-27445211 / 200000000000 : ℝ)
  | 8 => (-36303899 / 250000000000 : ℝ)
  | 9 => (-6135183 / 40000000000 : ℝ)
  | 10 => (-1263443 / 7812500000 : ℝ)
  | 11 => (-170241729 / 1000000000000 : ℝ)
  | 12 => (-44736357 / 250000000000 : ℝ)
  | 13 => (-37566923 / 200000000000 : ℝ)
  | 14 => (-196912137 / 1000000000000 : ℝ)
  | 15 => (-51545219 / 250000000000 : ℝ)
  | 16 => (-34503 / 160000000 : ℝ)
  | 17 => (-225303711 / 1000000000000 : ℝ)
  | 18 => (-58790937 / 250000000000 : ℝ)
  | 19 => (-122613443 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch051Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1020 : ℝ) + (j.val : ℝ)) / 1600)
      (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch051Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch051Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1020 : ℝ) + (j.val : ℝ)) / 1600)
    (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch051Neg100WeightLower j.val) (hpThetaShiftThreeBatch051Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch051Neg100WeightLower, hpThetaShiftThreeBatch051Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch051Neg100_integral_bounds :
    (-14829417 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-13799971 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1020 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch051Lower hpThetaJensenCellsBatch051Upper
    hpThetaShiftThreeBatch051Neg100WeightLower hpThetaShiftThreeBatch051Neg100WeightUpper hpThetaJensenCellsBatch051_bounds hpThetaShiftThreeBatch051Neg100_weight_bounds
  have hl : (-14829417 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch051Lower j * hpThetaShiftThreeBatch051Neg100WeightLower j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftThreeBatch051Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftThreeBatch051Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch051Lower j * hpThetaShiftThreeBatch051Neg100WeightUpper j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftThreeBatch051Neg100WeightUpper j) / 1600) ≤ (-13799971 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftThreeBatch051Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1020 : ℝ) / 1600 = 51 / 80 by norm_num,
    show ((1020 : ℝ) + 20) / 1600 = (51 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch051Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (53935463 / 250000000000 : ℝ)
  | 1 => (217796647 / 1000000000000 : ℝ)
  | 2 => (54963813 / 250000000000 : ℝ)
  | 3 => (22191741 / 100000000000 : ℝ)
  | 4 => (27997857 / 125000000000 : ℝ)
  | 5 => (226051323 / 1000000000000 : ℝ)
  | 6 => (45624507 / 200000000000 : ℝ)
  | 7 => (230196211 / 1000000000000 : ℝ)
  | 8 => (46454413 / 200000000000 : ℝ)
  | 9 => (58587451 / 250000000000 : ℝ)
  | 10 => (29553641 / 125000000000 : ℝ)
  | 11 => (238509733 / 1000000000000 : ℝ)
  | 12 => (240591307 / 1000000000000 : ℝ)
  | 13 => (60668383 / 250000000000 : ℝ)
  | 14 => (48951217 / 200000000000 : ℝ)
  | 15 => (123419317 / 500000000000 : ℝ)
  | 16 => (248920843 / 1000000000000 : ℝ)
  | 17 => (251002367 / 1000000000000 : ℝ)
  | 18 => (31635357 / 125000000000 : ℝ)
  | 19 => (255161951 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch051Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (27224581 / 125000000000 : ℝ)
  | 1 => (219855253 / 1000000000000 : ℝ)
  | 2 => (221917411 / 1000000000000 : ℝ)
  | 3 => (223982857 / 1000000000000 : ℝ)
  | 4 => (56512831 / 250000000000 : ℝ)
  | 5 => (28515317 / 125000000000 : ℝ)
  | 6 => (57549053 / 250000000000 : ℝ)
  | 7 => (116136033 / 500000000000 : ℝ)
  | 8 => (46869961 / 200000000000 : ℝ)
  | 9 => (236429129 / 1000000000000 : ℝ)
  | 10 => (119254867 / 500000000000 : ℝ)
  | 11 => (60147827 / 250000000000 : ℝ)
  | 12 => (242673533 / 1000000000000 : ℝ)
  | 13 => (122378043 / 500000000000 : ℝ)
  | 14 => (49367727 / 200000000000 : ℝ)
  | 15 => (62230211 / 250000000000 : ℝ)
  | 16 => (490239 / 1953125000 : ℝ)
  | 17 => (253082857 / 1000000000000 : ℝ)
  | 18 => (7973811 / 31250000000 : ℝ)
  | 19 => (25723929 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch051Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1020 : ℝ) + (j.val : ℝ)) / 1600)
      (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch051Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch051Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1020 : ℝ) + (j.val : ℝ)) / 1600)
    (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch051Neg70WeightLower j.val) (hpThetaShiftThreeBatch051Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch051Neg70WeightLower, hpThetaShiftThreeBatch051Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch051Neg70_integral_bounds :
    (41148899 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (42345623 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1020 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch051Lower hpThetaJensenCellsBatch051Upper
    hpThetaShiftThreeBatch051Neg70WeightLower hpThetaShiftThreeBatch051Neg70WeightUpper hpThetaJensenCellsBatch051_bounds hpThetaShiftThreeBatch051Neg70_weight_bounds
  have hl : (41148899 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch051Lower j * hpThetaShiftThreeBatch051Neg70WeightLower j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftThreeBatch051Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftThreeBatch051Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch051Lower j * hpThetaShiftThreeBatch051Neg70WeightUpper j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftThreeBatch051Neg70WeightUpper j) / 1600) ≤ (42345623 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftThreeBatch051Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1020 : ℝ) / 1600 = 51 / 80 by norm_num,
    show ((1020 : ℝ) + 20) / 1600 = (51 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch051Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-22677319 / 1000000000000 : ℝ)
  | 1 => (-10999403 / 500000000000 : ℝ)
  | 2 => (-10653839 / 500000000000 : ℝ)
  | 3 => (-20603819 / 1000000000000 : ℝ)
  | 4 => (-9943559 / 500000000000 : ℝ)
  | 5 => (-19157459 / 1000000000000 : ℝ)
  | 6 => (-18414729 / 1000000000000 : ℝ)
  | 7 => (-8829407 / 500000000000 : ℝ)
  | 8 => (-16889597 / 1000000000000 : ℝ)
  | 9 => (-4026741 / 250000000000 : ℝ)
  | 10 => (-15310799 / 1000000000000 : ℝ)
  | 11 => (-7250493 / 500000000000 : ℝ)
  | 12 => (-13677409 / 1000000000000 : ℝ)
  | 13 => (-256799 / 20000000000 : ℝ)
  | 14 => (-5994247 / 500000000000 : ℝ)
  | 15 => (-11122923 / 1000000000000 : ℝ)
  | 16 => (-5121559 / 500000000000 : ℝ)
  | 17 => (-9348963 / 1000000000000 : ℝ)
  | 18 => (-422017 / 50000000000 : ℝ)
  | 19 => (-7517129 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch051Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4399761 / 200000000000 : ℝ)
  | 1 => (-21307677 / 1000000000000 : ℝ)
  | 2 => (-10301909 / 500000000000 : ℝ)
  | 3 => (-19887117 / 1000000000000 : ℝ)
  | 4 => (-9578729 / 500000000000 : ℝ)
  | 5 => (-2301841 / 125000000000 : ℝ)
  | 6 => (-17658813 / 1000000000000 : ℝ)
  | 7 => (-4222399 / 250000000000 : ℝ)
  | 8 => (-16106963 / 1000000000000 : ℝ)
  | 9 => (-7655399 / 500000000000 : ℝ)
  | 10 => (-2900197 / 200000000000 : ℝ)
  | 11 => (-427419 / 31250000000 : ℝ)
  | 12 => (-12839949 / 1000000000000 : ℝ)
  | 13 => (-11988493 / 1000000000000 : ℝ)
  | 14 => (-5561461 / 500000000000 : ℝ)
  | 15 => (-10243117 / 1000000000000 : ℝ)
  | 16 => (-4674481 / 500000000000 : ℝ)
  | 17 => (-8440339 / 1000000000000 : ℝ)
  | 18 => (-939641 / 125000000000 : ℝ)
  | 19 => (-6579211 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch051Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1020 : ℝ) + (j.val : ℝ)) / 1600)
      (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch051Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch051Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1020 : ℝ) + (j.val : ℝ)) / 1600)
    (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch051Neg45WeightLower j.val) (hpThetaShiftThreeBatch051Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch051Neg45WeightLower, hpThetaShiftThreeBatch051Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch051Neg45_integral_bounds :
    (-88223 / 31250000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-525487 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1020 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch051Lower hpThetaJensenCellsBatch051Upper
    hpThetaShiftThreeBatch051Neg45WeightLower hpThetaShiftThreeBatch051Neg45WeightUpper hpThetaJensenCellsBatch051_bounds hpThetaShiftThreeBatch051Neg45_weight_bounds
  have hl : (-88223 / 31250000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch051Lower j * hpThetaShiftThreeBatch051Neg45WeightLower j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftThreeBatch051Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftThreeBatch051Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch051Lower j * hpThetaShiftThreeBatch051Neg45WeightUpper j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftThreeBatch051Neg45WeightUpper j) / 1600) ≤ (-525487 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftThreeBatch051Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1020 : ℝ) / 1600 = 51 / 80 by norm_num,
    show ((1020 : ℝ) + 20) / 1600 = (51 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch051Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-38825259 / 500000000000 : ℝ)
  | 1 => (-78422489 / 1000000000000 : ℝ)
  | 2 => (-9899727 / 125000000000 : ℝ)
  | 3 => (-9997061 / 125000000000 : ℝ)
  | 4 => (-80758489 / 1000000000000 : ℝ)
  | 5 => (-81543807 / 1000000000000 : ℝ)
  | 6 => (-82332427 / 1000000000000 : ℝ)
  | 7 => (-41562167 / 500000000000 : ℝ)
  | 8 => (-41959757 / 500000000000 : ℝ)
  | 9 => (-1694359 / 20000000000 : ℝ)
  | 10 => (-21379907 / 250000000000 : ℝ)
  | 11 => (-8632453 / 100000000000 : ℝ)
  | 12 => (-87132641 / 1000000000000 : ℝ)
  | 13 => (-10992993 / 125000000000 : ℝ)
  | 14 => (-44379211 / 500000000000 : ℝ)
  | 15 => (-89576057 / 1000000000000 : ℝ)
  | 16 => (-90396831 / 1000000000000 : ℝ)
  | 17 => (-3648829 / 40000000000 : ℝ)
  | 18 => (-46023861 / 500000000000 : ℝ)
  | 19 => (-92877801 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch051Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-76881917 / 1000000000000 : ℝ)
  | 1 => (-77650517 / 1000000000000 : ℝ)
  | 2 => (-9802811 / 125000000000 : ℝ)
  | 3 => (-15839563 / 200000000000 : ℝ)
  | 4 => (-79976487 / 1000000000000 : ℝ)
  | 5 => (-10094811 / 125000000000 : ℝ)
  | 6 => (-40771903 / 500000000000 : ℝ)
  | 7 => (-41166213 / 500000000000 : ℝ)
  | 8 => (-83124333 / 1000000000000 : ℝ)
  | 9 => (-83919513 / 1000000000000 : ℝ)
  | 10 => (-84717949 / 1000000000000 : ℝ)
  | 11 => (-85519627 / 1000000000000 : ℝ)
  | 12 => (-86324529 / 1000000000000 : ℝ)
  | 13 => (-544579 / 6250000000 : ℝ)
  | 14 => (-87943943 / 1000000000000 : ℝ)
  | 15 => (-88758421 / 1000000000000 : ℝ)
  | 16 => (-11197007 / 125000000000 : ℝ)
  | 17 => (-9039683 / 100000000000 : ℝ)
  | 18 => (-22805181 / 250000000000 : ℝ)
  | 19 => (-92047721 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch051Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1020 : ℝ) + (j.val : ℝ)) / 1600)
      (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch051Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch051Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1020 : ℝ) + (j.val : ℝ)) / 1600)
    (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch051Neg25WeightLower j.val) (hpThetaShiftThreeBatch051Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch051Neg25WeightLower, hpThetaShiftThreeBatch051Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch051Neg25_integral_bounds :
    (-15183011 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-3686077 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1020 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch051Lower hpThetaJensenCellsBatch051Upper
    hpThetaShiftThreeBatch051Neg25WeightLower hpThetaShiftThreeBatch051Neg25WeightUpper hpThetaJensenCellsBatch051_bounds hpThetaShiftThreeBatch051Neg25_weight_bounds
  have hl : (-15183011 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch051Lower j * hpThetaShiftThreeBatch051Neg25WeightLower j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftThreeBatch051Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftThreeBatch051Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch051Lower j * hpThetaShiftThreeBatch051Neg25WeightUpper j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftThreeBatch051Neg25WeightUpper j) / 1600) ≤ (-3686077 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftThreeBatch051Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1020 : ℝ) / 1600 = 51 / 80 by norm_num,
    show ((1020 : ℝ) + 20) / 1600 = (51 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch051Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch051Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch051Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch051Neg25_integral_bounds
end HodgeProofHP
