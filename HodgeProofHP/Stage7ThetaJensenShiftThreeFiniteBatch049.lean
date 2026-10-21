/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch049

/-! Exact signed weight and batch integral certificates, batch 49 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch049Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (8221669 / 100000000000 : ℝ)
  | 1 => (79831831 / 1000000000000 : ℝ)
  | 2 => (38683219 / 500000000000 : ℝ)
  | 3 => (37409509 / 500000000000 : ℝ)
  | 4 => (36094027 / 500000000000 : ℝ)
  | 5 => (6947201 / 100000000000 : ℝ)
  | 6 => (66669329 / 1000000000000 : ℝ)
  | 7 => (63778433 / 1000000000000 : ℝ)
  | 8 => (60797721 / 1000000000000 : ℝ)
  | 9 => (57725571 / 1000000000000 : ℝ)
  | 10 => (2728017 / 50000000000 : ℝ)
  | 11 => (1282509 / 25000000000 : ℝ)
  | 12 => (9588789 / 200000000000 : ℝ)
  | 13 => (44489381 / 1000000000000 : ℝ)
  | 14 => (20467467 / 500000000000 : ℝ)
  | 15 => (291241 / 7812500000 : ℝ)
  | 16 => (1675967 / 50000000000 : ℝ)
  | 17 => (5930921 / 200000000000 : ℝ)
  | 18 => (200647 / 7812500000 : ℝ)
  | 19 => (21602117 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch049Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (21130623 / 250000000000 : ℝ)
  | 1 => (82216691 / 1000000000000 : ℝ)
  | 2 => (9978979 / 125000000000 : ℝ)
  | 3 => (77366439 / 1000000000000 : ℝ)
  | 4 => (74819019 / 1000000000000 : ℝ)
  | 5 => (14437611 / 200000000000 : ℝ)
  | 6 => (69472011 / 1000000000000 : ℝ)
  | 7 => (6666933 / 100000000000 : ℝ)
  | 8 => (31889217 / 500000000000 : ℝ)
  | 9 => (30398861 / 500000000000 : ℝ)
  | 10 => (14431393 / 250000000000 : ℝ)
  | 11 => (54560341 / 1000000000000 : ℝ)
  | 12 => (51300361 / 1000000000000 : ℝ)
  | 13 => (23971973 / 500000000000 : ℝ)
  | 14 => (22244691 / 500000000000 : ℝ)
  | 15 => (8186987 / 200000000000 : ℝ)
  | 16 => (37278849 / 1000000000000 : ℝ)
  | 17 => (33519341 / 1000000000000 : ℝ)
  | 18 => (14827303 / 500000000000 : ℝ)
  | 19 => (25682817 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch049Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((980 : ℝ) + (j.val : ℝ)) / 1600)
      (((980 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch049Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch049Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((980 : ℝ) + (j.val : ℝ)) / 1600)
    (((980 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch049Neg100WeightLower j.val) (hpThetaShiftThreeBatch049Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch049Neg100WeightLower, hpThetaShiftThreeBatch049Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch049Neg100_integral_bounds :
    (377309 / 25000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (253813 / 15625000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (980 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch049Lower hpThetaJensenCellsBatch049Upper
    hpThetaShiftThreeBatch049Neg100WeightLower hpThetaShiftThreeBatch049Neg100WeightUpper hpThetaJensenCellsBatch049_bounds hpThetaShiftThreeBatch049Neg100_weight_bounds
  have hl : (377309 / 25000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch049Lower j * hpThetaShiftThreeBatch049Neg100WeightLower j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftThreeBatch049Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftThreeBatch049Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch049Lower j * hpThetaShiftThreeBatch049Neg100WeightUpper j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftThreeBatch049Neg100WeightUpper j) / 1600) ≤ (253813 / 15625000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftThreeBatch049Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (980 : ℝ) / 1600 = 49 / 80 by norm_num,
    show ((980 : ℝ) + 20) / 1600 = (49 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch049Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4344093 / 31250000000 : ℝ)
  | 1 => (35189617 / 250000000000 : ℝ)
  | 2 => (71258107 / 500000000000 : ℝ)
  | 3 => (144284131 / 1000000000000 : ℝ)
  | 4 => (14606213 / 100000000000 : ℝ)
  | 5 => (147850119 / 1000000000000 : ℝ)
  | 6 => (149648003 / 1000000000000 : ℝ)
  | 7 => (30291137 / 200000000000 : ℝ)
  | 8 => (153273063 / 1000000000000 : ℝ)
  | 9 => (1211719 / 7812500000 : ℝ)
  | 10 => (156936483 / 1000000000000 : ℝ)
  | 11 => (31756461 / 200000000000 : ℝ)
  | 12 => (80318691 / 500000000000 : ℝ)
  | 13 => (81250797 / 500000000000 : ℝ)
  | 14 => (82187409 / 500000000000 : ℝ)
  | 15 => (5195529 / 31250000000 : ℝ)
  | 16 => (10509237 / 62500000000 : ℝ)
  | 17 => (42511819 / 250000000000 : ℝ)
  | 18 => (85977621 / 500000000000 : ℝ)
  | 19 => (86935773 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch049Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (140758469 / 1000000000000 : ℝ)
  | 1 => (28503243 / 200000000000 : ℝ)
  | 2 => (36071033 / 250000000000 : ℝ)
  | 3 => (146062131 / 1000000000000 : ℝ)
  | 4 => (3696253 / 25000000000 : ℝ)
  | 5 => (37412001 / 250000000000 : ℝ)
  | 6 => (75727843 / 500000000000 : ℝ)
  | 7 => (19159133 / 125000000000 : ℝ)
  | 8 => (155100033 / 1000000000000 : ℝ)
  | 9 => (39234121 / 250000000000 : ℝ)
  | 10 => (79391153 / 500000000000 : ℝ)
  | 11 => (160637383 / 1000000000000 : ℝ)
  | 12 => (32500319 / 200000000000 : ℝ)
  | 13 => (164374819 / 1000000000000 : ℝ)
  | 14 => (166256929 / 1000000000000 : ℝ)
  | 15 => (168147793 / 1000000000000 : ℝ)
  | 16 => (170047277 / 1000000000000 : ℝ)
  | 17 => (171955243 / 1000000000000 : ℝ)
  | 18 => (173871547 / 1000000000000 : ℝ)
  | 19 => (43949011 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch049Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((980 : ℝ) + (j.val : ℝ)) / 1600)
      (((980 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch049Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch049Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((980 : ℝ) + (j.val : ℝ)) / 1600)
    (((980 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch049Neg70WeightLower j.val) (hpThetaShiftThreeBatch049Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch049Neg70WeightLower, hpThetaShiftThreeBatch049Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch049Neg70_integral_bounds :
    (42140487 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (8692769 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (980 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch049Lower hpThetaJensenCellsBatch049Upper
    hpThetaShiftThreeBatch049Neg70WeightLower hpThetaShiftThreeBatch049Neg70WeightUpper hpThetaJensenCellsBatch049_bounds hpThetaShiftThreeBatch049Neg70_weight_bounds
  have hl : (42140487 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch049Lower j * hpThetaShiftThreeBatch049Neg70WeightLower j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftThreeBatch049Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftThreeBatch049Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch049Lower j * hpThetaShiftThreeBatch049Neg70WeightUpper j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftThreeBatch049Neg70WeightUpper j) / 1600) ≤ (8692769 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftThreeBatch049Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (980 : ℝ) / 1600 = 49 / 80 by norm_num,
    show ((980 : ℝ) + 20) / 1600 = (49 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch049Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8144267 / 200000000000 : ℝ)
  | 1 => (-10114863 / 250000000000 : ℝ)
  | 2 => (-40189127 / 1000000000000 : ℝ)
  | 3 => (-19955133 / 500000000000 : ℝ)
  | 4 => (-19811387 / 500000000000 : ℝ)
  | 5 => (-39326553 / 1000000000000 : ℝ)
  | 6 => (-39021507 / 1000000000000 : ℝ)
  | 7 => (-1935377 / 50000000000 : ℝ)
  | 8 => (-19192277 / 500000000000 : ℝ)
  | 9 => (-38052449 / 1000000000000 : ℝ)
  | 10 => (-37711129 / 1000000000000 : ℝ)
  | 11 => (-18680247 / 500000000000 : ℝ)
  | 12 => (-37000443 / 1000000000000 : ℝ)
  | 13 => (-18315439 / 500000000000 : ℝ)
  | 14 => (-36251697 / 1000000000000 : ℝ)
  | 15 => (-89657 / 2500000000 : ℝ)
  | 16 => (-8866021 / 250000000000 : ℝ)
  | 17 => (-35055449 / 1000000000000 : ℝ)
  | 18 => (-3463679 / 100000000000 : ℝ)
  | 19 => (-17104003 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch049Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-40459451 / 1000000000000 : ℝ)
  | 1 => (-20094563 / 500000000000 : ℝ)
  | 2 => (-7982053 / 200000000000 : ℝ)
  | 3 => (-39622773 / 1000000000000 : ℝ)
  | 4 => (-4915819 / 125000000000 : ℝ)
  | 5 => (-19510753 / 500000000000 : ℝ)
  | 6 => (-38707539 / 1000000000000 : ℝ)
  | 7 => (-38384553 / 1000000000000 : ℝ)
  | 8 => (-1189139 / 31250000000 : ℝ)
  | 9 => (-4713891 / 125000000000 : ℝ)
  | 10 => (-37360493 / 1000000000000 : ℝ)
  | 11 => (-18500221 / 500000000000 : ℝ)
  | 12 => (-36630877 / 1000000000000 : ℝ)
  | 13 => (-2265731 / 62500000000 : ℝ)
  | 14 => (-35862799 / 1000000000000 : ℝ)
  | 15 => (-35464083 / 1000000000000 : ℝ)
  | 16 => (-4381931 / 125000000000 : ℝ)
  | 17 => (-34636789 / 1000000000000 : ℝ)
  | 18 => (-6841601 / 200000000000 : ℝ)
  | 19 => (-1055281 / 31250000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch049Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((980 : ℝ) + (j.val : ℝ)) / 1600)
      (((980 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch049Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch049Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((980 : ℝ) + (j.val : ℝ)) / 1600)
    (((980 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch049Neg45WeightLower j.val) (hpThetaShiftThreeBatch049Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch049Neg45WeightLower, hpThetaShiftThreeBatch049Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch049Neg45_integral_bounds :
    (-10453351 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-10161529 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (980 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch049Lower hpThetaJensenCellsBatch049Upper
    hpThetaShiftThreeBatch049Neg45WeightLower hpThetaShiftThreeBatch049Neg45WeightUpper hpThetaJensenCellsBatch049_bounds hpThetaShiftThreeBatch049Neg45_weight_bounds
  have hl : (-10453351 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch049Lower j * hpThetaShiftThreeBatch049Neg45WeightLower j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftThreeBatch049Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftThreeBatch049Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch049Lower j * hpThetaShiftThreeBatch049Neg45WeightUpper j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftThreeBatch049Neg45WeightUpper j) / 1600) ≤ (-10161529 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftThreeBatch049Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (980 : ℝ) / 1600 = 49 / 80 by norm_num,
    show ((980 : ℝ) + 20) / 1600 = (49 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch049Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-49637351 / 1000000000000 : ℝ)
  | 1 => (-25133887 / 500000000000 : ℝ)
  | 2 => (-6362729 / 125000000000 : ℝ)
  | 3 => (-25769763 / 500000000000 : ℝ)
  | 4 => (-13045213 / 250000000000 : ℝ)
  | 5 => (-3301613 / 62500000000 : ℝ)
  | 6 => (-53474393 / 1000000000000 : ℝ)
  | 7 => (-13531651 / 250000000000 : ℝ)
  | 8 => (-54782437 / 1000000000000 : ℝ)
  | 9 => (-5544189 / 100000000000 : ℝ)
  | 10 => (-5479 / 97656250 : ℝ)
  | 11 => (-56771641 / 1000000000000 : ℝ)
  | 12 => (-14360483 / 250000000000 : ℝ)
  | 13 => (-58115827 / 1000000000000 : ℝ)
  | 14 => (-58793321 / 1000000000000 : ℝ)
  | 15 => (-59474411 / 1000000000000 : ℝ)
  | 16 => (-15039773 / 250000000000 : ℝ)
  | 17 => (-60847357 / 1000000000000 : ℝ)
  | 18 => (-30769601 / 500000000000 : ℝ)
  | 19 => (-3111731 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch049Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-24505283 / 500000000000 : ℝ)
  | 1 => (-992747 / 20000000000 : ℝ)
  | 2 => (-50267773 / 1000000000000 : ℝ)
  | 3 => (-50901831 / 1000000000000 : ℝ)
  | 4 => (-2061581 / 40000000000 : ℝ)
  | 5 => (-52180851 / 1000000000000 : ℝ)
  | 6 => (-52825807 / 1000000000000 : ℝ)
  | 7 => (-6684299 / 125000000000 : ℝ)
  | 8 => (-54126603 / 1000000000000 : ℝ)
  | 9 => (-13695609 / 250000000000 : ℝ)
  | 10 => (-55441889 / 1000000000000 : ℝ)
  | 11 => (-56104959 / 1000000000000 : ℝ)
  | 12 => (-1419291 / 25000000000 : ℝ)
  | 13 => (-57441931 / 1000000000000 : ℝ)
  | 14 => (-29057913 / 500000000000 : ℝ)
  | 15 => (-1469833 / 25000000000 : ℝ)
  | 16 => (-5947441 / 100000000000 : ℝ)
  | 17 => (-60159091 / 1000000000000 : ℝ)
  | 18 => (-15211839 / 250000000000 : ℝ)
  | 19 => (-61539201 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch049Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((980 : ℝ) + (j.val : ℝ)) / 1600)
      (((980 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch049Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch049Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((980 : ℝ) + (j.val : ℝ)) / 1600)
    (((980 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch049Neg25WeightLower j.val) (hpThetaShiftThreeBatch049Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch049Neg25WeightLower, hpThetaShiftThreeBatch049Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch049Neg25_integral_bounds :
    (-15356657 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-7443019 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (980 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch049Lower hpThetaJensenCellsBatch049Upper
    hpThetaShiftThreeBatch049Neg25WeightLower hpThetaShiftThreeBatch049Neg25WeightUpper hpThetaJensenCellsBatch049_bounds hpThetaShiftThreeBatch049Neg25_weight_bounds
  have hl : (-15356657 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch049Lower j * hpThetaShiftThreeBatch049Neg25WeightLower j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftThreeBatch049Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftThreeBatch049Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch049Lower j * hpThetaShiftThreeBatch049Neg25WeightUpper j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftThreeBatch049Neg25WeightUpper j) / 1600) ≤ (-7443019 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftThreeBatch049Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (980 : ℝ) / 1600 = 49 / 80 by norm_num,
    show ((980 : ℝ) + 20) / 1600 = (49 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch049Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch049Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch049Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch049Neg25_integral_bounds
end HodgeProofHP
