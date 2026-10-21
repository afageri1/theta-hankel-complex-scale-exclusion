/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch052

/-! Exact signed weight and batch integral certificates, batch 52 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch052Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-66493687 / 250000000000 : ℝ)
  | 1 => (-34583213 / 125000000000 : ℝ)
  | 2 => (-28757223 / 100000000000 : ℝ)
  | 3 => (-59739507 / 200000000000 : ℝ)
  | 4 => (-31004487 / 100000000000 : ℝ)
  | 5 => (-321617523 / 1000000000000 : ℝ)
  | 6 => (-333418821 / 1000000000000 : ℝ)
  | 7 => (-86363033 / 250000000000 : ℝ)
  | 8 => (-357720861 / 1000000000000 : ℝ)
  | 9 => (-46278557 / 125000000000 : ℝ)
  | 10 => (-191489203 / 500000000000 : ℝ)
  | 11 => (-197987119 / 500000000000 : ℝ)
  | 12 => (-409219523 / 1000000000000 : ℝ)
  | 13 => (-422717873 / 1000000000000 : ℝ)
  | 14 => (-436472943 / 1000000000000 : ℝ)
  | 15 => (-450488431 / 1000000000000 : ℝ)
  | 16 => (-116192019 / 250000000000 : ℝ)
  | 17 => (-239657831 / 500000000000 : ℝ)
  | 18 => (-494135017 / 1000000000000 : ℝ)
  | 19 => (-254615007 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch052Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-127748093 / 500000000000 : ℝ)
  | 1 => (-265974747 / 1000000000000 : ℝ)
  | 2 => (-276665703 / 1000000000000 : ℝ)
  | 3 => (-287572229 / 1000000000000 : ℝ)
  | 4 => (-149348767 / 500000000000 : ℝ)
  | 5 => (-310044869 / 1000000000000 : ℝ)
  | 6 => (-160808761 / 500000000000 : ℝ)
  | 7 => (-16670941 / 50000000000 : ℝ)
  | 8 => (-345452131 / 1000000000000 : ℝ)
  | 9 => (-17886043 / 50000000000 : ℝ)
  | 10 => (-74045691 / 200000000000 : ℝ)
  | 11 => (-76595681 / 200000000000 : ℝ)
  | 12 => (-395974237 / 1000000000000 : ℝ)
  | 13 => (-204609761 / 500000000000 : ℝ)
  | 14 => (-26419867 / 62500000000 : ℝ)
  | 15 => (-218236471 / 500000000000 : ℝ)
  | 16 => (-45048843 / 100000000000 : ℝ)
  | 17 => (-18590723 / 40000000000 : ℝ)
  | 18 => (-479315661 / 1000000000000 : ℝ)
  | 19 => (-61766877 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch052Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1040 : ℝ) + (j.val : ℝ)) / 1600)
      (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch052Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch052Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1040 : ℝ) + (j.val : ℝ)) / 1600)
    (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch052Neg100WeightLower j.val) (hpThetaShiftThreeBatch052Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch052Neg100WeightLower, hpThetaShiftThreeBatch052Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch052Neg100_integral_bounds :
    (-53515371 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-2534277 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1040 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch052Lower hpThetaJensenCellsBatch052Upper
    hpThetaShiftThreeBatch052Neg100WeightLower hpThetaShiftThreeBatch052Neg100WeightUpper hpThetaJensenCellsBatch052_bounds hpThetaShiftThreeBatch052Neg100_weight_bounds
  have hl : (-53515371 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch052Lower j * hpThetaShiftThreeBatch052Neg100WeightLower j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftThreeBatch052Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftThreeBatch052Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch052Lower j * hpThetaShiftThreeBatch052Neg100WeightUpper j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftThreeBatch052Neg100WeightUpper j) / 1600) ≤ (-2534277 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftThreeBatch052Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1040 : ℝ) / 1600 = 52 / 80 by norm_num,
    show ((1040 : ℝ) + 20) / 1600 = (52 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch052Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (257239289 / 1000000000000 : ℝ)
  | 1 => (129657249 / 500000000000 : ℝ)
  | 2 => (261387199 / 1000000000000 : ℝ)
  | 3 => (131728503 / 500000000000 : ℝ)
  | 4 => (265523527 / 1000000000000 : ℝ)
  | 5 => (6689659 / 25000000000 : ℝ)
  | 6 => (269645097 / 1000000000000 : ℝ)
  | 7 => (67924831 / 250000000000 : ℝ)
  | 8 => (34218577 / 125000000000 : ℝ)
  | 9 => (275792543 / 1000000000000 : ℝ)
  | 10 => (138915333 / 500000000000 : ℝ)
  | 11 => (139931269 / 500000000000 : ℝ)
  | 12 => (56377541 / 200000000000 : ℝ)
  | 13 => (141952851 / 500000000000 : ℝ)
  | 14 => (14295803 / 50000000000 : ℝ)
  | 15 => (287918299 / 1000000000000 : ℝ)
  | 16 => (289911931 / 1000000000000 : ℝ)
  | 17 => (291896459 / 1000000000000 : ℝ)
  | 18 => (146935689 / 500000000000 : ℝ)
  | 19 => (147918087 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch052Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (259314499 / 1000000000000 : ℝ)
  | 1 => (163367 / 625000000 : ℝ)
  | 2 => (263457007 / 1000000000000 : ℝ)
  | 3 => (33190441 / 125000000000 : ℝ)
  | 4 => (267586361 / 1000000000000 : ℝ)
  | 5 => (134822549 / 500000000000 : ℝ)
  | 6 => (10867973 / 40000000000 : ℝ)
  | 7 => (273748617 / 1000000000000 : ℝ)
  | 8 => (8618517 / 31250000000 : ℝ)
  | 9 => (277830667 / 1000000000000 : ℝ)
  | 10 => (279862539 / 1000000000000 : ℝ)
  | 11 => (140943853 / 500000000000 : ℝ)
  | 12 => (283905703 / 1000000000000 : ℝ)
  | 13 => (285916061 / 1000000000000 : ℝ)
  | 14 => (2879183 / 10000000000 : ℝ)
  | 15 => (72477983 / 250000000000 : ℝ)
  | 16 => (14594823 / 50000000000 : ℝ)
  | 17 => (293871379 / 1000000000000 : ℝ)
  | 18 => (11833447 / 40000000000 : ℝ)
  | 19 => (297790327 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch052Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1040 : ℝ) + (j.val : ℝ)) / 1600)
      (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch052Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch052Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1040 : ℝ) + (j.val : ℝ)) / 1600)
    (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch052Neg70WeightLower j.val) (hpThetaShiftThreeBatch052Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch052Neg70WeightLower, hpThetaShiftThreeBatch052Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch052Neg70_integral_bounds :
    (38514839 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (19795331 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1040 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch052Lower hpThetaJensenCellsBatch052Upper
    hpThetaShiftThreeBatch052Neg70WeightLower hpThetaShiftThreeBatch052Neg70WeightUpper hpThetaJensenCellsBatch052_bounds hpThetaShiftThreeBatch052Neg70_weight_bounds
  have hl : (38514839 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch052Lower j * hpThetaShiftThreeBatch052Neg70WeightLower j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftThreeBatch052Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftThreeBatch052Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch052Lower j * hpThetaShiftThreeBatch052Neg70WeightUpper j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftThreeBatch052Neg70WeightUpper j) / 1600) ≤ (19795331 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftThreeBatch052Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1040 : ℝ) / 1600 = 52 / 80 by norm_num,
    show ((1040 : ℝ) + 20) / 1600 = (52 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch052Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1644803 / 250000000000 : ℝ)
  | 1 => (-5626471 / 1000000000000 : ℝ)
  | 2 => (-931757 / 200000000000 : ℝ)
  | 3 => (-919009 / 250000000000 : ℝ)
  | 4 => (-2678103 / 1000000000000 : ℝ)
  | 5 => (-416217 / 250000000000 : ℝ)
  | 6 => (-636209 / 1000000000000 : ℝ)
  | 7 => (407993 / 1000000000000 : ℝ)
  | 8 => (73393 / 50000000000 : ℝ)
  | 9 => (317939 / 125000000000 : ℝ)
  | 10 => (363507 / 100000000000 : ℝ)
  | 11 => (948531 / 200000000000 : ℝ)
  | 12 => (5866389 / 1000000000000 : ℝ)
  | 13 => (7006393 / 1000000000000 : ℝ)
  | 14 => (2040697 / 250000000000 : ℝ)
  | 15 => (4667849 / 500000000000 : ℝ)
  | 16 => (5262621 / 500000000000 : ℝ)
  | 17 => (1466443 / 125000000000 : ℝ)
  | 18 => (6477363 / 500000000000 : ℝ)
  | 19 => (14194911 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch052Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-562647 / 100000000000 : ℝ)
  | 1 => (-145587 / 31250000000 : ℝ)
  | 2 => (-735207 / 200000000000 : ℝ)
  | 3 => (-1339051 / 500000000000 : ℝ)
  | 4 => (-1664867 / 1000000000000 : ℝ)
  | 5 => (-39763 / 62500000000 : ℝ)
  | 6 => (203997 / 500000000000 : ℝ)
  | 7 => (1467861 / 1000000000000 : ℝ)
  | 8 => (2543513 / 1000000000000 : ℝ)
  | 9 => (3635071 / 1000000000000 : ℝ)
  | 10 => (9263 / 1953125000 : ℝ)
  | 11 => (586639 / 100000000000 : ℝ)
  | 12 => (3503197 / 500000000000 : ℝ)
  | 13 => (8162789 / 1000000000000 : ℝ)
  | 14 => (9335699 / 1000000000000 : ℝ)
  | 15 => (10525243 / 1000000000000 : ℝ)
  | 16 => (2346309 / 200000000000 : ℝ)
  | 17 => (12954727 / 1000000000000 : ℝ)
  | 18 => (443591 / 31250000000 : ℝ)
  | 19 => (772611 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch052Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1040 : ℝ) + (j.val : ℝ)) / 1600)
      (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch052Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch052Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1040 : ℝ) + (j.val : ℝ)) / 1600)
    (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch052Neg45WeightLower j.val) (hpThetaShiftThreeBatch052Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch052Neg45WeightLower, hpThetaShiftThreeBatch052Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch052Neg45_integral_bounds :
    (405329 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (18021 / 31250000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1040 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch052Lower hpThetaJensenCellsBatch052Upper
    hpThetaShiftThreeBatch052Neg45WeightLower hpThetaShiftThreeBatch052Neg45WeightUpper hpThetaJensenCellsBatch052_bounds hpThetaShiftThreeBatch052Neg45_weight_bounds
  have hl : (405329 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch052Lower j * hpThetaShiftThreeBatch052Neg45WeightLower j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftThreeBatch052Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftThreeBatch052Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch052Lower j * hpThetaShiftThreeBatch052Neg45WeightUpper j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftThreeBatch052Neg45WeightUpper j) / 1600) ≤ (18021 / 31250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftThreeBatch052Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1040 : ℝ) / 1600 = 52 / 80 by norm_num,
    show ((1040 : ℝ) + 20) / 1600 = (52 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch052Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2928467 / 31250000000 : ℝ)
  | 1 => (-94547131 / 1000000000000 : ℝ)
  | 2 => (-95386341 / 1000000000000 : ℝ)
  | 3 => (-48114277 / 500000000000 : ℝ)
  | 4 => (-97073749 / 1000000000000 : ℝ)
  | 5 => (-97921903 / 1000000000000 : ℝ)
  | 6 => (-24693249 / 250000000000 : ℝ)
  | 7 => (-49813503 / 500000000000 : ℝ)
  | 8 => (-25120977 / 250000000000 : ℝ)
  | 9 => (-101343681 / 1000000000000 : ℝ)
  | 10 => (-102206301 / 1000000000000 : ℝ)
  | 11 => (-103071743 / 1000000000000 : ℝ)
  | 12 => (-6496249 / 62500000000 : ℝ)
  | 13 => (-104810999 / 1000000000000 : ℝ)
  | 14 => (-105684763 / 1000000000000 : ℝ)
  | 15 => (-106561249 / 1000000000000 : ℝ)
  | 16 => (-6715027 / 62500000000 : ℝ)
  | 17 => (-54161143 / 500000000000 : ℝ)
  | 18 => (-109206783 / 1000000000000 : ℝ)
  | 19 => (-13761737 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch052Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-464389 / 5000000000 : ℝ)
  | 1 => (-93710943 / 1000000000000 : ℝ)
  | 2 => (-9454713 / 100000000000 : ℝ)
  | 3 => (-4769317 / 50000000000 : ℝ)
  | 4 => (-96228553 / 1000000000000 : ℝ)
  | 5 => (-24268437 / 250000000000 : ℝ)
  | 6 => (-48960951 / 500000000000 : ℝ)
  | 7 => (-19754599 / 200000000000 : ℝ)
  | 8 => (-19925401 / 200000000000 : ℝ)
  | 9 => (-100483907 / 1000000000000 : ℝ)
  | 10 => (-316699 / 3125000000 : ℝ)
  | 11 => (-1022063 / 10000000000 : ℝ)
  | 12 => (-51535871 / 500000000000 : ℝ)
  | 13 => (-103939983 / 1000000000000 : ℝ)
  | 14 => (-52405499 / 500000000000 : ℝ)
  | 15 => (-52842381 / 500000000000 : ℝ)
  | 16 => (-3330039 / 31250000000 : ℝ)
  | 17 => (-107440431 / 1000000000000 : ℝ)
  | 18 => (-21664457 / 200000000000 : ℝ)
  | 19 => (-54603391 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch052Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1040 : ℝ) + (j.val : ℝ)) / 1600)
      (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch052Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch052Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1040 : ℝ) + (j.val : ℝ)) / 1600)
    (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch052Neg25WeightLower j.val) (hpThetaShiftThreeBatch052Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch052Neg25WeightLower, hpThetaShiftThreeBatch052Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch052Neg25_integral_bounds :
    (-14455579 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-2809243 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1040 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch052Lower hpThetaJensenCellsBatch052Upper
    hpThetaShiftThreeBatch052Neg25WeightLower hpThetaShiftThreeBatch052Neg25WeightUpper hpThetaJensenCellsBatch052_bounds hpThetaShiftThreeBatch052Neg25_weight_bounds
  have hl : (-14455579 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch052Lower j * hpThetaShiftThreeBatch052Neg25WeightLower j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftThreeBatch052Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftThreeBatch052Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch052Lower j * hpThetaShiftThreeBatch052Neg25WeightUpper j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftThreeBatch052Neg25WeightUpper j) / 1600) ≤ (-2809243 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftThreeBatch052Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1040 : ℝ) / 1600 = 52 / 80 by norm_num,
    show ((1040 : ℝ) + 20) / 1600 = (52 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch052Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch052Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch052Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch052Neg25_integral_bounds
end HodgeProofHP
