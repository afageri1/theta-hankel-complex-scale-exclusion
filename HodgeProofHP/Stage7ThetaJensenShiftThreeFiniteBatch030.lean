/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch030

/-! Exact signed weight and batch integral certificates, batch 30 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch030Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3748481 / 1000000000000 : ℝ)
  | 1 => (-942591 / 250000000000 : ℝ)
  | 2 => (-3791771 / 1000000000000 : ℝ)
  | 3 => (-1906343 / 500000000000 : ℝ)
  | 4 => (-1916547 / 500000000000 : ℝ)
  | 5 => (-1926489 / 500000000000 : ℝ)
  | 6 => (-968081 / 250000000000 : ℝ)
  | 7 => (-3891113 / 1000000000000 : ℝ)
  | 8 => (-3909329 / 1000000000000 : ℝ)
  | 9 => (-785391 / 200000000000 : ℝ)
  | 10 => (-157759 / 40000000000 : ℝ)
  | 11 => (-396037 / 100000000000 : ℝ)
  | 12 => (-994031 / 250000000000 : ℝ)
  | 13 => (-3991217 / 1000000000000 : ℝ)
  | 14 => (-4005633 / 1000000000000 : ℝ)
  | 15 => (-4019353 / 1000000000000 : ℝ)
  | 16 => (-2016179 / 500000000000 : ℝ)
  | 17 => (-404463 / 100000000000 : ℝ)
  | 18 => (-81123 / 20000000000 : ℝ)
  | 19 => (-2033449 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch030Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3726137 / 1000000000000 : ℝ)
  | 1 => (-5857 / 1562500000 : ℝ)
  | 2 => (-3770363 / 1000000000000 : ℝ)
  | 3 => (-379177 / 100000000000 : ℝ)
  | 4 => (-762537 / 200000000000 : ℝ)
  | 5 => (-3833093 / 1000000000000 : ℝ)
  | 6 => (-3852977 / 1000000000000 : ℝ)
  | 7 => (-3872323 / 1000000000000 : ℝ)
  | 8 => (-486389 / 125000000000 : ℝ)
  | 9 => (-244333 / 62500000000 : ℝ)
  | 10 => (-1963477 / 500000000000 : ℝ)
  | 11 => (-1971987 / 500000000000 : ℝ)
  | 12 => (-3960369 / 1000000000000 : ℝ)
  | 13 => (-3976123 / 1000000000000 : ℝ)
  | 14 => (-249451 / 62500000000 : ℝ)
  | 15 => (-15647 / 3906250000 : ℝ)
  | 16 => (-502419 / 125000000000 : ℝ)
  | 17 => (-4032357 / 1000000000000 : ℝ)
  | 18 => (-4044629 / 1000000000000 : ℝ)
  | 19 => (-4056149 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch030Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((600 : ℝ) + (j.val : ℝ)) / 1600)
      (((600 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch030Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch030Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((600 : ℝ) + (j.val : ℝ)) / 1600)
    (((600 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch030Neg100WeightLower j.val) (hpThetaShiftThreeBatch030Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch030Neg100WeightLower, hpThetaShiftThreeBatch030Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch030Neg100_integral_bounds :
    (-20070671 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-492519 / 25000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (600 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch030Lower hpThetaJensenCellsBatch030Upper
    hpThetaShiftThreeBatch030Neg100WeightLower hpThetaShiftThreeBatch030Neg100WeightUpper hpThetaJensenCellsBatch030_bounds hpThetaShiftThreeBatch030Neg100_weight_bounds
  have hl : (-20070671 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch030Lower j * hpThetaShiftThreeBatch030Neg100WeightLower j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftThreeBatch030Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftThreeBatch030Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch030Lower j * hpThetaShiftThreeBatch030Neg100WeightUpper j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftThreeBatch030Neg100WeightUpper j) / 1600) ≤ (-492519 / 25000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftThreeBatch030Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (600 : ℝ) / 1600 = 30 / 80 by norm_num,
    show ((600 : ℝ) + 20) / 1600 = (30 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch030Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-603513 / 200000000000 : ℝ)
  | 1 => (-3072467 / 1000000000000 : ℝ)
  | 2 => (-1563909 / 500000000000 : ℝ)
  | 3 => (-1591807 / 500000000000 : ℝ)
  | 4 => (-202491 / 62500000000 : ℝ)
  | 5 => (-3296539 / 1000000000000 : ℝ)
  | 6 => (-3353663 / 1000000000000 : ℝ)
  | 7 => (-426403 / 125000000000 : ℝ)
  | 8 => (-1734611 / 500000000000 : ℝ)
  | 9 => (-881913 / 250000000000 : ℝ)
  | 10 => (-224157 / 62500000000 : ℝ)
  | 11 => (-18229 / 5000000000 : ℝ)
  | 12 => (-463189 / 125000000000 : ℝ)
  | 13 => (-1882823 / 500000000000 : ℝ)
  | 14 => (-3826199 / 1000000000000 : ℝ)
  | 15 => (-1943583 / 500000000000 : ℝ)
  | 16 => (-1974273 / 500000000000 : ℝ)
  | 17 => (-2005167 / 500000000000 : ℝ)
  | 18 => (-4072527 / 1000000000000 : ℝ)
  | 19 => (-51689 / 12500000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch030Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-370389 / 125000000000 : ℝ)
  | 1 => (-754391 / 250000000000 : ℝ)
  | 2 => (-1536233 / 500000000000 : ℝ)
  | 3 => (-3127817 / 1000000000000 : ℝ)
  | 4 => (-3183613 / 1000000000000 : ℝ)
  | 5 => (-647971 / 200000000000 : ℝ)
  | 6 => (-1648269 / 500000000000 : ℝ)
  | 7 => (-1676831 / 500000000000 : ℝ)
  | 8 => (-3411223 / 1000000000000 : ℝ)
  | 9 => (-3469221 / 1000000000000 : ℝ)
  | 10 => (-3527651 / 1000000000000 : ℝ)
  | 11 => (-3586511 / 1000000000000 : ℝ)
  | 12 => (-3645799 / 1000000000000 : ℝ)
  | 13 => (-3705511 / 1000000000000 : ℝ)
  | 14 => (-753129 / 200000000000 : ℝ)
  | 15 => (-1913099 / 500000000000 : ℝ)
  | 16 => (-777433 / 200000000000 : ℝ)
  | 17 => (-789709 / 200000000000 : ℝ)
  | 18 => (-4010333 / 1000000000000 : ℝ)
  | 19 => (-2036263 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch030Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((600 : ℝ) + (j.val : ℝ)) / 1600)
      (((600 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch030Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch030Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((600 : ℝ) + (j.val : ℝ)) / 1600)
    (((600 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch030Neg70WeightLower j.val) (hpThetaShiftThreeBatch030Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch030Neg70WeightLower, hpThetaShiftThreeBatch030Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch030Neg70_integral_bounds :
    (-3637059 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-17633177 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (600 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch030Lower hpThetaJensenCellsBatch030Upper
    hpThetaShiftThreeBatch030Neg70WeightLower hpThetaShiftThreeBatch030Neg70WeightUpper hpThetaJensenCellsBatch030_bounds hpThetaShiftThreeBatch030Neg70_weight_bounds
  have hl : (-3637059 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch030Lower j * hpThetaShiftThreeBatch030Neg70WeightLower j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftThreeBatch030Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftThreeBatch030Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch030Lower j * hpThetaShiftThreeBatch030Neg70WeightUpper j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftThreeBatch030Neg70WeightUpper j) / 1600) ≤ (-17633177 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftThreeBatch030Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (600 : ℝ) / 1600 = 30 / 80 by norm_num,
    show ((600 : ℝ) + 20) / 1600 = (30 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch030Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (171329 / 100000000000 : ℝ)
  | 1 => (52753 / 31250000000 : ℝ)
  | 2 => (415577 / 250000000000 : ℝ)
  | 3 => (1635919 / 1000000000000 : ℝ)
  | 4 => (402231 / 250000000000 : ℝ)
  | 5 => (1581317 / 1000000000000 : ℝ)
  | 6 => (388273 / 250000000000 : ℝ)
  | 7 => (381061 / 250000000000 : ℝ)
  | 8 => (1494767 / 1000000000000 : ℝ)
  | 9 => (732327 / 500000000000 : ℝ)
  | 10 => (716951 / 500000000000 : ℝ)
  | 11 => (1402503 / 1000000000000 : ℝ)
  | 12 => (342613 / 250000000000 : ℝ)
  | 13 => (1337743 / 1000000000000 : ℝ)
  | 14 => (130437 / 100000000000 : ℝ)
  | 15 => (158791 / 125000000000 : ℝ)
  | 16 => (308903 / 250000000000 : ℝ)
  | 17 => (600107 / 500000000000 : ℝ)
  | 18 => (116413 / 100000000000 : ℝ)
  | 19 => (563677 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch030Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (347579 / 200000000000 : ℝ)
  | 1 => (1713291 / 1000000000000 : ℝ)
  | 2 => (1688097 / 1000000000000 : ℝ)
  | 3 => (1662309 / 1000000000000 : ℝ)
  | 4 => (20449 / 12500000000 : ℝ)
  | 5 => (64357 / 40000000000 : ℝ)
  | 6 => (790659 / 500000000000 : ℝ)
  | 7 => (1553093 / 1000000000000 : ℝ)
  | 8 => (304849 / 200000000000 : ℝ)
  | 9 => (93423 / 62500000000 : ℝ)
  | 10 => (292931 / 200000000000 : ℝ)
  | 11 => (1433903 / 1000000000000 : ℝ)
  | 12 => (175313 / 125000000000 : ℝ)
  | 13 => (1370453 / 1000000000000 : ℝ)
  | 14 => (83609 / 62500000000 : ℝ)
  | 15 => (1304371 / 1000000000000 : ℝ)
  | 16 => (1270329 / 1000000000000 : ℝ)
  | 17 => (1235613 / 1000000000000 : ℝ)
  | 18 => (240043 / 200000000000 : ℝ)
  | 19 => (1164131 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch030Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((600 : ℝ) + (j.val : ℝ)) / 1600)
      (((600 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch030Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch030Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((600 : ℝ) + (j.val : ℝ)) / 1600)
    (((600 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch030Neg45WeightLower j.val) (hpThetaShiftThreeBatch030Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch030Neg45WeightLower, hpThetaShiftThreeBatch030Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch030Neg45_integral_bounds :
    (3642403 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (7544727 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (600 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch030Lower hpThetaJensenCellsBatch030Upper
    hpThetaShiftThreeBatch030Neg45WeightLower hpThetaShiftThreeBatch030Neg45WeightUpper hpThetaJensenCellsBatch030_bounds hpThetaShiftThreeBatch030Neg45_weight_bounds
  have hl : (3642403 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch030Lower j * hpThetaShiftThreeBatch030Neg45WeightLower j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftThreeBatch030Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftThreeBatch030Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch030Lower j * hpThetaShiftThreeBatch030Neg45WeightUpper j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftThreeBatch030Neg45WeightUpper j) / 1600) ≤ (7544727 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftThreeBatch030Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (600 : ℝ) / 1600 = 30 / 80 by norm_num,
    show ((600 : ℝ) + 20) / 1600 = (30 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch030Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (8944173 / 1000000000000 : ℝ)
  | 1 => (562271 / 62500000000 : ℝ)
  | 2 => (565531 / 62500000000 : ℝ)
  | 3 => (182013 / 20000000000 : ℝ)
  | 4 => (9152793 / 1000000000000 : ℝ)
  | 5 => (230123 / 25000000000 : ℝ)
  | 6 => (2314257 / 250000000000 : ℝ)
  | 7 => (9309113 / 1000000000000 : ℝ)
  | 8 => (9361169 / 1000000000000 : ℝ)
  | 9 => (9413193 / 1000000000000 : ℝ)
  | 10 => (473259 / 50000000000 : ℝ)
  | 11 => (4758563 / 500000000000 : ℝ)
  | 12 => (4784513 / 500000000000 : ℝ)
  | 13 => (2405219 / 250000000000 : ℝ)
  | 14 => (9672671 / 1000000000000 : ℝ)
  | 15 => (4862203 / 500000000000 : ℝ)
  | 16 => (2444019 / 250000000000 : ℝ)
  | 17 => (4913839 / 500000000000 : ℝ)
  | 18 => (4939603 / 500000000000 : ℝ)
  | 19 => (4965327 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch030Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (8996337 / 1000000000000 : ℝ)
  | 1 => (9048497 / 1000000000000 : ℝ)
  | 2 => (9100651 / 1000000000000 : ℝ)
  | 3 => (4576397 / 500000000000 : ℝ)
  | 4 => (9204921 / 1000000000000 : ℝ)
  | 5 => (9257029 / 1000000000000 : ℝ)
  | 6 => (4654557 / 500000000000 : ℝ)
  | 7 => (936117 / 100000000000 : ℝ)
  | 8 => (4706597 / 500000000000 : ℝ)
  | 9 => (9465181 / 1000000000000 : ℝ)
  | 10 => (9517127 / 1000000000000 : ℝ)
  | 11 => (9569027 / 1000000000000 : ℝ)
  | 12 => (9620877 / 1000000000000 : ℝ)
  | 13 => (302271 / 31250000000 : ℝ)
  | 14 => (9724407 / 1000000000000 : ℝ)
  | 15 => (9776077 / 1000000000000 : ℝ)
  | 16 => (9827679 / 1000000000000 : ℝ)
  | 17 => (9879207 / 1000000000000 : ℝ)
  | 18 => (1986131 / 200000000000 : ℝ)
  | 19 => (499101 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch030Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((600 : ℝ) + (j.val : ℝ)) / 1600)
      (((600 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch030Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch030Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((600 : ℝ) + (j.val : ℝ)) / 1600)
    (((600 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch030Neg25WeightLower j.val) (hpThetaShiftThreeBatch030Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch030Neg25WeightLower, hpThetaShiftThreeBatch030Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch030Neg25_integral_bounds :
    (11892327 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (48516247 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (600 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch030Lower hpThetaJensenCellsBatch030Upper
    hpThetaShiftThreeBatch030Neg25WeightLower hpThetaShiftThreeBatch030Neg25WeightUpper hpThetaJensenCellsBatch030_bounds hpThetaShiftThreeBatch030Neg25_weight_bounds
  have hl : (11892327 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch030Lower j * hpThetaShiftThreeBatch030Neg25WeightLower j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftThreeBatch030Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftThreeBatch030Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch030Lower j * hpThetaShiftThreeBatch030Neg25WeightUpper j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftThreeBatch030Neg25WeightUpper j) / 1600) ≤ (48516247 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftThreeBatch030Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (600 : ℝ) / 1600 = 30 / 80 by norm_num,
    show ((600 : ℝ) + 20) / 1600 = (30 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch030Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch030Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch030Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch030Neg25_integral_bounds
end HodgeProofHP
