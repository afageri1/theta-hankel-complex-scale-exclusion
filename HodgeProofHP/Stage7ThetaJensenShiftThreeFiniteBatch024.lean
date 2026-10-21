/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch024

/-! Exact signed weight and batch integral certificates, batch 24 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch024Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-599231 / 1000000000000 : ℝ)
  | 1 => (-616829 / 1000000000000 : ℝ)
  | 2 => (-634653 / 1000000000000 : ℝ)
  | 3 => (-130541 / 200000000000 : ℝ)
  | 4 => (-83873 / 125000000000 : ℝ)
  | 5 => (-68949 / 100000000000 : ℝ)
  | 6 => (-5533 / 7812500000 : ℝ)
  | 7 => (-145437 / 200000000000 : ℝ)
  | 8 => (-373187 / 500000000000 : ℝ)
  | 9 => (-765791 / 1000000000000 : ℝ)
  | 10 => (-392717 / 500000000000 : ℝ)
  | 11 => (-402653 / 500000000000 : ℝ)
  | 12 => (-206351 / 250000000000 : ℝ)
  | 13 => (-845729 / 1000000000000 : ℝ)
  | 14 => (-21657 / 25000000000 : ℝ)
  | 15 => (-887057 / 1000000000000 : ℝ)
  | 16 => (-45403 / 50000000000 : ℝ)
  | 17 => (-116161 / 125000000000 : ℝ)
  | 18 => (-47537 / 50000000000 : ℝ)
  | 19 => (-7597 / 7812500000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch024Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-290929 / 500000000000 : ℝ)
  | 1 => (-59923 / 100000000000 : ℝ)
  | 2 => (-154207 / 250000000000 : ℝ)
  | 3 => (-158663 / 250000000000 : ℝ)
  | 4 => (-20397 / 31250000000 : ℝ)
  | 5 => (-670983 / 1000000000000 : ℝ)
  | 6 => (-689489 / 1000000000000 : ℝ)
  | 7 => (-708223 / 1000000000000 : ℝ)
  | 8 => (-45449 / 62500000000 : ℝ)
  | 9 => (-746373 / 1000000000000 : ℝ)
  | 10 => (-76579 / 100000000000 : ℝ)
  | 11 => (-785433 / 1000000000000 : ℝ)
  | 12 => (-161061 / 200000000000 : ℝ)
  | 13 => (-825403 / 1000000000000 : ℝ)
  | 14 => (-26429 / 31250000000 : ℝ)
  | 15 => (-866279 / 1000000000000 : ℝ)
  | 16 => (-55441 / 62500000000 : ℝ)
  | 17 => (-908059 / 1000000000000 : ℝ)
  | 18 => (-929287 / 1000000000000 : ℝ)
  | 19 => (-950739 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch024Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((480 : ℝ) + (j.val : ℝ)) / 1600)
      (((480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch024Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch024Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((480 : ℝ) + (j.val : ℝ)) / 1600)
    (((480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch024Neg100WeightLower j.val) (hpThetaShiftThreeBatch024Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch024Neg100WeightLower, hpThetaShiftThreeBatch024Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch024Neg100_integral_bounds :
    (-172631 / 25000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-207627 / 31250000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch024Lower hpThetaJensenCellsBatch024Upper
    hpThetaShiftThreeBatch024Neg100WeightLower hpThetaShiftThreeBatch024Neg100WeightUpper hpThetaJensenCellsBatch024_bounds hpThetaShiftThreeBatch024Neg100_weight_bounds
  have hl : (-172631 / 25000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch024Lower j * hpThetaShiftThreeBatch024Neg100WeightLower j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftThreeBatch024Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftThreeBatch024Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch024Lower j * hpThetaShiftThreeBatch024Neg100WeightUpper j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftThreeBatch024Neg100WeightUpper j) / 1600) ≤ (-207627 / 31250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftThreeBatch024Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (480 : ℝ) / 1600 = 24 / 80 by norm_num,
    show ((480 : ℝ) + 20) / 1600 = (24 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch024Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (7223 / 15625000000 : ℝ)
  | 1 => (14191 / 31250000000 : ℝ)
  | 2 => (445709 / 1000000000000 : ℝ)
  | 3 => (437059 / 1000000000000 : ℝ)
  | 4 => (428159 / 1000000000000 : ℝ)
  | 5 => (209503 / 500000000000 : ℝ)
  | 6 => (204799 / 500000000000 : ℝ)
  | 7 => (399931 / 1000000000000 : ℝ)
  | 8 => (195001 / 500000000000 : ℝ)
  | 9 => (379809 / 1000000000000 : ℝ)
  | 10 => (369349 / 1000000000000 : ℝ)
  | 11 => (179309 / 500000000000 : ℝ)
  | 12 => (173807 / 500000000000 : ℝ)
  | 13 => (168167 / 500000000000 : ℝ)
  | 14 => (162387 / 500000000000 : ℝ)
  | 15 => (312933 / 1000000000000 : ℝ)
  | 16 => (60161 / 200000000000 : ℝ)
  | 17 => (28839 / 100000000000 : ℝ)
  | 18 => (68921 / 250000000000 : ℝ)
  | 19 => (262683 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch024Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (29387 / 62500000000 : ℝ)
  | 1 => (462273 / 1000000000000 : ℝ)
  | 2 => (454113 / 1000000000000 : ℝ)
  | 3 => (44571 / 100000000000 : ℝ)
  | 4 => (21853 / 50000000000 : ℝ)
  | 5 => (669 / 1562500000 : ℝ)
  | 6 => (419007 / 1000000000000 : ℝ)
  | 7 => (409599 / 1000000000000 : ℝ)
  | 8 => (99983 / 250000000000 : ℝ)
  | 9 => (390003 / 1000000000000 : ℝ)
  | 10 => (37981 / 100000000000 : ℝ)
  | 11 => (7387 / 20000000000 : ℝ)
  | 12 => (358619 / 1000000000000 : ℝ)
  | 13 => (69523 / 200000000000 : ℝ)
  | 14 => (67267 / 200000000000 : ℝ)
  | 15 => (12991 / 40000000000 : ℝ)
  | 16 => (156467 / 500000000000 : ℝ)
  | 17 => (150403 / 500000000000 : ℝ)
  | 18 => (288391 / 1000000000000 : ℝ)
  | 19 => (55137 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch024Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((480 : ℝ) + (j.val : ℝ)) / 1600)
      (((480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch024Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch024Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((480 : ℝ) + (j.val : ℝ)) / 1600)
    (((480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch024Neg70WeightLower j.val) (hpThetaShiftThreeBatch024Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch024Neg70WeightLower, hpThetaShiftThreeBatch024Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch024Neg70_integral_bounds :
    (3259847 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (3394823 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch024Lower hpThetaJensenCellsBatch024Upper
    hpThetaShiftThreeBatch024Neg70WeightLower hpThetaShiftThreeBatch024Neg70WeightUpper hpThetaJensenCellsBatch024_bounds hpThetaShiftThreeBatch024Neg70_weight_bounds
  have hl : (3259847 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch024Lower j * hpThetaShiftThreeBatch024Neg70WeightLower j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftThreeBatch024Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftThreeBatch024Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch024Lower j * hpThetaShiftThreeBatch024Neg70WeightUpper j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftThreeBatch024Neg70WeightUpper j) / 1600) ≤ (3394823 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftThreeBatch024Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (480 : ℝ) / 1600 = 24 / 80 by norm_num,
    show ((480 : ℝ) + 20) / 1600 = (24 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch024Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1916227 / 1000000000000 : ℝ)
  | 1 => (1927153 / 1000000000000 : ℝ)
  | 2 => (1938007 / 1000000000000 : ℝ)
  | 3 => (487197 / 250000000000 : ℝ)
  | 4 => (489873 / 250000000000 : ℝ)
  | 5 => (1970117 / 1000000000000 : ℝ)
  | 6 => (1980659 / 1000000000000 : ℝ)
  | 7 => (995559 / 500000000000 : ℝ)
  | 8 => (125093 / 62500000000 : ℝ)
  | 9 => (251471 / 125000000000 : ℝ)
  | 10 => (505489 / 250000000000 : ℝ)
  | 11 => (2032047 / 1000000000000 : ℝ)
  | 12 => (2042039 / 1000000000000 : ℝ)
  | 13 => (205193 / 100000000000 : ℝ)
  | 14 => (515429 / 250000000000 : ℝ)
  | 15 => (1035697 / 500000000000 : ℝ)
  | 16 => (2080961 / 1000000000000 : ℝ)
  | 17 => (418083 / 200000000000 : ℝ)
  | 18 => (262469 / 125000000000 : ℝ)
  | 19 => (210897 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch024Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (963577 / 500000000000 : ℝ)
  | 1 => (242251 / 125000000000 : ℝ)
  | 2 => (1948789 / 1000000000000 : ℝ)
  | 3 => (1959493 / 1000000000000 : ℝ)
  | 4 => (985059 / 500000000000 : ℝ)
  | 5 => (99033 / 50000000000 : ℝ)
  | 6 => (1991119 / 1000000000000 : ℝ)
  | 7 => (2001489 / 1000000000000 : ℝ)
  | 8 => (2011769 / 1000000000000 : ℝ)
  | 9 => (2021957 / 1000000000000 : ℝ)
  | 10 => (127003 / 62500000000 : ℝ)
  | 11 => (51051 / 25000000000 : ℝ)
  | 12 => (2051931 / 1000000000000 : ℝ)
  | 13 => (2061717 / 1000000000000 : ℝ)
  | 14 => (414279 / 200000000000 : ℝ)
  | 15 => (1040481 / 500000000000 : ℝ)
  | 16 => (130651 / 62500000000 : ℝ)
  | 17 => (2099753 / 1000000000000 : ℝ)
  | 18 => (2108971 / 1000000000000 : ℝ)
  | 19 => (423613 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch024Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((480 : ℝ) + (j.val : ℝ)) / 1600)
      (((480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch024Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch024Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((480 : ℝ) + (j.val : ℝ)) / 1600)
    (((480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch024Neg45WeightLower j.val) (hpThetaShiftThreeBatch024Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch024Neg45WeightLower, hpThetaShiftThreeBatch024Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch024Neg45_integral_bounds :
    (17670299 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (8996817 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch024Lower hpThetaJensenCellsBatch024Upper
    hpThetaShiftThreeBatch024Neg45WeightLower hpThetaShiftThreeBatch024Neg45WeightUpper hpThetaJensenCellsBatch024_bounds hpThetaShiftThreeBatch024Neg45_weight_bounds
  have hl : (17670299 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch024Lower j * hpThetaShiftThreeBatch024Neg45WeightLower j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftThreeBatch024Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftThreeBatch024Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch024Lower j * hpThetaShiftThreeBatch024Neg45WeightUpper j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftThreeBatch024Neg45WeightUpper j) / 1600) ≤ (8996817 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftThreeBatch024Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (480 : ℝ) / 1600 = 24 / 80 by norm_num,
    show ((480 : ℝ) + 20) / 1600 = (24 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch024Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3499627 / 1000000000000 : ℝ)
  | 1 => (3534171 / 1000000000000 : ℝ)
  | 2 => (3568929 / 1000000000000 : ℝ)
  | 3 => (3603903 / 1000000000000 : ℝ)
  | 4 => (3639091 / 1000000000000 : ℝ)
  | 5 => (3674493 / 1000000000000 : ℝ)
  | 6 => (371011 / 100000000000 : ℝ)
  | 7 => (3745941 / 1000000000000 : ℝ)
  | 8 => (1890993 / 500000000000 : ℝ)
  | 9 => (763649 / 200000000000 : ℝ)
  | 10 => (3854717 / 1000000000000 : ℝ)
  | 11 => (1945701 / 500000000000 : ℝ)
  | 12 => (3928301 / 1000000000000 : ℝ)
  | 13 => (991353 / 250000000000 : ℝ)
  | 14 => (800547 / 200000000000 : ℝ)
  | 15 => (404027 / 100000000000 : ℝ)
  | 16 => (4078017 / 1000000000000 : ℝ)
  | 17 => (164639 / 40000000000 : ℝ)
  | 18 => (129817 / 31250000000 : ℝ)
  | 19 => (4192523 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch024Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (883543 / 250000000000 : ℝ)
  | 1 => (356893 / 100000000000 : ℝ)
  | 2 => (56311 / 15625000000 : ℝ)
  | 3 => (909773 / 250000000000 : ℝ)
  | 4 => (1837247 / 500000000000 : ℝ)
  | 5 => (3710111 / 1000000000000 : ℝ)
  | 6 => (1872971 / 500000000000 : ℝ)
  | 7 => (3781987 / 1000000000000 : ℝ)
  | 8 => (1909123 / 500000000000 : ℝ)
  | 9 => (1927359 / 500000000000 : ℝ)
  | 10 => (3891403 / 1000000000000 : ℝ)
  | 11 => (1964151 / 500000000000 : ℝ)
  | 12 => (3965413 / 1000000000000 : ℝ)
  | 13 => (250171 / 62500000000 : ℝ)
  | 14 => (4040271 / 1000000000000 : ℝ)
  | 15 => (2039009 / 500000000000 : ℝ)
  | 16 => (514497 / 125000000000 : ℝ)
  | 17 => (830829 / 200000000000 : ℝ)
  | 18 => (1048131 / 250000000000 : ℝ)
  | 19 => (528889 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch024Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((480 : ℝ) + (j.val : ℝ)) / 1600)
      (((480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch024Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch024Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((480 : ℝ) + (j.val : ℝ)) / 1600)
    (((480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch024Neg25WeightLower j.val) (hpThetaShiftThreeBatch024Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch024Neg25WeightLower, hpThetaShiftThreeBatch024Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch024Neg25_integral_bounds :
    (33649439 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (17209513 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch024Lower hpThetaJensenCellsBatch024Upper
    hpThetaShiftThreeBatch024Neg25WeightLower hpThetaShiftThreeBatch024Neg25WeightUpper hpThetaJensenCellsBatch024_bounds hpThetaShiftThreeBatch024Neg25_weight_bounds
  have hl : (33649439 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch024Lower j * hpThetaShiftThreeBatch024Neg25WeightLower j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftThreeBatch024Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftThreeBatch024Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch024Lower j * hpThetaShiftThreeBatch024Neg25WeightUpper j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftThreeBatch024Neg25WeightUpper j) / 1600) ≤ (17209513 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftThreeBatch024Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (480 : ℝ) / 1600 = 24 / 80 by norm_num,
    show ((480 : ℝ) + 20) / 1600 = (24 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch024Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch024Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch024Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch024Neg25_integral_bounds
end HodgeProofHP
