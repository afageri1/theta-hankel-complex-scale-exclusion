/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch005

/-! Exact signed weight and batch integral certificates, batch 5 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch005Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (396604461 / 250000000000 : ℝ)
  | 1 => (322218339 / 200000000000 : ℝ)
  | 2 => (1635734897 / 1000000000000 : ℝ)
  | 3 => (1660339979 / 1000000000000 : ℝ)
  | 4 => (421224857 / 250000000000 : ℝ)
  | 5 => (3338683 / 1953125000 : ℝ)
  | 6 => (1083657 / 625000000 : ℝ)
  | 7 => (1758228319 / 1000000000000 : ℝ)
  | 8 => (891264699 / 500000000000 : ℝ)
  | 9 => (14115209 / 7812500000 : ℝ)
  | 10 => (91543633 / 50000000000 : ℝ)
  | 11 => (1854899371 / 1000000000000 : ℝ)
  | 12 => (1878819107 / 1000000000000 : ℝ)
  | 13 => (237828007 / 125000000000 : ℝ)
  | 14 => (1926306381 / 1000000000000 : ℝ)
  | 15 => (974929109 / 500000000000 : ℝ)
  | 16 => (986635839 / 500000000000 : ℝ)
  | 17 => (399307769 / 200000000000 : ℝ)
  | 18 => (100982589 / 50000000000 : ℝ)
  | 19 => (510650631 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch005Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (100693231 / 62500000000 : ℝ)
  | 1 => (817867449 / 500000000000 : ℝ)
  | 2 => (83016999 / 50000000000 : ℝ)
  | 3 => (1684899429 / 1000000000000 : ℝ)
  | 4 => (1709405697 / 1000000000000 : ℝ)
  | 5 => (1733851201 / 1000000000000 : ℝ)
  | 6 => (10988927 / 6250000000 : ℝ)
  | 7 => (1782529399 / 1000000000000 : ℝ)
  | 8 => (1806746753 / 1000000000000 : ℝ)
  | 9 => (1830872661 / 1000000000000 : ℝ)
  | 10 => (463724843 / 250000000000 : ℝ)
  | 11 => (469704777 / 250000000000 : ℝ)
  | 12 => (1902624057 / 1000000000000 : ℝ)
  | 13 => (963153191 / 500000000000 : ℝ)
  | 14 => (1949858219 / 1000000000000 : ℝ)
  | 15 => (1973271679 / 1000000000000 : ℝ)
  | 16 => (998269423 / 500000000000 : ℝ)
  | 17 => (2019651781 / 1000000000000 : ℝ)
  | 18 => (81704101 / 40000000000 : ℝ)
  | 19 => (1032691547 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch005Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((100 : ℝ) + (j.val : ℝ)) / 1600)
      (((100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch005Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch005Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((100 : ℝ) + (j.val : ℝ)) / 1600)
    (((100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch005Neg100WeightLower j.val) (hpThetaShiftOneBatch005Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch005Neg100WeightLower, hpThetaShiftOneBatch005Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch005Neg100_integral_bounds :
    (38629072069 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (9891266517 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch005Lower hpThetaJensenCellsBatch005Upper
    hpThetaShiftOneBatch005Neg100WeightLower hpThetaShiftOneBatch005Neg100WeightUpper hpThetaJensenCellsBatch005_bounds hpThetaShiftOneBatch005Neg100_weight_bounds
  have hl : (38629072069 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch005Lower j * hpThetaShiftOneBatch005Neg100WeightLower j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftOneBatch005Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftOneBatch005Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch005Lower j * hpThetaShiftOneBatch005Neg100WeightUpper j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftOneBatch005Neg100WeightUpper j) / 1600) ≤ (9891266517 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftOneBatch005Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (100 : ℝ) / 1600 = 5 / 80 by norm_num,
    show ((100 : ℝ) + 20) / 1600 = (5 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch005Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (855713679 / 500000000000 : ℝ)
  | 1 => (1741001351 / 1000000000000 : ℝ)
  | 2 => (1770681867 / 1000000000000 : ℝ)
  | 3 => (900231821 / 500000000000 : ℝ)
  | 4 => (7149771 / 3906250000 : ℝ)
  | 5 => (186030973 / 100000000000 : ℝ)
  | 6 => (945181667 / 500000000000 : ℝ)
  | 7 => (1920496779 / 1000000000000 : ℝ)
  | 8 => (1950704623 / 1000000000000 : ℝ)
  | 9 => (1980981389 / 1000000000000 : ℝ)
  | 10 => (402264313 / 200000000000 : ℝ)
  | 11 => (255214951 / 125000000000 : ℝ)
  | 12 => (103608497 / 50000000000 : ℝ)
  | 13 => (42053339 / 20000000000 : ℝ)
  | 14 => (2133204997 / 1000000000000 : ℝ)
  | 15 => (2163778407 / 1000000000000 : ℝ)
  | 16 => (548595369 / 250000000000 : ℝ)
  | 17 => (2225008467 / 1000000000000 : ℝ)
  | 18 => (451130723 / 200000000000 : ℝ)
  | 19 => (18290489 / 8000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch005Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (217625169 / 125000000000 : ℝ)
  | 1 => (442670467 / 250000000000 : ℝ)
  | 2 => (1800463643 / 1000000000000 : ℝ)
  | 3 => (1830341377 / 1000000000000 : ℝ)
  | 4 => (1860309731 / 1000000000000 : ℝ)
  | 5 => (378072667 / 200000000000 : ℝ)
  | 6 => (96024839 / 50000000000 : ℝ)
  | 7 => (121919039 / 62500000000 : ℝ)
  | 8 => (198098139 / 100000000000 : ℝ)
  | 9 => (1005660783 / 500000000000 : ℝ)
  | 10 => (2041719609 / 1000000000000 : ℝ)
  | 11 => (2072169941 / 1000000000000 : ℝ)
  | 12 => (2102666951 / 1000000000000 : ℝ)
  | 13 => (1066602499 / 500000000000 : ℝ)
  | 14 => (270472301 / 125000000000 : ℝ)
  | 15 => (2194381477 / 1000000000000 : ℝ)
  | 16 => (556252117 / 250000000000 : ℝ)
  | 17 => (140978351 / 62500000000 : ℝ)
  | 18 => (1143155563 / 500000000000 : ℝ)
  | 19 => (2316975173 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch005Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((100 : ℝ) + (j.val : ℝ)) / 1600)
      (((100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch005Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch005Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((100 : ℝ) + (j.val : ℝ)) / 1600)
    (((100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch005Neg65WeightLower j.val) (hpThetaShiftOneBatch005Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch005Neg65WeightLower, hpThetaShiftOneBatch005Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch005Neg65_integral_bounds :
    (21225668541 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (10891243821 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch005Lower hpThetaJensenCellsBatch005Upper
    hpThetaShiftOneBatch005Neg65WeightLower hpThetaShiftOneBatch005Neg65WeightUpper hpThetaJensenCellsBatch005_bounds hpThetaShiftOneBatch005Neg65_weight_bounds
  have hl : (21225668541 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch005Lower j * hpThetaShiftOneBatch005Neg65WeightLower j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftOneBatch005Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftOneBatch005Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch005Lower j * hpThetaShiftOneBatch005Neg65WeightUpper j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftOneBatch005Neg65WeightUpper j) / 1600) ≤ (10891243821 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftOneBatch005Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (100 : ℝ) / 1600 = 5 / 80 by norm_num,
    show ((100 : ℝ) + 20) / 1600 = (5 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch005Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (72116497 / 40000000000 : ℝ)
  | 1 => (918060249 / 500000000000 : ℝ)
  | 2 => (934769899 / 500000000000 : ℝ)
  | 3 => (1903166903 / 1000000000000 : ℝ)
  | 4 => (968499183 / 500000000000 : ℝ)
  | 5 => (197103071 / 100000000000 : ℝ)
  | 6 => (2005260429 / 1000000000000 : ℝ)
  | 7 => (1019841997 / 500000000000 : ℝ)
  | 8 => (414859569 / 200000000000 : ℝ)
  | 9 => (527274599 / 250000000000 : ℝ)
  | 10 => (536020509 / 250000000000 : ℝ)
  | 11 => (17433961 / 8000000000 : ℝ)
  | 12 => (1107291999 / 500000000000 : ℝ)
  | 13 => (2250094963 / 1000000000000 : ℝ)
  | 14 => (1142887151 / 500000000000 : ℝ)
  | 15 => (2321618271 / 1000000000000 : ℝ)
  | 16 => (1178811551 / 500000000000 : ℝ)
  | 17 => (1196892499 / 500000000000 : ℝ)
  | 18 => (2430100139 / 1000000000000 : ℝ)
  | 19 => (2466564681 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch005Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1836120499 / 1000000000000 : ℝ)
  | 1 => (1869539799 / 1000000000000 : ℝ)
  | 2 => (237895863 / 125000000000 : ℝ)
  | 3 => (1936998367 / 1000000000000 : ℝ)
  | 4 => (1971030711 / 1000000000000 : ℝ)
  | 5 => (200526043 / 100000000000 : ℝ)
  | 6 => (407936799 / 200000000000 : ℝ)
  | 7 => (1037148923 / 500000000000 : ℝ)
  | 8 => (2109098397 / 1000000000000 : ℝ)
  | 9 => (2144082037 / 1000000000000 : ℝ)
  | 10 => (1089622563 / 500000000000 : ℝ)
  | 11 => (2214583999 / 1000000000000 : ℝ)
  | 12 => (562523741 / 250000000000 : ℝ)
  | 13 => (2285774303 / 1000000000000 : ℝ)
  | 14 => (72550571 / 31250000000 : ℝ)
  | 15 => (2357623103 / 1000000000000 : ℝ)
  | 16 => (2393784999 / 1000000000000 : ℝ)
  | 17 => (121505007 / 50000000000 : ℝ)
  | 18 => (1233282341 / 500000000000 : ℝ)
  | 19 => (2503174753 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch005Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((100 : ℝ) + (j.val : ℝ)) / 1600)
      (((100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch005Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch005Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((100 : ℝ) + (j.val : ℝ)) / 1600)
    (((100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch005Neg40WeightLower j.val) (hpThetaShiftOneBatch005Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch005Neg40WeightLower, hpThetaShiftOneBatch005Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch005Neg40_integral_bounds :
    (5658093059 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (23255396807 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch005Lower hpThetaJensenCellsBatch005Upper
    hpThetaShiftOneBatch005Neg40WeightLower hpThetaShiftOneBatch005Neg40WeightUpper hpThetaJensenCellsBatch005_bounds hpThetaShiftOneBatch005Neg40_weight_bounds
  have hl : (5658093059 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch005Lower j * hpThetaShiftOneBatch005Neg40WeightLower j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftOneBatch005Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftOneBatch005Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch005Lower j * hpThetaShiftOneBatch005Neg40WeightUpper j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftOneBatch005Neg40WeightUpper j) / 1600) ≤ (23255396807 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftOneBatch005Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (100 : ℝ) / 1600 = 5 / 80 by norm_num,
    show ((100 : ℝ) + 20) / 1600 = (5 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch005Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (234678249 / 125000000000 : ℝ)
  | 1 => (1913622541 / 1000000000000 : ℝ)
  | 2 => (60941193 / 31250000000 : ℝ)
  | 3 => (1986911111 / 1000000000000 : ℝ)
  | 4 => (1011999773 / 500000000000 : ℝ)
  | 5 => (1030690833 / 500000000000 : ℝ)
  | 6 => (1049527819 / 500000000000 : ℝ)
  | 7 => (2137019613 / 1000000000000 : ℝ)
  | 8 => (135954483 / 62500000000 : ℝ)
  | 9 => (1106905051 / 500000000000 : ℝ)
  | 10 => (56315821 / 25000000000 : ℝ)
  | 11 => (229173803 / 100000000000 : ℝ)
  | 12 => (72847617 / 31250000000 : ℝ)
  | 13 => (59269701 / 25000000000 : ℝ)
  | 14 => (1205364479 / 500000000000 : ℝ)
  | 15 => (98037781 / 40000000000 : ℝ)
  | 16 => (9965731 / 4000000000 : ℝ)
  | 17 => (2532191627 / 1000000000000 : ℝ)
  | 18 => (2573219137 / 1000000000000 : ℝ)
  | 19 => (2614513243 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch005Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (956811271 / 500000000000 : ℝ)
  | 1 => (1950118177 / 1000000000000 : ℝ)
  | 2 => (248363889 / 125000000000 : ℝ)
  | 3 => (2023999547 / 1000000000000 : ℝ)
  | 4 => (2061381667 / 1000000000000 : ℝ)
  | 5 => (2099055639 / 1000000000000 : ℝ)
  | 6 => (1068509807 / 500000000000 : ℝ)
  | 7 => (2175271729 / 1000000000000 : ℝ)
  | 8 => (2213810103 / 1000000000000 : ℝ)
  | 9 => (2252632841 / 1000000000000 : ℝ)
  | 10 => (2291738031 / 1000000000000 : ℝ)
  | 11 => (466224749 / 200000000000 : ℝ)
  | 12 => (2370788041 / 1000000000000 : ℝ)
  | 13 => (2410728959 / 1000000000000 : ℝ)
  | 14 => (1225472263 / 500000000000 : ℝ)
  | 15 => (2491432751 / 1000000000000 : ℝ)
  | 16 => (633047907 / 250000000000 : ℝ)
  | 17 => (1286609569 / 500000000000 : ℝ)
  | 18 => (653628311 / 250000000000 : ℝ)
  | 19 => (2656071893 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch005Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((100 : ℝ) + (j.val : ℝ)) / 1600)
      (((100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch005Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch005Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((100 : ℝ) + (j.val : ℝ)) / 1600)
    (((100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch005Neg20WeightLower j.val) (hpThetaShiftOneBatch005Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch005Neg20WeightLower, hpThetaShiftOneBatch005Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch005Neg20_integral_bounds :
    (23782936697 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (5 / 80 : ℝ) ((5 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (24460602553 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch005Lower hpThetaJensenCellsBatch005Upper
    hpThetaShiftOneBatch005Neg20WeightLower hpThetaShiftOneBatch005Neg20WeightUpper hpThetaJensenCellsBatch005_bounds hpThetaShiftOneBatch005Neg20_weight_bounds
  have hl : (23782936697 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch005Lower j * hpThetaShiftOneBatch005Neg20WeightLower j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftOneBatch005Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftOneBatch005Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch005Lower j * hpThetaShiftOneBatch005Neg20WeightUpper j)
        (hpThetaJensenCellsBatch005Upper j * hpThetaShiftOneBatch005Neg20WeightUpper j) / 1600) ≤ (24460602553 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch005Lower, hpThetaJensenCellsBatch005Upper,
      hpThetaShiftOneBatch005Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (100 : ℝ) / 1600 = 5 / 80 by norm_num,
    show ((100 : ℝ) + 20) / 1600 = (5 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch005Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch005Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch005Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch005Neg20_integral_bounds
end HodgeProofHP
