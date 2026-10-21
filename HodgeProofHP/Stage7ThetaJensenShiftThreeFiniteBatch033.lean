/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch033

/-! Exact signed weight and batch integral certificates, batch 33 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch033Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3614079 / 1000000000000 : ℝ)
  | 1 => (-3573701 / 1000000000000 : ℝ)
  | 2 => (-353153 / 100000000000 : ℝ)
  | 3 => (-217971 / 62500000000 : ℝ)
  | 4 => (-430211 / 125000000000 : ℝ)
  | 5 => (-3393957 / 1000000000000 : ℝ)
  | 6 => (-3344313 / 1000000000000 : ℝ)
  | 7 => (-1646363 / 500000000000 : ℝ)
  | 8 => (-647833 / 200000000000 : ℝ)
  | 9 => (-3183599 / 1000000000000 : ℝ)
  | 10 => (-1562999 / 500000000000 : ℝ)
  | 11 => (-306633 / 100000000000 : ℝ)
  | 12 => (-3004563 / 1000000000000 : ℝ)
  | 13 => (-735167 / 250000000000 : ℝ)
  | 14 => (-287461 / 100000000000 : ℝ)
  | 15 => (-70159 / 25000000000 : ℝ)
  | 16 => (-683971 / 250000000000 : ℝ)
  | 17 => (-2663149 / 1000000000000 : ℝ)
  | 18 => (-647031 / 250000000000 : ℝ)
  | 19 => (-313847 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch033Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-35737 / 10000000000 : ℝ)
  | 1 => (-3531529 / 1000000000000 : ℝ)
  | 2 => (-697507 / 200000000000 : ℝ)
  | 3 => (-3441687 / 1000000000000 : ℝ)
  | 4 => (-848489 / 250000000000 : ℝ)
  | 5 => (-418039 / 125000000000 : ℝ)
  | 6 => (-131709 / 40000000000 : ℝ)
  | 7 => (-809791 / 250000000000 : ℝ)
  | 8 => (-1591799 / 500000000000 : ℝ)
  | 9 => (-3125997 / 1000000000000 : ℝ)
  | 10 => (-3066329 / 1000000000000 : ℝ)
  | 11 => (-1502281 / 500000000000 : ℝ)
  | 12 => (-2940667 / 1000000000000 : ℝ)
  | 13 => (-2874609 / 1000000000000 : ℝ)
  | 14 => (-2806359 / 1000000000000 : ℝ)
  | 15 => (-2735883 / 1000000000000 : ℝ)
  | 16 => (-665787 / 250000000000 : ℝ)
  | 17 => (-2588123 / 1000000000000 : ℝ)
  | 18 => (-100431 / 40000000000 : ℝ)
  | 19 => (-2431071 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch033Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((660 : ℝ) + (j.val : ℝ)) / 1600)
      (((660 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch033Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch033Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((660 : ℝ) + (j.val : ℝ)) / 1600)
    (((660 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch033Neg100WeightLower j.val) (hpThetaShiftThreeBatch033Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch033Neg100WeightLower, hpThetaShiftThreeBatch033Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch033Neg100_integral_bounds :
    (-11467497 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-11086727 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (660 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch033Lower hpThetaJensenCellsBatch033Upper
    hpThetaShiftThreeBatch033Neg100WeightLower hpThetaShiftThreeBatch033Neg100WeightUpper hpThetaJensenCellsBatch033_bounds hpThetaShiftThreeBatch033Neg100_weight_bounds
  have hl : (-11467497 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch033Lower j * hpThetaShiftThreeBatch033Neg100WeightLower j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftThreeBatch033Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftThreeBatch033Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch033Lower j * hpThetaShiftThreeBatch033Neg100WeightUpper j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftThreeBatch033Neg100WeightUpper j) / 1600) ≤ (-11086727 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftThreeBatch033Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (660 : ℝ) / 1600 = 33 / 80 by norm_num,
    show ((660 : ℝ) + 20) / 1600 = (33 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch033Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3489843 / 500000000000 : ℝ)
  | 1 => (-3526837 / 500000000000 : ℝ)
  | 2 => (-28511 / 4000000000 : ℝ)
  | 3 => (-7201901 / 1000000000000 : ℝ)
  | 4 => (-1819029 / 250000000000 : ℝ)
  | 5 => (-459399 / 62500000000 : ℝ)
  | 6 => (-1856173 / 250000000000 : ℝ)
  | 7 => (-1874757 / 250000000000 : ℝ)
  | 8 => (-378669 / 50000000000 : ℝ)
  | 9 => (-1529547 / 200000000000 : ℝ)
  | 10 => (-7722079 / 1000000000000 : ℝ)
  | 11 => (-7796401 / 1000000000000 : ℝ)
  | 12 => (-3935343 / 500000000000 : ℝ)
  | 13 => (-7944921 / 1000000000000 : ℝ)
  | 14 => (-8019091 / 1000000000000 : ℝ)
  | 15 => (-15807 / 1953125000 : ℝ)
  | 16 => (-510449 / 62500000000 : ℝ)
  | 17 => (-8241077 / 1000000000000 : ℝ)
  | 18 => (-259839 / 31250000000 : ℝ)
  | 19 => (-8388483 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch033Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1381159 / 200000000000 : ℝ)
  | 1 => (-1395937 / 200000000000 : ℝ)
  | 2 => (-7053673 / 1000000000000 : ℝ)
  | 3 => (-7127749 / 1000000000000 : ℝ)
  | 4 => (-72019 / 10000000000 : ℝ)
  | 5 => (-1455223 / 200000000000 : ℝ)
  | 6 => (-7350383 / 1000000000000 : ℝ)
  | 7 => (-7424691 / 1000000000000 : ℝ)
  | 8 => (-7499027 / 1000000000000 : ℝ)
  | 9 => (-7573379 / 1000000000000 : ℝ)
  | 10 => (-3823867 / 500000000000 : ℝ)
  | 11 => (-3861039 / 500000000000 : ℝ)
  | 12 => (-19491 / 2500000000 : ℝ)
  | 13 => (-1574137 / 200000000000 : ℝ)
  | 14 => (-198623 / 25000000000 : ℝ)
  | 15 => (-801909 / 100000000000 : ℝ)
  | 16 => (-8093183 / 1000000000000 : ℝ)
  | 17 => (-8167183 / 1000000000000 : ℝ)
  | 18 => (-2060269 / 250000000000 : ℝ)
  | 19 => (-8314847 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch033Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((660 : ℝ) + (j.val : ℝ)) / 1600)
      (((660 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch033Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch033Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((660 : ℝ) + (j.val : ℝ)) / 1600)
    (((660 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch033Neg70WeightLower j.val) (hpThetaShiftThreeBatch033Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch033Neg70WeightLower, hpThetaShiftThreeBatch033Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch033Neg70_integral_bounds :
    (-438747 / 15625000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-27398583 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (660 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch033Lower hpThetaJensenCellsBatch033Upper
    hpThetaShiftThreeBatch033Neg70WeightLower hpThetaShiftThreeBatch033Neg70WeightUpper hpThetaJensenCellsBatch033_bounds hpThetaShiftThreeBatch033Neg70_weight_bounds
  have hl : (-438747 / 15625000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch033Lower j * hpThetaShiftThreeBatch033Neg70WeightLower j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftThreeBatch033Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftThreeBatch033Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch033Lower j * hpThetaShiftThreeBatch033Neg70WeightUpper j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftThreeBatch033Neg70WeightUpper j) / 1600) ≤ (-27398583 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftThreeBatch033Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (660 : ℝ) / 1600 = 33 / 80 by norm_num,
    show ((660 : ℝ) + 20) / 1600 = (33 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch033Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-209351 / 200000000000 : ℝ)
  | 1 => (-1117701 / 1000000000000 : ℝ)
  | 2 => (-1189577 / 1000000000000 : ℝ)
  | 3 => (-315597 / 250000000000 : ℝ)
  | 4 => (-668069 / 500000000000 : ℝ)
  | 5 => (-88177 / 62500000000 : ℝ)
  | 6 => (-371619 / 250000000000 : ℝ)
  | 7 => (-781537 / 500000000000 : ℝ)
  | 8 => (-1640631 / 1000000000000 : ℝ)
  | 9 => (-1719151 / 1000000000000 : ℝ)
  | 10 => (-22483 / 12500000000 : ℝ)
  | 11 => (-939551 / 500000000000 : ℝ)
  | 12 => (-980271 / 500000000000 : ℝ)
  | 13 => (-510741 / 250000000000 : ℝ)
  | 14 => (-2126373 / 1000000000000 : ℝ)
  | 15 => (-2210773 / 1000000000000 : ℝ)
  | 16 => (-2296169 / 1000000000000 : ℝ)
  | 17 => (-476513 / 200000000000 : ℝ)
  | 18 => (-1234983 / 500000000000 : ℝ)
  | 19 => (-20467 / 8000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch033Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-244183 / 250000000000 : ℝ)
  | 1 => (-523377 / 500000000000 : ℝ)
  | 2 => (-11177 / 10000000000 : ℝ)
  | 3 => (-148697 / 125000000000 : ℝ)
  | 4 => (-1262387 / 1000000000000 : ℝ)
  | 5 => (-1336137 / 1000000000000 : ℝ)
  | 6 => (-1410831 / 1000000000000 : ℝ)
  | 7 => (-59459 / 40000000000 : ℝ)
  | 8 => (-1563073 / 1000000000000 : ℝ)
  | 9 => (-164063 / 100000000000 : ℝ)
  | 10 => (-34383 / 20000000000 : ℝ)
  | 11 => (-1798639 / 1000000000000 : ℝ)
  | 12 => (-1879101 / 1000000000000 : ℝ)
  | 13 => (-1960541 / 1000000000000 : ℝ)
  | 14 => (-2042963 / 1000000000000 : ℝ)
  | 15 => (-531593 / 250000000000 : ℝ)
  | 16 => (-552693 / 250000000000 : ℝ)
  | 17 => (-287021 / 125000000000 : ℝ)
  | 18 => (-595641 / 250000000000 : ℝ)
  | 19 => (-493993 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch033Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((660 : ℝ) + (j.val : ℝ)) / 1600)
      (((660 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch033Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch033Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((660 : ℝ) + (j.val : ℝ)) / 1600)
    (((660 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch033Neg45WeightLower j.val) (hpThetaShiftThreeBatch033Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch033Neg45WeightLower, hpThetaShiftThreeBatch033Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch033Neg45_integral_bounds :
    (-6440567 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-1515251 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (660 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch033Lower hpThetaJensenCellsBatch033Upper
    hpThetaShiftThreeBatch033Neg45WeightLower hpThetaShiftThreeBatch033Neg45WeightUpper hpThetaJensenCellsBatch033_bounds hpThetaShiftThreeBatch033Neg45_weight_bounds
  have hl : (-6440567 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch033Lower j * hpThetaShiftThreeBatch033Neg45WeightLower j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftThreeBatch033Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftThreeBatch033Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch033Lower j * hpThetaShiftThreeBatch033Neg45WeightUpper j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftThreeBatch033Neg45WeightUpper j) / 1600) ≤ (-1515251 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftThreeBatch033Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (660 : ℝ) / 1600 = 33 / 80 by norm_num,
    show ((660 : ℝ) + 20) / 1600 = (33 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch033Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (5952701 / 500000000000 : ℝ)
  | 1 => (5974241 / 500000000000 : ℝ)
  | 2 => (5995613 / 500000000000 : ℝ)
  | 3 => (6016813 / 500000000000 : ℝ)
  | 4 => (3018919 / 250000000000 : ℝ)
  | 5 => (1514671 / 125000000000 : ℝ)
  | 6 => (2431739 / 200000000000 : ℝ)
  | 7 => (243993 / 20000000000 : ℝ)
  | 8 => (489609 / 40000000000 : ℝ)
  | 9 => (3070103 / 250000000000 : ℝ)
  | 10 => (2464041 / 200000000000 : ℝ)
  | 11 => (2471919 / 200000000000 : ℝ)
  | 12 => (495943 / 40000000000 : ℝ)
  | 13 => (12437137 / 1000000000000 : ℝ)
  | 14 => (6237637 / 500000000000 : ℝ)
  | 15 => (12512977 / 1000000000000 : ℝ)
  | 16 => (12550239 / 1000000000000 : ℝ)
  | 17 => (3146763 / 250000000000 : ℝ)
  | 18 => (788963 / 62500000000 : ℝ)
  | 19 => (6329649 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch033Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (11948483 / 1000000000000 : ℝ)
  | 1 => (11991227 / 1000000000000 : ℝ)
  | 2 => (12033627 / 1000000000000 : ℝ)
  | 3 => (12075677 / 1000000000000 : ℝ)
  | 4 => (12117369 / 1000000000000 : ℝ)
  | 5 => (1519837 / 125000000000 : ℝ)
  | 6 => (12199651 / 1000000000000 : ℝ)
  | 7 => (6120113 / 500000000000 : ℝ)
  | 8 => (12280413 / 1000000000000 : ℝ)
  | 9 => (6160103 / 500000000000 : ℝ)
  | 10 => (3089899 / 250000000000 : ℝ)
  | 11 => (774911 / 62500000000 : ℝ)
  | 12 => (6218569 / 500000000000 : ℝ)
  | 13 => (499011 / 40000000000 : ℝ)
  | 14 => (6256489 / 500000000000 : ℝ)
  | 15 => (78439 / 6250000000 : ℝ)
  | 16 => (12587053 / 1000000000000 : ℝ)
  | 17 => (12623409 / 1000000000000 : ℝ)
  | 18 => (12659299 / 1000000000000 : ℝ)
  | 19 => (3173679 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch033Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((660 : ℝ) + (j.val : ℝ)) / 1600)
      (((660 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch033Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch033Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((660 : ℝ) + (j.val : ℝ)) / 1600)
    (((660 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch033Neg25WeightLower j.val) (hpThetaShiftThreeBatch033Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch033Neg25WeightLower, hpThetaShiftThreeBatch033Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch033Neg25_integral_bounds :
    (173109 / 3906250000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (45123419 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (660 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch033Lower hpThetaJensenCellsBatch033Upper
    hpThetaShiftThreeBatch033Neg25WeightLower hpThetaShiftThreeBatch033Neg25WeightUpper hpThetaJensenCellsBatch033_bounds hpThetaShiftThreeBatch033Neg25_weight_bounds
  have hl : (173109 / 3906250000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch033Lower j * hpThetaShiftThreeBatch033Neg25WeightLower j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftThreeBatch033Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftThreeBatch033Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch033Lower j * hpThetaShiftThreeBatch033Neg25WeightUpper j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftThreeBatch033Neg25WeightUpper j) / 1600) ≤ (45123419 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftThreeBatch033Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (660 : ℝ) / 1600 = 33 / 80 by norm_num,
    show ((660 : ℝ) + 20) / 1600 = (33 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch033Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch033Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch033Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch033Neg25_integral_bounds
end HodgeProofHP
