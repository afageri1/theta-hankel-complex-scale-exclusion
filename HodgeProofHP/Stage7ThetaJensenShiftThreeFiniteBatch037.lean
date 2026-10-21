/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch037

/-! Exact signed weight and batch integral certificates, batch 37 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch037Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3996839 / 500000000000 : ℝ)
  | 1 => (8284361 / 1000000000000 : ℝ)
  | 2 => (68637 / 8000000000 : ℝ)
  | 3 => (8879503 / 1000000000000 : ℝ)
  | 4 => (9184029 / 1000000000000 : ℝ)
  | 5 => (2373309 / 250000000000 : ℝ)
  | 6 => (9807159 / 1000000000000 : ℝ)
  | 7 => (10125829 / 1000000000000 : ℝ)
  | 8 => (10449281 / 1000000000000 : ℝ)
  | 9 => (2155509 / 200000000000 : ℝ)
  | 10 => (2222131 / 200000000000 : ℝ)
  | 11 => (5724321 / 500000000000 : ℝ)
  | 12 => (11791537 / 1000000000000 : ℝ)
  | 13 => (12139371 / 1000000000000 : ℝ)
  | 14 => (499687 / 40000000000 : ℝ)
  | 15 => (12849979 / 1000000000000 : ℝ)
  | 16 => (3303203 / 250000000000 : ℝ)
  | 17 => (2716141 / 200000000000 : ℝ)
  | 18 => (2790737 / 200000000000 : ℝ)
  | 19 => (14331781 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch037Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (4142181 / 500000000000 : ℝ)
  | 1 => (4289813 / 500000000000 : ℝ)
  | 2 => (554969 / 62500000000 : ℝ)
  | 3 => (918403 / 100000000000 : ℝ)
  | 4 => (9493237 / 1000000000000 : ℝ)
  | 5 => (245179 / 25000000000 : ℝ)
  | 6 => (1012583 / 100000000000 : ℝ)
  | 7 => (5224641 / 500000000000 : ℝ)
  | 8 => (5388773 / 500000000000 : ℝ)
  | 9 => (43401 / 3906250000 : ℝ)
  | 10 => (11448643 / 1000000000000 : ℝ)
  | 11 => (5895769 / 500000000000 : ℝ)
  | 12 => (3034843 / 250000000000 : ℝ)
  | 13 => (780761 / 62500000000 : ℝ)
  | 14 => (642499 / 50000000000 : ℝ)
  | 15 => (13212813 / 1000000000000 : ℝ)
  | 16 => (6790353 / 500000000000 : ℝ)
  | 17 => (6976843 / 500000000000 : ℝ)
  | 18 => (7165891 / 500000000000 : ℝ)
  | 19 => (7357511 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch037Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((740 : ℝ) + (j.val : ℝ)) / 1600)
      (((740 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch037Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch037Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((740 : ℝ) + (j.val : ℝ)) / 1600)
    (((740 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch037Neg100WeightLower j.val) (hpThetaShiftThreeBatch037Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch037Neg100WeightLower, hpThetaShiftThreeBatch037Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch037Neg100_integral_bounds :
    (147581 / 6250000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (4944449 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (740 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch037Lower hpThetaJensenCellsBatch037Upper
    hpThetaShiftThreeBatch037Neg100WeightLower hpThetaShiftThreeBatch037Neg100WeightUpper hpThetaJensenCellsBatch037_bounds hpThetaShiftThreeBatch037Neg100_weight_bounds
  have hl : (147581 / 6250000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch037Lower j * hpThetaShiftThreeBatch037Neg100WeightLower j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftThreeBatch037Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftThreeBatch037Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch037Lower j * hpThetaShiftThreeBatch037Neg100WeightUpper j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftThreeBatch037Neg100WeightUpper j) / 1600) ≤ (4944449 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftThreeBatch037Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (740 : ℝ) / 1600 = 37 / 80 by norm_num,
    show ((740 : ℝ) + 20) / 1600 = (37 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch037Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2963947 / 250000000000 : ℝ)
  | 1 => (-11880303 / 1000000000000 : ℝ)
  | 2 => (-11903171 / 1000000000000 : ℝ)
  | 3 => (-11924359 / 1000000000000 : ℝ)
  | 4 => (-11943833 / 1000000000000 : ℝ)
  | 5 => (-2990389 / 250000000000 : ℝ)
  | 6 => (-1497187 / 125000000000 : ℝ)
  | 7 => (-187369 / 15625000000 : ℝ)
  | 8 => (-12003881 / 1000000000000 : ℝ)
  | 9 => (-2402851 / 200000000000 : ℝ)
  | 10 => (-12022701 / 1000000000000 : ℝ)
  | 11 => (-46989 / 3906250000 : ℝ)
  | 12 => (-2406733 / 200000000000 : ℝ)
  | 13 => (-12036109 / 1000000000000 : ℝ)
  | 14 => (-23509 / 1953125000 : ℝ)
  | 15 => (-3009119 / 250000000000 : ℝ)
  | 16 => (-12034729 / 1000000000000 : ℝ)
  | 17 => (-1203083 / 100000000000 : ℝ)
  | 18 => (-601237 / 50000000000 : ℝ)
  | 19 => (-600821 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch037Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5914829 / 500000000000 : ℝ)
  | 1 => (-11855787 / 1000000000000 : ℝ)
  | 2 => (-5940151 / 500000000000 : ℝ)
  | 3 => (-1190317 / 100000000000 : ℝ)
  | 4 => (-5962179 / 500000000000 : ℝ)
  | 5 => (-1492979 / 125000000000 : ℝ)
  | 6 => (-2392311 / 200000000000 : ℝ)
  | 7 => (-2395499 / 200000000000 : ℝ)
  | 8 => (-2398323 / 200000000000 : ℝ)
  | 9 => (-300097 / 25000000000 : ℝ)
  | 10 => (-6007127 / 500000000000 : ℝ)
  | 11 => (-120227 / 10000000000 : ℝ)
  | 12 => (-12029183 / 1000000000000 : ℝ)
  | 13 => (-94013 / 7812500000 : ℝ)
  | 14 => (-3009027 / 250000000000 : ℝ)
  | 15 => (-1504341 / 125000000000 : ℝ)
  | 16 => (-12030829 / 1000000000000 : ℝ)
  | 17 => (-12024739 / 1000000000000 : ℝ)
  | 18 => (-12016419 / 1000000000000 : ℝ)
  | 19 => (-1200583 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch037Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((740 : ℝ) + (j.val : ℝ)) / 1600)
      (((740 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch037Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch037Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((740 : ℝ) + (j.val : ℝ)) / 1600)
    (((740 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch037Neg70WeightLower j.val) (hpThetaShiftThreeBatch037Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch037Neg70WeightLower, hpThetaShiftThreeBatch037Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch037Neg70_integral_bounds :
    (-3282931 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-12913297 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (740 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch037Lower hpThetaJensenCellsBatch037Upper
    hpThetaShiftThreeBatch037Neg70WeightLower hpThetaShiftThreeBatch037Neg70WeightUpper hpThetaJensenCellsBatch037_bounds hpThetaShiftThreeBatch037Neg70_weight_bounds
  have hl : (-3282931 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch037Lower j * hpThetaShiftThreeBatch037Neg70WeightLower j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftThreeBatch037Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftThreeBatch037Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch037Lower j * hpThetaShiftThreeBatch037Neg70WeightUpper j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftThreeBatch037Neg70WeightUpper j) / 1600) ≤ (-12913297 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftThreeBatch037Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (740 : ℝ) / 1600 = 37 / 80 by norm_num,
    show ((740 : ℝ) + 20) / 1600 = (37 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch037Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2495763 / 250000000000 : ℝ)
  | 1 => (-10139179 / 1000000000000 : ℝ)
  | 2 => (-2059283 / 200000000000 : ℝ)
  | 3 => (-10454757 / 1000000000000 : ℝ)
  | 4 => (-2653551 / 250000000000 : ℝ)
  | 5 => (-336711 / 31250000000 : ℝ)
  | 6 => (-27341 / 2500000000 : ℝ)
  | 7 => (-2219829 / 200000000000 : ℝ)
  | 8 => (-1407873 / 125000000000 : ℝ)
  | 9 => (-11427913 / 1000000000000 : ℝ)
  | 10 => (-11593929 / 1000000000000 : ℝ)
  | 11 => (-1176103 / 100000000000 : ℝ)
  | 12 => (-1192921 / 100000000000 : ℝ)
  | 13 => (-12098467 / 1000000000000 : ℝ)
  | 14 => (-12268797 / 1000000000000 : ℝ)
  | 15 => (-3110049 / 250000000000 : ℝ)
  | 16 => (-12612659 / 1000000000000 : ℝ)
  | 17 => (-12786181 / 1000000000000 : ℝ)
  | 18 => (-12960759 / 1000000000000 : ℝ)
  | 19 => (-13136387 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch037Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2457009 / 250000000000 : ℝ)
  | 1 => (-9983051 / 1000000000000 : ℝ)
  | 2 => (-5069589 / 500000000000 : ℝ)
  | 3 => (-5148207 / 500000000000 : ℝ)
  | 4 => (-2613689 / 250000000000 : ℝ)
  | 5 => (-10614203 / 1000000000000 : ℝ)
  | 6 => (-10774751 / 1000000000000 : ℝ)
  | 7 => (-10936399 / 1000000000000 : ℝ)
  | 8 => (-1387393 / 125000000000 : ℝ)
  | 9 => (-11262983 / 1000000000000 : ℝ)
  | 10 => (-1428489 / 125000000000 : ℝ)
  | 11 => (-1449241 / 125000000000 : ℝ)
  | 12 => (-11761029 / 1000000000000 : ℝ)
  | 13 => (-11929209 / 1000000000000 : ℝ)
  | 14 => (-6049233 / 500000000000 : ℝ)
  | 15 => (-3067199 / 250000000000 : ℝ)
  | 16 => (-2488039 / 200000000000 : ℝ)
  | 17 => (-6306329 / 500000000000 : ℝ)
  | 18 => (-639309 / 50000000000 : ℝ)
  | 19 => (-6480379 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch037Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((740 : ℝ) + (j.val : ℝ)) / 1600)
      (((740 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch037Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch037Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((740 : ℝ) + (j.val : ℝ)) / 1600)
    (((740 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch037Neg45WeightLower j.val) (hpThetaShiftThreeBatch037Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch037Neg45WeightLower, hpThetaShiftThreeBatch037Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch037Neg45_integral_bounds :
    (-25178197 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-24428129 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (740 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch037Lower hpThetaJensenCellsBatch037Upper
    hpThetaShiftThreeBatch037Neg45WeightLower hpThetaShiftThreeBatch037Neg45WeightUpper hpThetaJensenCellsBatch037_bounds hpThetaShiftThreeBatch037Neg45_weight_bounds
  have hl : (-25178197 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch037Lower j * hpThetaShiftThreeBatch037Neg45WeightLower j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftThreeBatch037Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftThreeBatch037Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch037Lower j * hpThetaShiftThreeBatch037Neg45WeightUpper j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftThreeBatch037Neg45WeightUpper j) / 1600) ≤ (-24428129 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftThreeBatch037Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (740 : ℝ) / 1600 = 37 / 80 by norm_num,
    show ((740 : ℝ) + 20) / 1600 = (37 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch037Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (6802333 / 500000000000 : ℝ)
  | 1 => (13592693 / 1000000000000 : ℝ)
  | 2 => (13579629 / 1000000000000 : ℝ)
  | 3 => (6782731 / 500000000000 : ℝ)
  | 4 => (13550181 / 1000000000000 : ℝ)
  | 5 => (6766887 / 500000000000 : ℝ)
  | 6 => (1351623 / 100000000000 : ℝ)
  | 7 => (13497537 / 1000000000000 : ℝ)
  | 8 => (3369421 / 250000000000 : ℝ)
  | 9 => (6728329 / 500000000000 : ℝ)
  | 10 => (839653 / 62500000000 : ℝ)
  | 11 => (6705521 / 500000000000 : ℝ)
  | 12 => (13386429 / 1000000000000 : ℝ)
  | 13 => (2672119 / 200000000000 : ℝ)
  | 14 => (1333353 / 100000000000 : ℝ)
  | 15 => (6652611 / 500000000000 : ℝ)
  | 16 => (13275657 / 1000000000000 : ℝ)
  | 17 => (529793 / 40000000000 : ℝ)
  | 18 => (13212713 / 1000000000000 : ℝ)
  | 19 => (3294827 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch037Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (13615561 / 1000000000000 : ℝ)
  | 1 => (13604667 / 1000000000000 : ℝ)
  | 2 => (6796347 / 500000000000 : ℝ)
  | 3 => (1357963 / 100000000000 : ℝ)
  | 4 => (13565463 / 1000000000000 : ℝ)
  | 5 => (6775091 / 500000000000 : ℝ)
  | 6 => (541351 / 40000000000 : ℝ)
  | 7 => (13516231 / 1000000000000 : ℝ)
  | 8 => (6748769 / 500000000000 : ℝ)
  | 9 => (2695537 / 200000000000 : ℝ)
  | 10 => (13456659 / 1000000000000 : ℝ)
  | 11 => (13434449 / 1000000000000 : ℝ)
  | 12 => (13411043 / 1000000000000 : ℝ)
  | 13 => (1338643 / 100000000000 : ℝ)
  | 14 => (3340149 / 250000000000 : ℝ)
  | 15 => (13333531 / 1000000000000 : ℝ)
  | 16 => (13305223 / 1000000000000 : ℝ)
  | 17 => (6637829 / 500000000000 : ℝ)
  | 18 => (6622413 / 500000000000 : ℝ)
  | 19 => (6606357 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch037Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((740 : ℝ) + (j.val : ℝ)) / 1600)
      (((740 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch037Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch037Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((740 : ℝ) + (j.val : ℝ)) / 1600)
    (((740 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch037Neg25WeightLower j.val) (hpThetaShiftThreeBatch037Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch037Neg25WeightLower, hpThetaShiftThreeBatch037Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch037Neg25_integral_bounds :
    (3621231 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (1179087 / 40000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (740 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch037Lower hpThetaJensenCellsBatch037Upper
    hpThetaShiftThreeBatch037Neg25WeightLower hpThetaShiftThreeBatch037Neg25WeightUpper hpThetaJensenCellsBatch037_bounds hpThetaShiftThreeBatch037Neg25_weight_bounds
  have hl : (3621231 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch037Lower j * hpThetaShiftThreeBatch037Neg25WeightLower j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftThreeBatch037Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftThreeBatch037Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch037Lower j * hpThetaShiftThreeBatch037Neg25WeightUpper j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftThreeBatch037Neg25WeightUpper j) / 1600) ≤ (1179087 / 40000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftThreeBatch037Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (740 : ℝ) / 1600 = 37 / 80 by norm_num,
    show ((740 : ℝ) + 20) / 1600 = (37 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch037Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch037Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch037Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch037Neg25_integral_bounds
end HodgeProofHP
