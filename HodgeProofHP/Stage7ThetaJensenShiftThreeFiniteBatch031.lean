/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch031

/-! Exact signed weight and batch integral certificates, batch 31 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch031Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2038427 / 500000000000 : ℝ)
  | 1 => (-2043 / 500000000 : ℝ)
  | 2 => (-1023579 / 250000000000 : ℝ)
  | 3 => (-205089 / 50000000000 : ℝ)
  | 4 => (-2054187 / 500000000000 : ℝ)
  | 5 => (-164563 / 40000000000 : ℝ)
  | 6 => (-257429 / 62500000000 : ℝ)
  | 7 => (-2061359 / 500000000000 : ℝ)
  | 8 => (-2062809 / 500000000000 : ℝ)
  | 9 => (-206377 / 50000000000 : ℝ)
  | 10 => (-258029 / 62500000000 : ℝ)
  | 11 => (-4128561 / 1000000000000 : ℝ)
  | 12 => (-258023 / 62500000000 : ℝ)
  | 13 => (-1031807 / 250000000000 : ℝ)
  | 14 => (-4125023 / 1000000000000 : ℝ)
  | 15 => (-4121729 / 1000000000000 : ℝ)
  | 16 => (-1029331 / 250000000000 : ℝ)
  | 17 => (-513973 / 125000000000 : ℝ)
  | 18 => (-2052543 / 500000000000 : ℝ)
  | 19 => (-2048603 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch031Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4066897 / 1000000000000 : ℝ)
  | 1 => (-4076853 / 1000000000000 : ℝ)
  | 2 => (-4085999 / 1000000000000 : ℝ)
  | 3 => (-818863 / 200000000000 : ℝ)
  | 4 => (-4101779 / 1000000000000 : ℝ)
  | 5 => (-4108373 / 1000000000000 : ℝ)
  | 6 => (-2057037 / 500000000000 : ℝ)
  | 7 => (-4118863 / 1000000000000 : ℝ)
  | 8 => (-4122717 / 1000000000000 : ℝ)
  | 9 => (-4125617 / 1000000000000 : ℝ)
  | 10 => (-4127539 / 1000000000000 : ℝ)
  | 11 => (-4128367 / 1000000000000 : ℝ)
  | 12 => (-4127227 / 1000000000000 : ℝ)
  | 13 => (-2062511 / 500000000000 : ℝ)
  | 14 => (-32201 / 7812500000 : ℝ)
  | 15 => (-4117323 / 1000000000000 : ℝ)
  | 16 => (-4111783 / 1000000000000 : ℝ)
  | 17 => (-821017 / 200000000000 : ℝ)
  | 18 => (-819441 / 200000000000 : ℝ)
  | 19 => (-4088119 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch031Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((620 : ℝ) + (j.val : ℝ)) / 1600)
      (((620 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch031Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch031Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((620 : ℝ) + (j.val : ℝ)) / 1600)
    (((620 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch031Neg100WeightLower j.val) (hpThetaShiftThreeBatch031Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch031Neg100WeightLower, hpThetaShiftThreeBatch031Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch031Neg100_integral_bounds :
    (-1891033 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-4654083 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (620 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch031Lower hpThetaJensenCellsBatch031Upper
    hpThetaShiftThreeBatch031Neg100WeightLower hpThetaShiftThreeBatch031Neg100WeightUpper hpThetaJensenCellsBatch031_bounds hpThetaShiftThreeBatch031Neg100_weight_bounds
  have hl : (-1891033 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch031Lower j * hpThetaShiftThreeBatch031Neg100WeightLower j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftThreeBatch031Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftThreeBatch031Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch031Lower j * hpThetaShiftThreeBatch031Neg100WeightUpper j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftThreeBatch031Neg100WeightUpper j) / 1600) ≤ (-4654083 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftThreeBatch031Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (620 : ℝ) / 1600 = 31 / 80 by norm_num,
    show ((620 : ℝ) + 20) / 1600 = (31 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch031Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-419811 / 100000000000 : ℝ)
  | 1 => (-2130747 / 500000000000 : ℝ)
  | 2 => (-2162633 / 500000000000 : ℝ)
  | 3 => (-2194711 / 500000000000 : ℝ)
  | 4 => (-4453959 / 1000000000000 : ℝ)
  | 5 => (-451887 / 100000000000 : ℝ)
  | 6 => (-573019 / 125000000000 : ℝ)
  | 7 => (-23249 / 5000000000 : ℝ)
  | 8 => (-147369 / 31250000000 : ℝ)
  | 9 => (-1195543 / 250000000000 : ℝ)
  | 10 => (-2424443 / 500000000000 : ℝ)
  | 11 => (-4915943 / 1000000000000 : ℝ)
  | 12 => (-249167 / 50000000000 : ℝ)
  | 13 => (-505107 / 100000000000 : ℝ)
  | 14 => (-2559563 / 500000000000 : ℝ)
  | 15 => (-324219 / 62500000000 : ℝ)
  | 16 => (-1314049 / 250000000000 : ℝ)
  | 17 => (-1065039 / 200000000000 : ℝ)
  | 18 => (-84289 / 15625000000 : ℝ)
  | 19 => (-1366023 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch031Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4135119 / 1000000000000 : ℝ)
  | 1 => (-4198109 / 1000000000000 : ℝ)
  | 2 => (-4261493 / 1000000000000 : ℝ)
  | 3 => (-865053 / 200000000000 : ℝ)
  | 4 => (-4389421 / 1000000000000 : ℝ)
  | 5 => (-2226979 / 500000000000 : ℝ)
  | 6 => (-4518869 / 1000000000000 : ℝ)
  | 7 => (-4584151 / 1000000000000 : ℝ)
  | 8 => (-4649799 / 1000000000000 : ℝ)
  | 9 => (-4715807 / 1000000000000 : ℝ)
  | 10 => (-4782171 / 1000000000000 : ℝ)
  | 11 => (-969777 / 200000000000 : ℝ)
  | 12 => (-2457971 / 500000000000 : ℝ)
  | 13 => (-4983339 / 1000000000000 : ℝ)
  | 14 => (-5051069 / 1000000000000 : ℝ)
  | 15 => (-40953 / 8000000000 : ℝ)
  | 16 => (-5187503 / 1000000000000 : ℝ)
  | 17 => (-1051239 / 200000000000 : ℝ)
  | 18 => (-2662597 / 500000000000 : ℝ)
  | 19 => (-1078899 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch031Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((620 : ℝ) + (j.val : ℝ)) / 1600)
      (((620 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch031Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch031Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((620 : ℝ) + (j.val : ℝ)) / 1600)
    (((620 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch031Neg70WeightLower j.val) (hpThetaShiftThreeBatch031Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch031Neg70WeightLower, hpThetaShiftThreeBatch031Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch031Neg70_integral_bounds :
    (-22110221 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-21492691 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (620 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch031Lower hpThetaJensenCellsBatch031Upper
    hpThetaShiftThreeBatch031Neg70WeightLower hpThetaShiftThreeBatch031Neg70WeightUpper hpThetaJensenCellsBatch031_bounds hpThetaShiftThreeBatch031Neg70_weight_bounds
  have hl : (-22110221 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch031Lower j * hpThetaShiftThreeBatch031Neg70WeightLower j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftThreeBatch031Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftThreeBatch031Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch031Lower j * hpThetaShiftThreeBatch031Neg70WeightUpper j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftThreeBatch031Neg70WeightUpper j) / 1600) ≤ (-21492691 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftThreeBatch031Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (620 : ℝ) / 1600 = 31 / 80 by norm_num,
    show ((620 : ℝ) + 20) / 1600 = (31 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch031Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1089879 / 1000000000000 : ℝ)
  | 1 => (1051701 / 1000000000000 : ℝ)
  | 2 => (1012813 / 1000000000000 : ℝ)
  | 3 => (97321 / 100000000000 : ℝ)
  | 4 => (186577 / 200000000000 : ℝ)
  | 5 => (445917 / 500000000000 : ℝ)
  | 6 => (850051 / 1000000000000 : ℝ)
  | 7 => (807529 / 1000000000000 : ℝ)
  | 8 => (764263 / 1000000000000 : ℝ)
  | 9 => (720247 / 1000000000000 : ℝ)
  | 10 => (168869 / 250000000000 : ℝ)
  | 11 => (78743 / 125000000000 : ℝ)
  | 12 => (116729 / 200000000000 : ℝ)
  | 13 => (536573 / 1000000000000 : ℝ)
  | 14 => (488723 / 1000000000000 : ℝ)
  | 15 => (440089 / 1000000000000 : ℝ)
  | 16 => (195333 / 500000000000 : ℝ)
  | 17 => (10639 / 31250000000 : ℝ)
  | 18 => (289429 / 1000000000000 : ℝ)
  | 19 => (237603 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch031Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (225471 / 200000000000 : ℝ)
  | 1 => (27247 / 25000000000 : ℝ)
  | 2 => (525851 / 500000000000 : ℝ)
  | 3 => (506407 / 500000000000 : ℝ)
  | 4 => (973211 / 1000000000000 : ℝ)
  | 5 => (466443 / 500000000000 : ℝ)
  | 6 => (178367 / 200000000000 : ℝ)
  | 7 => (212513 / 250000000000 : ℝ)
  | 8 => (80753 / 100000000000 : ℝ)
  | 9 => (95533 / 125000000000 : ℝ)
  | 10 => (90031 / 125000000000 : ℝ)
  | 11 => (675477 / 1000000000000 : ℝ)
  | 12 => (125989 / 200000000000 : ℝ)
  | 13 => (291823 / 500000000000 : ℝ)
  | 14 => (268287 / 500000000000 : ℝ)
  | 15 => (122181 / 250000000000 : ℝ)
  | 16 => (44009 / 100000000000 : ℝ)
  | 17 => (390667 / 1000000000000 : ℝ)
  | 18 => (340449 / 1000000000000 : ℝ)
  | 19 => (28943 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch031Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((620 : ℝ) + (j.val : ℝ)) / 1600)
      (((620 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch031Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch031Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((620 : ℝ) + (j.val : ℝ)) / 1600)
    (((620 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch031Neg45WeightLower j.val) (hpThetaShiftThreeBatch031Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch031Neg45WeightLower, hpThetaShiftThreeBatch031Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch031Neg45_integral_bounds :
    (3142781 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (3392273 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (620 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch031Lower hpThetaJensenCellsBatch031Upper
    hpThetaShiftThreeBatch031Neg45WeightLower hpThetaShiftThreeBatch031Neg45WeightUpper hpThetaJensenCellsBatch031_bounds hpThetaShiftThreeBatch031Neg45_weight_bounds
  have hl : (3142781 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch031Lower j * hpThetaShiftThreeBatch031Neg45WeightLower j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftThreeBatch031Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftThreeBatch031Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch031Lower j * hpThetaShiftThreeBatch031Neg45WeightUpper j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftThreeBatch031Neg45WeightUpper j) / 1600) ≤ (3392273 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftThreeBatch031Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (620 : ℝ) / 1600 = 31 / 80 by norm_num,
    show ((620 : ℝ) + 20) / 1600 = (31 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch031Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (9982019 / 1000000000000 : ℝ)
  | 1 => (627081 / 62500000000 : ℝ)
  | 2 => (10084479 / 1000000000000 : ℝ)
  | 3 => (10135563 / 1000000000000 : ℝ)
  | 4 => (10186543 / 1000000000000 : ℝ)
  | 5 => (5118707 / 500000000000 : ℝ)
  | 6 => (10288171 / 1000000000000 : ℝ)
  | 7 => (10338809 / 1000000000000 : ℝ)
  | 8 => (10389321 / 1000000000000 : ℝ)
  | 9 => (1304963 / 125000000000 : ℝ)
  | 10 => (10489951 / 1000000000000 : ℝ)
  | 11 => (10540057 / 1000000000000 : ℝ)
  | 12 => (10590017 / 1000000000000 : ℝ)
  | 13 => (425593 / 40000000000 : ℝ)
  | 14 => (5344737 / 500000000000 : ℝ)
  | 15 => (10738961 / 1000000000000 : ℝ)
  | 16 => (5394139 / 500000000000 : ℝ)
  | 17 => (10837421 / 1000000000000 : ℝ)
  | 18 => (10886383 / 1000000000000 : ℝ)
  | 19 => (10935159 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch031Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (10033297 / 1000000000000 : ℝ)
  | 1 => (15757 / 1562500000 : ℝ)
  | 2 => (2533891 / 250000000000 : ℝ)
  | 3 => (636659 / 62500000000 : ℝ)
  | 4 => (2047483 / 200000000000 : ℝ)
  | 5 => (2572043 / 250000000000 : ℝ)
  | 6 => (1033881 / 100000000000 : ℝ)
  | 7 => (5194661 / 500000000000 : ℝ)
  | 8 => (2087941 / 200000000000 : ℝ)
  | 9 => (327811 / 31250000000 : ℝ)
  | 10 => (5270029 / 500000000000 : ℝ)
  | 11 => (5295009 / 500000000000 : ℝ)
  | 12 => (5319913 / 500000000000 : ℝ)
  | 13 => (427579 / 40000000000 : ℝ)
  | 14 => (5369481 / 500000000000 : ℝ)
  | 15 => (10788279 / 1000000000000 : ℝ)
  | 16 => (5418711 / 500000000000 : ℝ)
  | 17 => (680399 / 62500000000 : ℝ)
  | 18 => (273379 / 25000000000 : ℝ)
  | 19 => (10983743 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch031Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((620 : ℝ) + (j.val : ℝ)) / 1600)
      (((620 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch031Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch031Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((620 : ℝ) + (j.val : ℝ)) / 1600)
    (((620 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch031Neg25WeightLower j.val) (hpThetaShiftThreeBatch031Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch031Neg25WeightLower, hpThetaShiftThreeBatch031Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch031Neg25_integral_bounds :
    (47371873 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (48290491 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (620 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch031Lower hpThetaJensenCellsBatch031Upper
    hpThetaShiftThreeBatch031Neg25WeightLower hpThetaShiftThreeBatch031Neg25WeightUpper hpThetaJensenCellsBatch031_bounds hpThetaShiftThreeBatch031Neg25_weight_bounds
  have hl : (47371873 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch031Lower j * hpThetaShiftThreeBatch031Neg25WeightLower j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftThreeBatch031Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftThreeBatch031Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch031Lower j * hpThetaShiftThreeBatch031Neg25WeightUpper j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftThreeBatch031Neg25WeightUpper j) / 1600) ≤ (48290491 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftThreeBatch031Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (620 : ℝ) / 1600 = 31 / 80 by norm_num,
    show ((620 : ℝ) + 20) / 1600 = (31 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch031Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch031Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch031Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch031Neg25_integral_bounds
end HodgeProofHP
