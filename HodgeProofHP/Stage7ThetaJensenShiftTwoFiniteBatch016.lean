/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch016

/-! Exact signed weight and batch integral certificates, batch 16 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch016Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (307209 / 20000000000 : ℝ)
  | 1 => (3010041 / 200000000000 : ℝ)
  | 2 => (14730547 / 1000000000000 : ℝ)
  | 3 => (1800173 / 125000000000 : ℝ)
  | 4 => (14062623 / 1000000000000 : ℝ)
  | 5 => (13714173 / 1000000000000 : ℝ)
  | 6 => (1669493 / 125000000000 : ℝ)
  | 7 => (2597569 / 200000000000 : ℝ)
  | 8 => (12609787 / 1000000000000 : ℝ)
  | 9 => (12221681 / 1000000000000 : ℝ)
  | 10 => (147793 / 12500000000 : ℝ)
  | 11 => (178359 / 15625000000 : ℝ)
  | 12 => (2749051 / 250000000000 : ℝ)
  | 13 => (10567037 / 1000000000000 : ℝ)
  | 14 => (10127391 / 1000000000000 : ℝ)
  | 15 => (75603 / 7812500000 : ℝ)
  | 16 => (9216331 / 1000000000000 : ℝ)
  | 17 => (8744751 / 1000000000000 : ℝ)
  | 18 => (2065591 / 250000000000 : ℝ)
  | 19 => (776909 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch016Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (244709 / 15625000000 : ℝ)
  | 1 => (15360451 / 1000000000000 : ℝ)
  | 2 => (7525103 / 500000000000 : ℝ)
  | 3 => (3682637 / 250000000000 : ℝ)
  | 4 => (2880277 / 200000000000 : ℝ)
  | 5 => (439457 / 31250000000 : ℝ)
  | 6 => (6857087 / 500000000000 : ℝ)
  | 7 => (2671189 / 200000000000 : ℝ)
  | 8 => (6493923 / 500000000000 : ℝ)
  | 9 => (3152447 / 250000000000 : ℝ)
  | 10 => (6110841 / 500000000000 : ℝ)
  | 11 => (11823441 / 1000000000000 : ℝ)
  | 12 => (11414977 / 1000000000000 : ℝ)
  | 13 => (2199241 / 200000000000 : ℝ)
  | 14 => (5283519 / 500000000000 : ℝ)
  | 15 => (316481 / 31250000000 : ℝ)
  | 16 => (1935437 / 200000000000 : ℝ)
  | 17 => (2304083 / 250000000000 : ℝ)
  | 18 => (546547 / 62500000000 : ℝ)
  | 19 => (1652473 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch016Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((320 : ℝ) + (j.val : ℝ)) / 1600)
      (((320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch016Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch016Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((320 : ℝ) + (j.val : ℝ)) / 1600)
    (((320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch016Neg100WeightLower j.val) (hpThetaShiftTwoBatch016Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch016Neg100WeightLower, hpThetaShiftTwoBatch016Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch016Neg100_integral_bounds :
    (87786613 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (91784279 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch016Lower hpThetaJensenCellsBatch016Upper
    hpThetaShiftTwoBatch016Neg100WeightLower hpThetaShiftTwoBatch016Neg100WeightUpper hpThetaJensenCellsBatch016_bounds hpThetaShiftTwoBatch016Neg100_weight_bounds
  have hl : (87786613 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch016Lower j * hpThetaShiftTwoBatch016Neg100WeightLower j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftTwoBatch016Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftTwoBatch016Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch016Lower j * hpThetaShiftTwoBatch016Neg100WeightUpper j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftTwoBatch016Neg100WeightUpper j) / 1600) ≤ (91784279 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftTwoBatch016Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (320 : ℝ) / 1600 = 16 / 80 by norm_num,
    show ((320 : ℝ) + 20) / 1600 = (16 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch016Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (47717671 / 1000000000000 : ℝ)
  | 1 => (187053 / 3906250000 : ℝ)
  | 2 => (48048259 / 1000000000000 : ℝ)
  | 3 => (48205639 / 1000000000000 : ℝ)
  | 4 => (24178801 / 500000000000 : ℝ)
  | 5 => (24252019 / 500000000000 : ℝ)
  | 6 => (48644841 / 1000000000000 : ℝ)
  | 7 => (487799 / 10000000000 : ℝ)
  | 8 => (48909107 / 1000000000000 : ℝ)
  | 9 => (49032351 / 1000000000000 : ℝ)
  | 10 => (49149523 / 1000000000000 : ℝ)
  | 11 => (4926051 / 100000000000 : ℝ)
  | 12 => (24682601 / 500000000000 : ℝ)
  | 13 => (49463487 / 1000000000000 : ℝ)
  | 14 => (198221 / 4000000000 : ℝ)
  | 15 => (49640381 / 1000000000000 : ℝ)
  | 16 => (12429691 / 250000000000 : ℝ)
  | 17 => (9958057 / 200000000000 : ℝ)
  | 18 => (3115927 / 62500000000 : ℝ)
  | 19 => (49912287 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch016Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (47885569 / 1000000000000 : ℝ)
  | 1 => (2402413 / 50000000000 : ℝ)
  | 2 => (1205141 / 25000000000 : ℝ)
  | 3 => (48357603 / 1000000000000 : ℝ)
  | 4 => (48504039 / 1000000000000 : ℝ)
  | 5 => (24322421 / 500000000000 : ℝ)
  | 6 => (48779901 / 1000000000000 : ℝ)
  | 7 => (12227277 / 250000000000 : ℝ)
  | 8 => (1532261 / 31250000000 : ℝ)
  | 9 => (12287381 / 250000000000 : ℝ)
  | 10 => (49260511 / 1000000000000 : ℝ)
  | 11 => (49365203 / 1000000000000 : ℝ)
  | 12 => (772867 / 15625000000 : ℝ)
  | 13 => (49555251 / 1000000000000 : ℝ)
  | 14 => (24820191 / 500000000000 : ℝ)
  | 15 => (9943753 / 200000000000 : ℝ)
  | 16 => (24895143 / 500000000000 : ℝ)
  | 17 => (49854833 / 1000000000000 : ℝ)
  | 18 => (1559759 / 31250000000 : ℝ)
  | 19 => (49962537 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch016Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((320 : ℝ) + (j.val : ℝ)) / 1600)
      (((320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch016Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch016Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((320 : ℝ) + (j.val : ℝ)) / 1600)
    (((320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch016Neg65WeightLower j.val) (hpThetaShiftTwoBatch016Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch016Neg65WeightLower, hpThetaShiftTwoBatch016Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch016Neg65_integral_bounds :
    (180838829 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (91717523 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch016Lower hpThetaJensenCellsBatch016Upper
    hpThetaShiftTwoBatch016Neg65WeightLower hpThetaShiftTwoBatch016Neg65WeightUpper hpThetaJensenCellsBatch016_bounds hpThetaShiftTwoBatch016Neg65_weight_bounds
  have hl : (180838829 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch016Lower j * hpThetaShiftTwoBatch016Neg65WeightLower j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftTwoBatch016Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftTwoBatch016Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch016Lower j * hpThetaShiftTwoBatch016Neg65WeightUpper j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftTwoBatch016Neg65WeightUpper j) / 1600) ≤ (91717523 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftTwoBatch016Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (320 : ℝ) / 1600 = 16 / 80 by norm_num,
    show ((320 : ℝ) + 20) / 1600 = (16 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch016Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4392619 / 62500000000 : ℝ)
  | 1 => (14164001 / 200000000000 : ℝ)
  | 2 => (1427147 / 20000000000 : ℝ)
  | 3 => (3594693 / 50000000000 : ℝ)
  | 4 => (14485891 / 200000000000 : ℝ)
  | 5 => (36482027 / 500000000000 : ℝ)
  | 6 => (9187197 / 125000000000 : ℝ)
  | 7 => (37014969 / 500000000000 : ℝ)
  | 8 => (37280529 / 500000000000 : ℝ)
  | 9 => (1501817 / 20000000000 : ℝ)
  | 10 => (7561923 / 100000000000 : ℝ)
  | 11 => (1189783 / 15625000000 : ℝ)
  | 12 => (76671411 / 1000000000000 : ℝ)
  | 13 => (77195037 / 1000000000000 : ℝ)
  | 14 => (77716903 / 1000000000000 : ℝ)
  | 15 => (78236921 / 1000000000000 : ℝ)
  | 16 => (78754999 / 1000000000000 : ℝ)
  | 17 => (9908881 / 125000000000 : ℝ)
  | 18 => (4986561 / 62500000000 : ℝ)
  | 19 => (80296691 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch016Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (35410003 / 500000000000 : ℝ)
  | 1 => (71357351 / 1000000000000 : ℝ)
  | 2 => (71893861 / 1000000000000 : ℝ)
  | 3 => (4526841 / 62500000000 : ℝ)
  | 4 => (14592811 / 200000000000 : ℝ)
  | 5 => (73497577 / 1000000000000 : ℝ)
  | 6 => (74029939 / 1000000000000 : ℝ)
  | 7 => (74561059 / 1000000000000 : ℝ)
  | 8 => (75090851 / 1000000000000 : ℝ)
  | 9 => (75619231 / 1000000000000 : ℝ)
  | 10 => (76146113 / 1000000000000 : ℝ)
  | 11 => (19167853 / 250000000000 : ℝ)
  | 12 => (38597519 / 500000000000 : ℝ)
  | 13 => (9714613 / 125000000000 : ℝ)
  | 14 => (39118461 / 500000000000 : ℝ)
  | 15 => (15751 / 200000000 : ℝ)
  | 16 => (79271049 / 1000000000000 : ℝ)
  | 17 => (79784977 / 1000000000000 : ℝ)
  | 18 => (20074173 / 250000000000 : ℝ)
  | 19 => (808061 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch016Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((320 : ℝ) + (j.val : ℝ)) / 1600)
      (((320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch016Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch016Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((320 : ℝ) + (j.val : ℝ)) / 1600)
    (((320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch016Neg45WeightLower j.val) (hpThetaShiftTwoBatch016Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch016Neg45WeightLower, hpThetaShiftTwoBatch016Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch016Neg45_integral_bounds :
    (277964569 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (45323913 / 40000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch016Lower hpThetaJensenCellsBatch016Upper
    hpThetaShiftTwoBatch016Neg45WeightLower hpThetaShiftTwoBatch016Neg45WeightUpper hpThetaJensenCellsBatch016_bounds hpThetaShiftTwoBatch016Neg45_weight_bounds
  have hl : (277964569 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch016Lower j * hpThetaShiftTwoBatch016Neg45WeightLower j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftTwoBatch016Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftTwoBatch016Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch016Lower j * hpThetaShiftTwoBatch016Neg45WeightUpper j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftTwoBatch016Neg45WeightUpper j) / 1600) ≤ (45323913 / 40000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftTwoBatch016Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (320 : ℝ) / 1600 = 16 / 80 by norm_num,
    show ((320 : ℝ) + 20) / 1600 = (16 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch016Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (48068783 / 500000000000 : ℝ)
  | 1 => (19425343 / 200000000000 : ℝ)
  | 2 => (49060633 / 500000000000 : ℝ)
  | 3 => (24780299 / 250000000000 : ℝ)
  | 4 => (100126483 / 1000000000000 : ℝ)
  | 5 => (20227421 / 200000000000 : ℝ)
  | 6 => (102153037 / 1000000000000 : ℝ)
  | 7 => (6448391 / 62500000000 : ℝ)
  | 8 => (104200737 / 1000000000000 : ℝ)
  | 9 => (105232453 / 1000000000000 : ℝ)
  | 10 => (106269379 / 1000000000000 : ℝ)
  | 11 => (107311489 / 1000000000000 : ℝ)
  | 12 => (108358753 / 1000000000000 : ℝ)
  | 13 => (21882229 / 200000000000 : ℝ)
  | 14 => (22093727 / 200000000000 : ℝ)
  | 15 => (111531193 / 1000000000000 : ℝ)
  | 16 => (11259879 / 100000000000 : ℝ)
  | 17 => (22734279 / 200000000000 : ℝ)
  | 18 => (4589959 / 40000000000 : ℝ)
  | 19 => (115831499 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch016Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (24281679 / 250000000000 : ℝ)
  | 1 => (98121267 / 1000000000000 : ℝ)
  | 2 => (99121197 / 1000000000000 : ℝ)
  | 3 => (25031621 / 250000000000 : ℝ)
  | 4 => (50568553 / 500000000000 : ℝ)
  | 5 => (51076519 / 500000000000 : ℝ)
  | 6 => (103174257 / 1000000000000 : ℝ)
  | 7 => (52100369 / 500000000000 : ℝ)
  | 8 => (52616227 / 500000000000 : ℝ)
  | 9 => (5313469 / 50000000000 : ℝ)
  | 10 => (10731149 / 100000000000 : ℝ)
  | 11 => (54179377 / 500000000000 : ℝ)
  | 12 => (54705573 / 500000000000 : ℝ)
  | 13 => (27617159 / 250000000000 : ℝ)
  | 14 => (55765597 / 500000000000 : ℝ)
  | 15 => (112598791 / 1000000000000 : ℝ)
  | 16 => (28417849 / 250000000000 : ℝ)
  | 17 => (7171811 / 62500000000 : ℝ)
  | 18 => (231663 / 2000000000 : ℝ)
  | 19 => (58459467 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch016Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((320 : ℝ) + (j.val : ℝ)) / 1600)
      (((320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch016Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch016Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((320 : ℝ) + (j.val : ℝ)) / 1600)
    (((320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch016Neg25WeightLower j.val) (hpThetaShiftTwoBatch016Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch016Neg25WeightLower, hpThetaShiftTwoBatch016Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch016Neg25_integral_bounds :
    (62469651 / 40000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (399012373 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch016Lower hpThetaJensenCellsBatch016Upper
    hpThetaShiftTwoBatch016Neg25WeightLower hpThetaShiftTwoBatch016Neg25WeightUpper hpThetaJensenCellsBatch016_bounds hpThetaShiftTwoBatch016Neg25_weight_bounds
  have hl : (62469651 / 40000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch016Lower j * hpThetaShiftTwoBatch016Neg25WeightLower j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftTwoBatch016Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftTwoBatch016Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch016Lower j * hpThetaShiftTwoBatch016Neg25WeightUpper j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftTwoBatch016Neg25WeightUpper j) / 1600) ≤ (399012373 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftTwoBatch016Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (320 : ℝ) / 1600 = 16 / 80 by norm_num,
    show ((320 : ℝ) + 20) / 1600 = (16 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch016Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch016Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch016Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch016Neg25_integral_bounds
end HodgeProofHP
