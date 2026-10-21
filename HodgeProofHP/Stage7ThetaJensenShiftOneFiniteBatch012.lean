/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch012

/-! Exact signed weight and batch integral certificates, batch 12 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch012Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (61865813 / 50000000000 : ℝ)
  | 1 => (23697343 / 20000000000 : ℝ)
  | 2 => (282876289 / 250000000000 : ℝ)
  | 3 => (1077229673 / 1000000000000 : ℝ)
  | 4 => (255510059 / 250000000000 : ℝ)
  | 5 => (965936529 / 1000000000000 : ℝ)
  | 6 => (454459191 / 500000000000 : ℝ)
  | 7 => (85098577 / 100000000000 : ℝ)
  | 8 => (792138821 / 1000000000000 : ℝ)
  | 9 => (73237781 / 100000000000 : ℝ)
  | 10 => (335851583 / 500000000000 : ℝ)
  | 11 => (610115469 / 1000000000000 : ℝ)
  | 12 => (109523091 / 200000000000 : ℝ)
  | 13 => (121051003 / 250000000000 : ℝ)
  | 14 => (419882187 / 1000000000000 : ℝ)
  | 15 => (22165699 / 62500000000 : ℝ)
  | 16 => (288512367 / 1000000000000 : ℝ)
  | 17 => (221467257 / 1000000000000 : ℝ)
  | 18 => (153517539 / 1000000000000 : ℝ)
  | 19 => (84665059 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch012Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1288853237 / 1000000000000 : ℝ)
  | 1 => (1237316261 / 1000000000000 : ℝ)
  | 2 => (1184867151 / 1000000000000 : ℝ)
  | 3 => (1131505157 / 1000000000000 : ℝ)
  | 4 => (538614837 / 500000000000 : ℝ)
  | 5 => (1022040237 / 1000000000000 : ℝ)
  | 6 => (96593653 / 100000000000 : ℝ)
  | 7 => (908918383 / 1000000000000 : ℝ)
  | 8 => (850985771 / 1000000000000 : ℝ)
  | 9 => (396069411 / 500000000000 : ℝ)
  | 10 => (732377811 / 1000000000000 : ℝ)
  | 11 => (671703167 / 1000000000000 : ℝ)
  | 12 => (61011547 / 100000000000 : ℝ)
  | 13 => (17112983 / 31250000000 : ℝ)
  | 14 => (484204013 / 1000000000000 : ℝ)
  | 15 => (104970547 / 250000000000 : ℝ)
  | 16 => (70930237 / 200000000000 : ℝ)
  | 17 => (18032023 / 62500000000 : ℝ)
  | 18 => (110733629 / 500000000000 : ℝ)
  | 19 => (7675877 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch012Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((240 : ℝ) + (j.val : ℝ)) / 1600)
      (((240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch012Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch012Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((240 : ℝ) + (j.val : ℝ)) / 1600)
    (((240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch012Neg100WeightLower j.val) (hpThetaShiftOneBatch012Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch012Neg100WeightLower, hpThetaShiftOneBatch012Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch012Neg100_integral_bounds :
    (12176964731 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (1673749489 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch012Lower hpThetaJensenCellsBatch012Upper
    hpThetaShiftOneBatch012Neg100WeightLower hpThetaShiftOneBatch012Neg100WeightUpper hpThetaJensenCellsBatch012_bounds hpThetaShiftOneBatch012Neg100_weight_bounds
  have hl : (12176964731 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch012Lower j * hpThetaShiftOneBatch012Neg100WeightLower j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftOneBatch012Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftOneBatch012Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch012Lower j * hpThetaShiftOneBatch012Neg100WeightUpper j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftOneBatch012Neg100WeightUpper j) / 1600) ≤ (1673749489 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftOneBatch012Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (240 : ℝ) / 1600 = 12 / 80 by norm_num,
    show ((240 : ℝ) + 20) / 1600 = (12 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch012Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (833926083 / 200000000000 : ℝ)
  | 1 => (4153841267 / 1000000000000 : ℝ)
  | 2 => (4137305171 / 1000000000000 : ℝ)
  | 3 => (1030004349 / 250000000000 : ℝ)
  | 4 => (820394653 / 200000000000 : ℝ)
  | 5 => (4083168153 / 1000000000000 : ℝ)
  | 6 => (253974843 / 62500000000 : ℝ)
  | 7 => (4043256753 / 1000000000000 : ℝ)
  | 8 => (4022141487 / 1000000000000 : ℝ)
  | 9 => (2000123641 / 500000000000 : ℝ)
  | 10 => (994392447 / 250000000000 : ℝ)
  | 11 => (1977052357 / 500000000000 : ℝ)
  | 12 => (1964923911 / 500000000000 : ℝ)
  | 13 => (3904794939 / 1000000000000 : ℝ)
  | 14 => (775788389 / 200000000000 : ℝ)
  | 15 => (770456957 / 200000000000 : ℝ)
  | 16 => (1912409731 / 500000000000 : ℝ)
  | 17 => (3796542043 / 1000000000000 : ℝ)
  | 18 => (1883724327 / 500000000000 : ℝ)
  | 19 => (1868767743 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch012Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (836935479 / 200000000000 : ℝ)
  | 1 => (260601901 / 62500000000 : ℝ)
  | 2 => (1038460317 / 250000000000 : ℝ)
  | 3 => (1034326293 / 250000000000 : ℝ)
  | 4 => (4120017397 / 1000000000000 : ℝ)
  | 5 => (2050986633 / 500000000000 : ℝ)
  | 6 => (2041584077 / 500000000000 : ℝ)
  | 7 => (4063597489 / 1000000000000 : ℝ)
  | 8 => (2021628377 / 500000000000 : ℝ)
  | 9 => (251383843 / 62500000000 : ℝ)
  | 10 => (4000247283 / 1000000000000 : ℝ)
  | 11 => (3977569789 / 1000000000000 : ℝ)
  | 12 => (790820943 / 200000000000 : ℝ)
  | 13 => (3929847823 / 1000000000000 : ℝ)
  | 14 => (195239747 / 50000000000 : ℝ)
  | 15 => (1939470973 / 500000000000 : ℝ)
  | 16 => (1926142393 / 500000000000 : ℝ)
  | 17 => (3824819463 / 1000000000000 : ℝ)
  | 18 => (949135511 / 250000000000 : ℝ)
  | 19 => (753489731 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch012Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((240 : ℝ) + (j.val : ℝ)) / 1600)
      (((240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch012Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch012Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((240 : ℝ) + (j.val : ℝ)) / 1600)
    (((240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch012Neg65WeightLower j.val) (hpThetaShiftOneBatch012Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch012Neg65WeightLower, hpThetaShiftOneBatch012Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch012Neg65_integral_bounds :
    (273873961 / 3906250000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (71319191379 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch012Lower hpThetaJensenCellsBatch012Upper
    hpThetaShiftOneBatch012Neg65WeightLower hpThetaShiftOneBatch012Neg65WeightUpper hpThetaJensenCellsBatch012_bounds hpThetaShiftOneBatch012Neg65_weight_bounds
  have hl : (273873961 / 3906250000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch012Lower j * hpThetaShiftOneBatch012Neg65WeightLower j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftOneBatch012Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftOneBatch012Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch012Lower j * hpThetaShiftOneBatch012Neg65WeightUpper j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftOneBatch012Neg65WeightUpper j) / 1600) ≤ (71319191379 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftOneBatch012Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (240 : ℝ) / 1600 = 12 / 80 by norm_num,
    show ((240 : ℝ) + 20) / 1600 = (12 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch012Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (6633361607 / 1000000000000 : ℝ)
  | 1 => (1330716563 / 200000000000 : ℝ)
  | 2 => (6673362707 / 1000000000000 : ℝ)
  | 3 => (209146757 / 31250000000 : ℝ)
  | 4 => (3355789157 / 500000000000 : ℝ)
  | 5 => (210312623 / 31250000000 : ℝ)
  | 6 => (3373984029 / 500000000000 : ℝ)
  | 7 => (6765465657 / 1000000000000 : ℝ)
  | 8 => (6782491719 / 1000000000000 : ℝ)
  | 9 => (3399520621 / 500000000000 : ℝ)
  | 10 => (3407554617 / 500000000000 : ℝ)
  | 11 => (853836339 / 125000000000 : ℝ)
  | 12 => (6845780707 / 1000000000000 : ℝ)
  | 13 => (343018713 / 50000000000 : ℝ)
  | 14 => (859308303 / 125000000000 : ℝ)
  | 15 => (1377610453 / 200000000000 : ℝ)
  | 16 => (6901126859 / 1000000000000 : ℝ)
  | 17 => (6913685299 / 1000000000000 : ℝ)
  | 18 => (108214417 / 15625000000 : ℝ)
  | 19 => (216788567 / 31250000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch012Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (207924463 / 31250000000 : ℝ)
  | 1 => (1668340677 / 250000000000 : ℝ)
  | 2 => (267707849 / 40000000000 : ℝ)
  | 3 => (1342315663 / 200000000000 : ℝ)
  | 4 => (6730003937 / 1000000000000 : ℝ)
  | 5 => (6747968059 / 1000000000000 : ℝ)
  | 6 => (3382732829 / 500000000000 : ℝ)
  | 7 => (169562293 / 25000000000 : ℝ)
  | 8 => (6799041243 / 1000000000000 : ℝ)
  | 9 => (1363021847 / 200000000000 : ℝ)
  | 10 => (6830690713 / 1000000000000 : ℝ)
  | 11 => (1711445177 / 250000000000 : ℝ)
  | 12 => (6860374261 / 1000000000000 : ℝ)
  | 13 => (274978657 / 40000000000 : ℝ)
  | 14 => (3444026133 / 500000000000 : ℝ)
  | 15 => (345056343 / 50000000000 : ℝ)
  | 16 => (69136853 / 10000000000 : ℝ)
  | 17 => (6925722689 / 1000000000000 : ℝ)
  | 18 => (1387446829 / 200000000000 : ℝ)
  | 19 => (3474107399 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch012Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((240 : ℝ) + (j.val : ℝ)) / 1600)
      (((240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch012Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch012Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((240 : ℝ) + (j.val : ℝ)) / 1600)
    (((240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch012Neg40WeightLower j.val) (hpThetaShiftOneBatch012Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch012Neg40WeightLower, hpThetaShiftOneBatch012Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch012Neg40_integral_bounds :
    (59917035589 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (60749694489 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch012Lower hpThetaJensenCellsBatch012Upper
    hpThetaShiftOneBatch012Neg40WeightLower hpThetaShiftOneBatch012Neg40WeightUpper hpThetaJensenCellsBatch012_bounds hpThetaShiftOneBatch012Neg40_weight_bounds
  have hl : (59917035589 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch012Lower j * hpThetaShiftOneBatch012Neg40WeightLower j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftOneBatch012Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftOneBatch012Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch012Lower j * hpThetaShiftOneBatch012Neg40WeightUpper j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftOneBatch012Neg40WeightUpper j) / 1600) ≤ (60749694489 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftOneBatch012Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (240 : ℝ) / 1600 = 12 / 80 by norm_num,
    show ((240 : ℝ) + 20) / 1600 = (12 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch012Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (353257433 / 40000000000 : ℝ)
  | 1 => (4442882719 / 500000000000 : ℝ)
  | 2 => (8940013033 / 1000000000000 : ℝ)
  | 3 => (2248543791 / 250000000000 : ℝ)
  | 4 => (9048248381 / 1000000000000 : ℝ)
  | 5 => (1137778653 / 125000000000 : ℝ)
  | 6 => (915611423 / 100000000000 : ℝ)
  | 7 => (920989993 / 100000000000 : ℝ)
  | 8 => (4631791423 / 500000000000 : ℝ)
  | 9 => (9317159497 / 1000000000000 : ℝ)
  | 10 => (1874125279 / 200000000000 : ℝ)
  | 11 => (4711990023 / 500000000000 : ℝ)
  | 12 => (9477216951 / 1000000000000 : ℝ)
  | 13 => (4765166803 / 500000000000 : ℝ)
  | 14 => (9583326499 / 1000000000000 : ℝ)
  | 15 => (9636192117 / 1000000000000 : ℝ)
  | 16 => (9688926937 / 1000000000000 : ℝ)
  | 17 => (4870763717 / 500000000000 : ℝ)
  | 18 => (9793990077 / 1000000000000 : ℝ)
  | 19 => (9846311331 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch012Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (8885765439 / 1000000000000 : ℝ)
  | 1 => (4470006517 / 500000000000 : ℝ)
  | 2 => (1798835033 / 200000000000 : ℝ)
  | 3 => (4524124191 / 500000000000 : ℝ)
  | 4 => (364089169 / 40000000000 : ℝ)
  | 5 => (9156114231 / 1000000000000 : ℝ)
  | 6 => (9209899931 / 1000000000000 : ℝ)
  | 7 => (9263582847 / 1000000000000 : ℝ)
  | 8 => (4658579749 / 500000000000 : ℝ)
  | 9 => (2342656599 / 250000000000 : ℝ)
  | 10 => (9423980047 / 1000000000000 : ℝ)
  | 11 => (1184652119 / 125000000000 : ℝ)
  | 12 => (9530333607 / 1000000000000 : ℝ)
  | 13 => (19166653 / 2000000000 : ℝ)
  | 14 => (4818096059 / 500000000000 : ℝ)
  | 15 => (4844463469 / 500000000000 : ℝ)
  | 16 => (1948305487 / 200000000000 : ℝ)
  | 17 => (4896995039 / 500000000000 : ℝ)
  | 18 => (2461577833 / 250000000000 : ℝ)
  | 19 => (4949243827 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch012Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((240 : ℝ) + (j.val : ℝ)) / 1600)
      (((240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch012Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch012Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((240 : ℝ) + (j.val : ℝ)) / 1600)
    (((240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch012Neg20WeightLower j.val) (hpThetaShiftOneBatch012Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch012Neg20WeightLower, hpThetaShiftOneBatch012Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch012Neg20_integral_bounds :
    (164619083149 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (12 / 80 : ℝ) ((12 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (83735988083 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch012Lower hpThetaJensenCellsBatch012Upper
    hpThetaShiftOneBatch012Neg20WeightLower hpThetaShiftOneBatch012Neg20WeightUpper hpThetaJensenCellsBatch012_bounds hpThetaShiftOneBatch012Neg20_weight_bounds
  have hl : (164619083149 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch012Lower j * hpThetaShiftOneBatch012Neg20WeightLower j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftOneBatch012Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftOneBatch012Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch012Lower j * hpThetaShiftOneBatch012Neg20WeightUpper j)
        (hpThetaJensenCellsBatch012Upper j * hpThetaShiftOneBatch012Neg20WeightUpper j) / 1600) ≤ (83735988083 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch012Lower, hpThetaJensenCellsBatch012Upper,
      hpThetaShiftOneBatch012Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (240 : ℝ) / 1600 = 12 / 80 by norm_num,
    show ((240 : ℝ) + 20) / 1600 = (12 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch012Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch012Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch012Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch012Neg20_integral_bounds
end HodgeProofHP
