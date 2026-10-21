/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch027

/-! Exact signed weight and batch integral certificates, batch 27 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch027Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-508637 / 250000000000 : ℝ)
  | 1 => (-206391 / 100000000000 : ℝ)
  | 2 => (-1046691 / 500000000000 : ℝ)
  | 3 => (-2122961 / 1000000000000 : ℝ)
  | 4 => (-2152641 / 1000000000000 : ℝ)
  | 5 => (-2182417 / 1000000000000 : ℝ)
  | 6 => (-2212283 / 1000000000000 : ℝ)
  | 7 => (-1121117 / 500000000000 : ℝ)
  | 8 => (-284033 / 125000000000 : ℝ)
  | 9 => (-2302367 / 1000000000000 : ℝ)
  | 10 => (-2332537 / 1000000000000 : ℝ)
  | 11 => (-147673 / 62500000000 : ℝ)
  | 12 => (-1196527 / 500000000000 : ℝ)
  | 13 => (-2423389 / 1000000000000 : ℝ)
  | 14 => (-490753 / 200000000000 : ℝ)
  | 15 => (-2484177 / 1000000000000 : ℝ)
  | 16 => (-2514617 / 1000000000000 : ℝ)
  | 17 => (-1272539 / 500000000000 : ℝ)
  | 18 => (-2575553 / 1000000000000 : ℝ)
  | 19 => (-651509 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch027Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2005301 / 1000000000000 : ℝ)
  | 1 => (-2034547 / 1000000000000 : ℝ)
  | 2 => (-2063909 / 1000000000000 : ℝ)
  | 3 => (-2093381 / 1000000000000 : ℝ)
  | 4 => (-26537 / 12500000000 : ℝ)
  | 5 => (-6727 / 3125000000 : ℝ)
  | 6 => (-136401 / 62500000000 : ℝ)
  | 7 => (-1106141 / 500000000000 : ℝ)
  | 8 => (-2242233 / 1000000000000 : ℝ)
  | 9 => (-2272263 / 1000000000000 : ℝ)
  | 10 => (-1151183 / 500000000000 : ℝ)
  | 11 => (-291567 / 125000000000 : ℝ)
  | 12 => (-2362767 / 1000000000000 : ℝ)
  | 13 => (-2393053 / 1000000000000 : ℝ)
  | 14 => (-605847 / 250000000000 : ℝ)
  | 15 => (-613441 / 250000000000 : ℝ)
  | 16 => (-155261 / 62500000000 : ℝ)
  | 17 => (-314327 / 125000000000 : ℝ)
  | 18 => (-2545077 / 1000000000000 : ℝ)
  | 19 => (-40243 / 15625000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch027Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((540 : ℝ) + (j.val : ℝ)) / 1600)
      (((540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch027Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch027Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((540 : ℝ) + (j.val : ℝ)) / 1600)
    (((540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch027Neg100WeightLower j.val) (hpThetaShiftThreeBatch027Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch027Neg100WeightLower, hpThetaShiftThreeBatch027Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch027Neg100_integral_bounds :
    (-198767 / 12500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-7741091 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch027Lower hpThetaJensenCellsBatch027Upper
    hpThetaShiftThreeBatch027Neg100WeightLower hpThetaShiftThreeBatch027Neg100WeightUpper hpThetaJensenCellsBatch027_bounds hpThetaShiftThreeBatch027Neg100_weight_bounds
  have hl : (-198767 / 12500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch027Lower j * hpThetaShiftThreeBatch027Neg100WeightLower j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftThreeBatch027Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftThreeBatch027Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch027Lower j * hpThetaShiftThreeBatch027Neg100WeightUpper j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftThreeBatch027Neg100WeightUpper j) / 1600) ≤ (-7741091 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftThreeBatch027Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (540 : ℝ) / 1600 = 27 / 80 by norm_num,
    show ((540 : ℝ) + 20) / 1600 = (27 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch027Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-139813 / 250000000000 : ℝ)
  | 1 => (-23487 / 40000000000 : ℝ)
  | 2 => (-615509 / 1000000000000 : ℝ)
  | 3 => (-644257 / 1000000000000 : ℝ)
  | 4 => (-673421 / 1000000000000 : ℝ)
  | 5 => (-175751 / 250000000000 : ℝ)
  | 6 => (-366503 / 500000000000 : ℝ)
  | 7 => (-763431 / 1000000000000 : ℝ)
  | 8 => (-794281 / 1000000000000 : ℝ)
  | 9 => (-206389 / 250000000000 : ℝ)
  | 10 => (-857261 / 1000000000000 : ℝ)
  | 11 => (-222349 / 250000000000 : ℝ)
  | 12 => (-921963 / 1000000000000 : ℝ)
  | 13 => (-238741 / 250000000000 : ℝ)
  | 14 => (-494201 / 500000000000 : ℝ)
  | 15 => (-1022277 / 1000000000000 : ℝ)
  | 16 => (-66037 / 62500000000 : ℝ)
  | 17 => (-272837 / 250000000000 : ℝ)
  | 18 => (-1126547 / 1000000000000 : ℝ)
  | 19 => (-116219 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch027Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-531737 / 1000000000000 : ℝ)
  | 1 => (-559251 / 1000000000000 : ℝ)
  | 2 => (-293587 / 500000000000 : ℝ)
  | 3 => (-153877 / 250000000000 : ℝ)
  | 4 => (-20133 / 31250000000 : ℝ)
  | 5 => (-33671 / 50000000000 : ℝ)
  | 6 => (-703003 / 1000000000000 : ℝ)
  | 7 => (-146601 / 200000000000 : ℝ)
  | 8 => (-76343 / 100000000000 : ℝ)
  | 9 => (-19857 / 25000000000 : ℝ)
  | 10 => (-165111 / 200000000000 : ℝ)
  | 11 => (-42863 / 50000000000 : ℝ)
  | 12 => (-177879 / 200000000000 : ℝ)
  | 13 => (-460981 / 500000000000 : ℝ)
  | 14 => (-954963 / 1000000000000 : ℝ)
  | 15 => (-988401 / 1000000000000 : ℝ)
  | 16 => (-255569 / 250000000000 : ℝ)
  | 17 => (-1056591 / 1000000000000 : ℝ)
  | 18 => (-1091347 / 1000000000000 : ℝ)
  | 19 => (-563273 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch027Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((540 : ℝ) + (j.val : ℝ)) / 1600)
      (((540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch027Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch027Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((540 : ℝ) + (j.val : ℝ)) / 1600)
    (((540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch027Neg70WeightLower j.val) (hpThetaShiftThreeBatch027Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch027Neg70WeightLower, hpThetaShiftThreeBatch027Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch027Neg70_integral_bounds :
    (-362351 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-1101141 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch027Lower hpThetaJensenCellsBatch027Upper
    hpThetaShiftThreeBatch027Neg70WeightLower hpThetaShiftThreeBatch027Neg70WeightUpper hpThetaJensenCellsBatch027_bounds hpThetaShiftThreeBatch027Neg70_weight_bounds
  have hl : (-362351 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch027Lower j * hpThetaShiftThreeBatch027Neg70WeightLower j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftThreeBatch027Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftThreeBatch027Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch027Lower j * hpThetaShiftThreeBatch027Neg70WeightUpper j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftThreeBatch027Neg70WeightUpper j) / 1600) ≤ (-1101141 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftThreeBatch027Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (540 : ℝ) / 1600 = 27 / 80 by norm_num,
    show ((540 : ℝ) + 20) / 1600 = (27 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch027Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (93653 / 40000000000 : ℝ)
  | 1 => (2342309 / 1000000000000 : ℝ)
  | 2 => (585753 / 250000000000 : ℝ)
  | 3 => (585857 / 250000000000 : ℝ)
  | 4 => (292923 / 125000000000 : ℝ)
  | 5 => (585729 / 250000000000 : ℝ)
  | 6 => (2342143 / 1000000000000 : ℝ)
  | 7 => (2341061 / 1000000000000 : ℝ)
  | 8 => (2339667 / 1000000000000 : ℝ)
  | 9 => (1168977 / 500000000000 : ℝ)
  | 10 => (2335919 / 1000000000000 : ℝ)
  | 11 => (2333557 / 1000000000000 : ℝ)
  | 12 => (145679 / 62500000000 : ℝ)
  | 13 => (2327833 / 1000000000000 : ℝ)
  | 14 => (1162231 / 500000000000 : ℝ)
  | 15 => (290093 / 125000000000 : ℝ)
  | 16 => (579169 / 250000000000 : ℝ)
  | 17 => (578063 / 250000000000 : ℝ)
  | 18 => (2307467 / 1000000000000 : ℝ)
  | 19 => (2302317 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch027Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (234231 / 100000000000 : ℝ)
  | 1 => (2343013 / 1000000000000 : ℝ)
  | 2 => (2343429 / 1000000000000 : ℝ)
  | 3 => (585889 / 250000000000 : ℝ)
  | 4 => (468711 / 200000000000 : ℝ)
  | 5 => (468677 / 200000000000 : ℝ)
  | 6 => (2342917 / 1000000000000 : ℝ)
  | 7 => (9149 / 3906250000 : ℝ)
  | 8 => (1170531 / 500000000000 : ℝ)
  | 9 => (584917 / 250000000000 : ℝ)
  | 10 => (467591 / 200000000000 : ℝ)
  | 11 => (29199 / 12500000000 : ℝ)
  | 12 => (1166779 / 500000000000 : ℝ)
  | 13 => (466173 / 200000000000 : ℝ)
  | 14 => (1163917 / 500000000000 : ℝ)
  | 15 => (2324463 / 1000000000000 : ℝ)
  | 16 => (464149 / 200000000000 : ℝ)
  | 17 => (2316677 / 1000000000000 : ℝ)
  | 18 => (2312253 / 1000000000000 : ℝ)
  | 19 => (576867 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch027Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((540 : ℝ) + (j.val : ℝ)) / 1600)
      (((540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch027Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch027Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((540 : ℝ) + (j.val : ℝ)) / 1600)
    (((540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch027Neg45WeightLower j.val) (hpThetaShiftThreeBatch027Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch027Neg45WeightLower, hpThetaShiftThreeBatch027Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch027Neg45_integral_bounds :
    (15807011 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (8019449 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch027Lower hpThetaJensenCellsBatch027Upper
    hpThetaShiftThreeBatch027Neg45WeightLower hpThetaShiftThreeBatch027Neg45WeightUpper hpThetaJensenCellsBatch027_bounds hpThetaShiftThreeBatch027Neg45_weight_bounds
  have hl : (15807011 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch027Lower j * hpThetaShiftThreeBatch027Neg45WeightLower j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftThreeBatch027Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftThreeBatch027Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch027Lower j * hpThetaShiftThreeBatch027Neg45WeightUpper j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftThreeBatch027Neg45WeightUpper j) / 1600) ≤ (8019449 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftThreeBatch027Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (540 : ℝ) / 1600 = 27 / 80 by norm_num,
    show ((540 : ℝ) + 20) / 1600 = (27 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch027Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (5938171 / 1000000000000 : ℝ)
  | 1 => (5984637 / 1000000000000 : ℝ)
  | 2 => (6031269 / 1000000000000 : ℝ)
  | 3 => (1215613 / 200000000000 : ℝ)
  | 4 => (6125023 / 1000000000000 : ℝ)
  | 5 => (3086071 / 500000000000 : ℝ)
  | 6 => (310971 / 50000000000 : ℝ)
  | 7 => (1253371 / 200000000000 : ℝ)
  | 8 => (3157223 / 500000000000 : ℝ)
  | 9 => (6362189 / 1000000000000 : ℝ)
  | 10 => (1602521 / 250000000000 : ℝ)
  | 11 => (403633 / 62500000000 : ℝ)
  | 12 => (81329 / 12500000000 : ℝ)
  | 13 => (6554657 / 1000000000000 : ℝ)
  | 14 => (3301569 / 500000000000 : ℝ)
  | 15 => (6651759 / 1000000000000 : ℝ)
  | 16 => (167513 / 25000000000 : ℝ)
  | 17 => (6749417 / 1000000000000 : ℝ)
  | 18 => (6798449 / 1000000000000 : ℝ)
  | 19 => (6847613 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch027Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2992319 / 500000000000 : ℝ)
  | 1 => (603127 / 100000000000 : ℝ)
  | 2 => (3039033 / 500000000000 : ℝ)
  | 3 => (191407 / 31250000000 : ℝ)
  | 4 => (6172143 / 1000000000000 : ℝ)
  | 5 => (6219421 / 1000000000000 : ℝ)
  | 6 => (783357 / 125000000000 : ℝ)
  | 7 => (6314447 / 1000000000000 : ℝ)
  | 8 => (636219 / 100000000000 : ℝ)
  | 9 => (1282017 / 200000000000 : ℝ)
  | 10 => (6458129 / 1000000000000 : ℝ)
  | 11 => (6506321 / 1000000000000 : ℝ)
  | 12 => (3277329 / 500000000000 : ℝ)
  | 13 => (6603139 / 1000000000000 : ℝ)
  | 14 => (83147 / 12500000000 : ℝ)
  | 15 => (6700521 / 1000000000000 : ℝ)
  | 16 => (3374709 / 500000000000 : ℝ)
  | 17 => (135969 / 20000000000 : ℝ)
  | 18 => (3423807 / 500000000000 : ℝ)
  | 19 => (6896909 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch027Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((540 : ℝ) + (j.val : ℝ)) / 1600)
      (((540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch027Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch027Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((540 : ℝ) + (j.val : ℝ)) / 1600)
    (((540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch027Neg25WeightLower j.val) (hpThetaShiftThreeBatch027Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch027Neg25WeightLower, hpThetaShiftThreeBatch027Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch027Neg25_integral_bounds :
    (21629209 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (44182269 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch027Lower hpThetaJensenCellsBatch027Upper
    hpThetaShiftThreeBatch027Neg25WeightLower hpThetaShiftThreeBatch027Neg25WeightUpper hpThetaJensenCellsBatch027_bounds hpThetaShiftThreeBatch027Neg25_weight_bounds
  have hl : (21629209 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch027Lower j * hpThetaShiftThreeBatch027Neg25WeightLower j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftThreeBatch027Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftThreeBatch027Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch027Lower j * hpThetaShiftThreeBatch027Neg25WeightUpper j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftThreeBatch027Neg25WeightUpper j) / 1600) ≤ (44182269 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftThreeBatch027Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (540 : ℝ) / 1600 = 27 / 80 by norm_num,
    show ((540 : ℝ) + 20) / 1600 = (27 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch027Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch027Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch027Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch027Neg25_integral_bounds
end HodgeProofHP
