/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch000

/-! Exact signed weight and batch integral certificates, batch 0 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch000Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (0 / 1 : ℝ)
  | 1 => (48827 / 250000000000 : ℝ)
  | 2 => (195297 / 250000000000 : ℝ)
  | 3 => (1757503 / 1000000000000 : ℝ)
  | 4 => (3124023 / 1000000000000 : ℝ)
  | 5 => (1220107 / 250000000000 : ℝ)
  | 6 => (3513153 / 500000000000 : ℝ)
  | 7 => (1912231 / 200000000000 : ℝ)
  | 8 => (6242189 / 500000000000 : ℝ)
  | 9 => (3948823 / 250000000000 : ℝ)
  | 10 => (19493117 / 1000000000000 : ℝ)
  | 11 => (23576987 / 1000000000000 : ℝ)
  | 12 => (14022971 / 500000000000 : ℝ)
  | 13 => (8224733 / 250000000000 : ℝ)
  | 14 => (1191713 / 31250000000 : ℝ)
  | 15 => (43752363 / 1000000000000 : ℝ)
  | 16 => (49750249 / 1000000000000 : ℝ)
  | 17 => (7015883 / 125000000000 : ℝ)
  | 18 => (12576261 / 200000000000 : ℝ)
  | 19 => (35005689 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch000Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (195309 / 1000000000000 : ℝ)
  | 1 => (781189 / 1000000000000 : ℝ)
  | 2 => (27461 / 15625000000 : ℝ)
  | 3 => (390503 / 125000000000 : ℝ)
  | 4 => (4880429 / 1000000000000 : ℝ)
  | 5 => (7026307 / 1000000000000 : ℝ)
  | 6 => (2390289 / 250000000000 : ℝ)
  | 7 => (12484379 / 1000000000000 : ℝ)
  | 8 => (15795293 / 1000000000000 : ℝ)
  | 9 => (9746559 / 500000000000 : ℝ)
  | 10 => (5894247 / 250000000000 : ℝ)
  | 11 => (28045943 / 1000000000000 : ℝ)
  | 12 => (32898933 / 1000000000000 : ℝ)
  | 13 => (38134817 / 1000000000000 : ℝ)
  | 14 => (10938091 / 250000000000 : ℝ)
  | 15 => (199001 / 4000000000 : ℝ)
  | 16 => (11225413 / 200000000000 : ℝ)
  | 17 => (31440653 / 500000000000 : ℝ)
  | 18 => (70011379 / 1000000000000 : ℝ)
  | 19 => (38757801 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch000Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((0 : ℝ) + (j.val : ℝ)) / 1600)
      (((0 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch000Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch000Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((0 : ℝ) + (j.val : ℝ)) / 1600)
    (((0 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch000Neg100WeightLower j.val) (hpThetaShiftOneBatch000Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch000Neg100WeightLower, hpThetaShiftOneBatch000Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch000Neg100_integral_bounds :
    (532797147 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (78170109 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (0 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch000Lower hpThetaJensenCellsBatch000Upper
    hpThetaShiftOneBatch000Neg100WeightLower hpThetaShiftOneBatch000Neg100WeightUpper hpThetaJensenCellsBatch000_bounds hpThetaShiftOneBatch000Neg100_weight_bounds
  have hl : (532797147 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch000Lower j * hpThetaShiftOneBatch000Neg100WeightLower j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftOneBatch000Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftOneBatch000Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch000Lower j * hpThetaShiftOneBatch000Neg100WeightUpper j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftOneBatch000Neg100WeightUpper j) / 1600) ≤ (78170109 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftOneBatch000Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (0 : ℝ) / 1600 = 0 / 80 by norm_num,
    show ((0 : ℝ) + 20) / 1600 = (0 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch000Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (0 / 1 : ℝ)
  | 1 => (19531 / 100000000000 : ℝ)
  | 2 => (78121 / 100000000000 : ℝ)
  | 3 => (1757611 / 1000000000000 : ℝ)
  | 4 => (624873 / 200000000000 : ℝ)
  | 5 => (2440631 / 500000000000 : ℝ)
  | 6 => (1757009 / 250000000000 : ℝ)
  | 7 => (9564359 / 1000000000000 : ℝ)
  | 8 => (2497969 / 200000000000 : ℝ)
  | 9 => (15804047 / 1000000000000 : ℝ)
  | 10 => (975323 / 50000000000 : ℝ)
  | 11 => (589913 / 25000000000 : ℝ)
  | 12 => (14036801 / 500000000000 : ℝ)
  | 13 => (514641 / 15625000000 : ℝ)
  | 14 => (19093021 / 500000000000 : ℝ)
  | 15 => (2738741 / 62500000000 : ℝ)
  | 16 => (9967521 / 200000000000 : ℝ)
  | 17 => (56238369 / 1000000000000 : ℝ)
  | 18 => (6302117 / 100000000000 : ℝ)
  | 19 => (7018497 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch000Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (195311 / 1000000000000 : ℝ)
  | 1 => (781211 / 1000000000000 : ℝ)
  | 2 => (439403 / 250000000000 : ℝ)
  | 3 => (1562183 / 500000000000 : ℝ)
  | 4 => (4881263 / 1000000000000 : ℝ)
  | 5 => (7028037 / 1000000000000 : ℝ)
  | 6 => (239109 / 25000000000 : ℝ)
  | 7 => (6244923 / 500000000000 : ℝ)
  | 8 => (987753 / 62500000000 : ℝ)
  | 9 => (19506461 / 1000000000000 : ℝ)
  | 10 => (23596521 / 1000000000000 : ℝ)
  | 11 => (28073603 / 1000000000000 : ℝ)
  | 12 => (1317481 / 40000000000 : ℝ)
  | 13 => (38186043 / 1000000000000 : ℝ)
  | 14 => (43819857 / 1000000000000 : ℝ)
  | 15 => (24918803 / 500000000000 : ℝ)
  | 16 => (5623837 / 100000000000 : ℝ)
  | 17 => (63021171 / 1000000000000 : ℝ)
  | 18 => (70184971 / 1000000000000 : ℝ)
  | 19 => (3109147 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch000Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((0 : ℝ) + (j.val : ℝ)) / 1600)
      (((0 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch000Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch000Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((0 : ℝ) + (j.val : ℝ)) / 1600)
    (((0 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch000Neg65WeightLower j.val) (hpThetaShiftOneBatch000Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch000Neg65WeightLower, hpThetaShiftOneBatch000Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch000Neg65_integral_bounds :
    (33351811 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (626440389 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (0 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch000Lower hpThetaJensenCellsBatch000Upper
    hpThetaShiftOneBatch000Neg65WeightLower hpThetaShiftOneBatch000Neg65WeightUpper hpThetaJensenCellsBatch000_bounds hpThetaShiftOneBatch000Neg65_weight_bounds
  have hl : (33351811 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch000Lower j * hpThetaShiftOneBatch000Neg65WeightLower j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftOneBatch000Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftOneBatch000Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch000Lower j * hpThetaShiftOneBatch000Neg65WeightUpper j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftOneBatch000Neg65WeightUpper j) / 1600) ≤ (626440389 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftOneBatch000Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (0 : ℝ) / 1600 = 0 / 80 by norm_num,
    show ((0 : ℝ) + 20) / 1600 = (0 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch000Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (0 / 1 : ℝ)
  | 1 => (19531 / 100000000000 : ℝ)
  | 2 => (31249 / 40000000000 : ℝ)
  | 3 => (219711 / 125000000000 : ℝ)
  | 4 => (3124609 / 1000000000000 : ℝ)
  | 5 => (2440929 / 500000000000 : ℝ)
  | 6 => (878659 / 125000000000 : ℝ)
  | 7 => (9566649 / 1000000000000 : ℝ)
  | 8 => (1999 / 160000000 : ℝ)
  | 9 => (7905151 / 500000000000 : ℝ)
  | 10 => (19515993 / 1000000000000 : ℝ)
  | 11 => (5902619 / 250000000000 : ℝ)
  | 12 => (14046683 / 500000000000 : ℝ)
  | 13 => (32964243 / 1000000000000 : ℝ)
  | 14 => (38222649 / 1000000000000 : ℝ)
  | 15 => (10967023 / 250000000000 : ℝ)
  | 16 => (49900039 / 1000000000000 : ℝ)
  | 17 => (56317927 / 1000000000000 : ℝ)
  | 18 => (1262423 / 20000000000 : ℝ)
  | 19 => (7030907 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch000Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (195311 / 1000000000000 : ℝ)
  | 1 => (390613 / 500000000000 : ℝ)
  | 2 => (1757689 / 1000000000000 : ℝ)
  | 3 => (312461 / 100000000000 : ℝ)
  | 4 => (4881859 / 1000000000000 : ℝ)
  | 5 => (7029273 / 1000000000000 : ℝ)
  | 6 => (191333 / 20000000000 : ℝ)
  | 7 => (12493751 / 1000000000000 : ℝ)
  | 8 => (15810303 / 1000000000000 : ℝ)
  | 9 => (9757997 / 500000000000 : ℝ)
  | 10 => (23610477 / 1000000000000 : ℝ)
  | 11 => (28093367 / 1000000000000 : ℝ)
  | 12 => (8241061 / 250000000000 : ℝ)
  | 13 => (764453 / 20000000000 : ℝ)
  | 14 => (43868093 / 1000000000000 : ℝ)
  | 15 => (1247501 / 25000000000 : ℝ)
  | 16 => (7039741 / 125000000000 : ℝ)
  | 17 => (63121151 / 1000000000000 : ℝ)
  | 18 => (70309071 / 1000000000000 : ℝ)
  | 19 => (19470253 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch000Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((0 : ℝ) + (j.val : ℝ)) / 1600)
      (((0 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch000Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch000Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((0 : ℝ) + (j.val : ℝ)) / 1600)
    (((0 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch000Neg40WeightLower j.val) (hpThetaShiftOneBatch000Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch000Neg40WeightLower, hpThetaShiftOneBatch000Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch000Neg40_integral_bounds :
    (267111759 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (125442403 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (0 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch000Lower hpThetaJensenCellsBatch000Upper
    hpThetaShiftOneBatch000Neg40WeightLower hpThetaShiftOneBatch000Neg40WeightUpper hpThetaJensenCellsBatch000_bounds hpThetaShiftOneBatch000Neg40_weight_bounds
  have hl : (267111759 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch000Lower j * hpThetaShiftOneBatch000Neg40WeightLower j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftOneBatch000Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftOneBatch000Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch000Lower j * hpThetaShiftOneBatch000Neg40WeightUpper j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftOneBatch000Neg40WeightUpper j) / 1600) ≤ (125442403 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftOneBatch000Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (0 : ℝ) / 1600 = 0 / 80 by norm_num,
    show ((0 : ℝ) + 20) / 1600 = (0 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch000Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (0 / 1 : ℝ)
  | 1 => (195311 / 1000000000000 : ℝ)
  | 2 => (781237 / 1000000000000 : ℝ)
  | 3 => (7031 / 4000000000 : ℝ)
  | 4 => (781201 / 250000000000 : ℝ)
  | 5 => (976467 / 200000000000 : ℝ)
  | 6 => (7030261 / 1000000000000 : ℝ)
  | 7 => (59803 / 6250000000 : ℝ)
  | 8 => (3999 / 320000000 : ℝ)
  | 9 => (15815307 / 1000000000000 : ℝ)
  | 10 => (19523621 / 1000000000000 : ℝ)
  | 11 => (23621643 / 1000000000000 : ℝ)
  | 12 => (28109181 / 1000000000000 : ℝ)
  | 13 => (1319441 / 40000000000 : ℝ)
  | 14 => (7650389 / 200000000000 : ℝ)
  | 15 => (8781339 / 200000000000 : ℝ)
  | 16 => (49950009 / 1000000000000 : ℝ)
  | 17 => (11276321 / 200000000000 : ℝ)
  | 18 => (63201179 / 1000000000000 : ℝ)
  | 19 => (70408413 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch000Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (12207 / 62500000000 : ℝ)
  | 1 => (390619 / 500000000000 : ℝ)
  | 2 => (1757751 / 1000000000000 : ℝ)
  | 3 => (624961 / 200000000000 : ℝ)
  | 4 => (152573 / 31250000000 : ℝ)
  | 5 => (3515131 / 500000000000 : ℝ)
  | 6 => (9568481 / 1000000000000 : ℝ)
  | 7 => (3124219 / 250000000000 : ℝ)
  | 8 => (3953827 / 250000000000 : ℝ)
  | 9 => (9761811 / 500000000000 : ℝ)
  | 10 => (5905411 / 250000000000 : ℝ)
  | 11 => (14054591 / 500000000000 : ℝ)
  | 12 => (16493013 / 500000000000 : ℝ)
  | 13 => (19125973 / 500000000000 : ℝ)
  | 14 => (5488337 / 125000000000 : ℝ)
  | 15 => (4995001 / 100000000000 : ℝ)
  | 16 => (28190803 / 500000000000 : ℝ)
  | 17 => (3160059 / 50000000000 : ℝ)
  | 18 => (35204207 / 500000000000 : ℝ)
  | 19 => (9750371 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch000Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((0 : ℝ) + (j.val : ℝ)) / 1600)
      (((0 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch000Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch000Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((0 : ℝ) + (j.val : ℝ)) / 1600)
    (((0 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch000Neg20WeightLower j.val) (hpThetaShiftOneBatch000Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch000Neg20WeightLower, hpThetaShiftOneBatch000Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch000Neg20_integral_bounds :
    (267349689 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (0 / 80 : ℝ) ((0 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (627829641 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (0 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch000Lower hpThetaJensenCellsBatch000Upper
    hpThetaShiftOneBatch000Neg20WeightLower hpThetaShiftOneBatch000Neg20WeightUpper hpThetaJensenCellsBatch000_bounds hpThetaShiftOneBatch000Neg20_weight_bounds
  have hl : (267349689 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch000Lower j * hpThetaShiftOneBatch000Neg20WeightLower j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftOneBatch000Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftOneBatch000Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch000Lower j * hpThetaShiftOneBatch000Neg20WeightUpper j)
        (hpThetaJensenCellsBatch000Upper j * hpThetaShiftOneBatch000Neg20WeightUpper j) / 1600) ≤ (627829641 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch000Lower, hpThetaJensenCellsBatch000Upper,
      hpThetaShiftOneBatch000Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (0 : ℝ) / 1600 = 0 / 80 by norm_num,
    show ((0 : ℝ) + 20) / 1600 = (0 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch000Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch000Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch000Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch000Neg20_integral_bounds
end HodgeProofHP
