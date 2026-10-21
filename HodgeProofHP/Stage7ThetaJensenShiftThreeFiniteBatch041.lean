/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch041

/-! Exact signed weight and batch integral certificates, batch 41 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch041Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (23866523 / 500000000000 : ℝ)
  | 1 => (48450233 / 1000000000000 : ℝ)
  | 2 => (24586217 / 500000000000 : ℝ)
  | 3 => (24949799 / 500000000000 : ℝ)
  | 4 => (6328959 / 125000000000 : ℝ)
  | 5 => (51368601 / 1000000000000 : ℝ)
  | 6 => (52110327 / 1000000000000 : ℝ)
  | 7 => (6607099 / 125000000000 : ℝ)
  | 8 => (53607931 / 1000000000000 : ℝ)
  | 9 => (27181841 / 500000000000 : ℝ)
  | 10 => (55123977 / 1000000000000 : ℝ)
  | 11 => (11177749 / 200000000000 : ℝ)
  | 12 => (11331583 / 200000000000 : ℝ)
  | 13 => (57431411 / 1000000000000 : ℝ)
  | 14 => (14552289 / 250000000000 : ℝ)
  | 15 => (58991069 / 1000000000000 : ℝ)
  | 16 => (59777067 / 1000000000000 : ℝ)
  | 17 => (60567063 / 1000000000000 : ℝ)
  | 18 => (6136097 / 100000000000 : ℝ)
  | 19 => (62158693 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch041Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (24225117 / 500000000000 : ℝ)
  | 1 => (9834487 / 200000000000 : ℝ)
  | 2 => (49899599 / 1000000000000 : ℝ)
  | 3 => (50631673 / 1000000000000 : ℝ)
  | 4 => (25684301 / 500000000000 : ℝ)
  | 5 => (6513791 / 125000000000 : ℝ)
  | 6 => (52856793 / 1000000000000 : ℝ)
  | 7 => (13401983 / 250000000000 : ℝ)
  | 8 => (54363683 / 1000000000000 : ℝ)
  | 9 => (27561989 / 500000000000 : ℝ)
  | 10 => (27944373 / 500000000000 : ℝ)
  | 11 => (14164479 / 250000000000 : ℝ)
  | 12 => (14357853 / 250000000000 : ℝ)
  | 13 => (58209157 / 1000000000000 : ℝ)
  | 14 => (5899107 / 100000000000 : ℝ)
  | 15 => (14944267 / 250000000000 : ℝ)
  | 16 => (7570883 / 125000000000 : ℝ)
  | 17 => (61360971 / 1000000000000 : ℝ)
  | 18 => (31079347 / 500000000000 : ℝ)
  | 19 => (62960141 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch041Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((820 : ℝ) + (j.val : ℝ)) / 1600)
      (((820 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch041Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch041Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((820 : ℝ) + (j.val : ℝ)) / 1600)
    (((820 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch041Neg100WeightLower j.val) (hpThetaShiftThreeBatch041Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch041Neg100WeightLower, hpThetaShiftThreeBatch041Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch041Neg100_integral_bounds :
    (64824041 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (66838897 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (820 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch041Lower hpThetaJensenCellsBatch041Upper
    hpThetaShiftThreeBatch041Neg100WeightLower hpThetaShiftThreeBatch041Neg100WeightUpper hpThetaJensenCellsBatch041_bounds hpThetaShiftThreeBatch041Neg100_weight_bounds
  have hl : (64824041 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch041Lower j * hpThetaShiftThreeBatch041Neg100WeightLower j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftThreeBatch041Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftThreeBatch041Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch041Lower j * hpThetaShiftThreeBatch041Neg100WeightUpper j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftThreeBatch041Neg100WeightUpper j) / 1600) ≤ (66838897 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftThreeBatch041Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (820 : ℝ) / 1600 = 41 / 80 by norm_num,
    show ((820 : ℝ) + 20) / 1600 = (41 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch041Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1381647 / 250000000000 : ℝ)
  | 1 => (-2644889 / 500000000000 : ℝ)
  | 2 => (-1009523 / 200000000000 : ℝ)
  | 3 => (-120001 / 25000000000 : ℝ)
  | 4 => (-4546993 / 1000000000000 : ℝ)
  | 5 => (-134013 / 31250000000 : ℝ)
  | 6 => (-4024249 / 1000000000000 : ℝ)
  | 7 => (-58663 / 15625000000 : ℝ)
  | 8 => (-434863 / 125000000000 : ℝ)
  | 9 => (-3197607 / 1000000000000 : ℝ)
  | 10 => (-2910479 / 1000000000000 : ℝ)
  | 11 => (-2617459 / 1000000000000 : ℝ)
  | 12 => (-289811 / 125000000000 : ℝ)
  | 13 => (-2013503 / 1000000000000 : ℝ)
  | 14 => (-425611 / 250000000000 : ℝ)
  | 15 => (-5541 / 4000000000 : ℝ)
  | 16 => (-1061859 / 1000000000000 : ℝ)
  | 17 => (-732209 / 1000000000000 : ℝ)
  | 18 => (-396239 / 1000000000000 : ℝ)
  | 19 => (-26943 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch041Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5289777 / 1000000000000 : ℝ)
  | 1 => (-2523807 / 500000000000 : ℝ)
  | 2 => (-4800039 / 1000000000000 : ℝ)
  | 3 => (-284187 / 62500000000 : ℝ)
  | 4 => (-857683 / 200000000000 : ℝ)
  | 5 => (-503031 / 125000000000 : ℝ)
  | 6 => (-3754431 / 1000000000000 : ℝ)
  | 7 => (-3478903 / 1000000000000 : ℝ)
  | 8 => (-1598803 / 500000000000 : ℝ)
  | 9 => (-1455239 / 500000000000 : ℝ)
  | 10 => (-1308729 / 500000000000 : ℝ)
  | 11 => (-2318487 / 1000000000000 : ℝ)
  | 12 => (-1006751 / 500000000000 : ℝ)
  | 13 => (-1702443 / 1000000000000 : ℝ)
  | 14 => (-1385249 / 1000000000000 : ℝ)
  | 15 => (-530929 / 500000000000 : ℝ)
  | 16 => (-45763 / 62500000000 : ℝ)
  | 17 => (-198119 / 500000000000 : ℝ)
  | 18 => (-10777 / 200000000000 : ℝ)
  | 19 => (72 / 244140625 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch041Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((820 : ℝ) + (j.val : ℝ)) / 1600)
      (((820 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch041Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch041Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((820 : ℝ) + (j.val : ℝ)) / 1600)
    (((820 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch041Neg70WeightLower j.val) (hpThetaShiftThreeBatch041Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch041Neg70WeightLower, hpThetaShiftThreeBatch041Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch041Neg70_integral_bounds :
    (-1830917 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-1628579 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (820 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch041Lower hpThetaJensenCellsBatch041Upper
    hpThetaShiftThreeBatch041Neg70WeightLower hpThetaShiftThreeBatch041Neg70WeightUpper hpThetaJensenCellsBatch041_bounds hpThetaShiftThreeBatch041Neg70_weight_bounds
  have hl : (-1830917 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch041Lower j * hpThetaShiftThreeBatch041Neg70WeightLower j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftThreeBatch041Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftThreeBatch041Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch041Lower j * hpThetaShiftThreeBatch041Neg70WeightUpper j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftThreeBatch041Neg70WeightUpper j) / 1600) ≤ (-1628579 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftThreeBatch041Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (820 : ℝ) / 1600 = 41 / 80 by norm_num,
    show ((820 : ℝ) + 20) / 1600 = (41 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch041Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-25512131 / 1000000000000 : ℝ)
  | 1 => (-25734497 / 1000000000000 : ℝ)
  | 2 => (-811161 / 31250000000 : ℝ)
  | 3 => (-6545019 / 250000000000 : ℝ)
  | 4 => (-13201623 / 500000000000 : ℝ)
  | 5 => (-13313321 / 500000000000 : ℝ)
  | 6 => (-26850241 / 1000000000000 : ℝ)
  | 7 => (-13537011 / 500000000000 : ℝ)
  | 8 => (-13648981 / 500000000000 : ℝ)
  | 9 => (-13761019 / 500000000000 : ℝ)
  | 10 => (-13873113 / 500000000000 : ℝ)
  | 11 => (-3496313 / 125000000000 : ℝ)
  | 12 => (-881089 / 31250000000 : ℝ)
  | 13 => (-28419233 / 1000000000000 : ℝ)
  | 14 => (-14321817 / 500000000000 : ℝ)
  | 15 => (-28868027 / 1000000000000 : ℝ)
  | 16 => (-29092387 / 1000000000000 : ℝ)
  | 17 => (-1832293 / 62500000000 : ℝ)
  | 18 => (-29540903 / 1000000000000 : ℝ)
  | 19 => (-1860313 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch041Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-25290073 / 1000000000000 : ℝ)
  | 1 => (-2551213 / 100000000000 : ℝ)
  | 2 => (-804203 / 31250000000 : ℝ)
  | 3 => (-25957151 / 1000000000000 : ℝ)
  | 4 => (-1047203 / 40000000000 : ℝ)
  | 5 => (-5280649 / 200000000000 : ℝ)
  | 6 => (-26626641 / 1000000000000 : ℝ)
  | 7 => (-83907 / 3125000000 : ℝ)
  | 8 => (-27074021 / 1000000000000 : ℝ)
  | 9 => (-27297961 / 1000000000000 : ℝ)
  | 10 => (-27522037 / 1000000000000 : ℝ)
  | 11 => (-1109849 / 40000000000 : ℝ)
  | 12 => (-27970503 / 1000000000000 : ℝ)
  | 13 => (-28194847 / 1000000000000 : ℝ)
  | 14 => (-888101 / 31250000000 : ℝ)
  | 15 => (-28643633 / 1000000000000 : ℝ)
  | 16 => (-14434013 / 500000000000 : ℝ)
  | 17 => (-14546193 / 500000000000 : ℝ)
  | 18 => (-29316687 / 1000000000000 : ℝ)
  | 19 => (-14770451 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch041Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((820 : ℝ) + (j.val : ℝ)) / 1600)
      (((820 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch041Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch041Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((820 : ℝ) + (j.val : ℝ)) / 1600)
    (((820 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch041Neg45WeightLower j.val) (hpThetaShiftThreeBatch041Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch041Neg45WeightLower, hpThetaShiftThreeBatch041Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch041Neg45_integral_bounds :
    (-16642211 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-16232459 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (820 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch041Lower hpThetaJensenCellsBatch041Upper
    hpThetaShiftThreeBatch041Neg45WeightLower hpThetaShiftThreeBatch041Neg45WeightUpper hpThetaJensenCellsBatch041_bounds hpThetaShiftThreeBatch041Neg45_weight_bounds
  have hl : (-16642211 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch041Lower j * hpThetaShiftThreeBatch041Neg45WeightLower j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftThreeBatch041Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftThreeBatch041Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch041Lower j * hpThetaShiftThreeBatch041Neg45WeightUpper j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftThreeBatch041Neg45WeightUpper j) / 1600) ≤ (-16232459 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftThreeBatch041Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (820 : ℝ) / 1600 = 41 / 80 by norm_num,
    show ((820 : ℝ) + 20) / 1600 = (41 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch041Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2047749 / 250000000000 : ℝ)
  | 1 => (4026107 / 500000000000 : ℝ)
  | 2 => (3955653 / 500000000000 : ℝ)
  | 3 => (7768259 / 1000000000000 : ℝ)
  | 4 => (7623059 / 1000000000000 : ℝ)
  | 5 => (1868923 / 250000000000 : ℝ)
  | 6 => (114471 / 15625000000 : ℝ)
  | 7 => (7174401 / 1000000000000 : ℝ)
  | 8 => (140409 / 20000000000 : ℝ)
  | 9 => (1716069 / 250000000000 : ℝ)
  | 10 => (3352933 / 500000000000 : ℝ)
  | 11 => (1309041 / 200000000000 : ℝ)
  | 12 => (159557 / 25000000000 : ℝ)
  | 13 => (1554269 / 250000000000 : ℝ)
  | 14 => (6049581 / 1000000000000 : ℝ)
  | 15 => (293989 / 50000000000 : ℝ)
  | 16 => (5707659 / 1000000000000 : ℝ)
  | 17 => (1383301 / 250000000000 : ℝ)
  | 18 => (2678201 / 500000000000 : ℝ)
  | 19 => (2588619 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch041Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2081917 / 250000000000 : ℝ)
  | 1 => (8190997 / 1000000000000 : ℝ)
  | 2 => (1610443 / 200000000000 : ℝ)
  | 3 => (7911307 / 1000000000000 : ℝ)
  | 4 => (388413 / 50000000000 : ℝ)
  | 5 => (381153 / 50000000000 : ℝ)
  | 6 => (7475693 / 1000000000000 : ℝ)
  | 7 => (1465229 / 200000000000 : ℝ)
  | 8 => (3587201 / 500000000000 : ℝ)
  | 9 => (7020451 / 1000000000000 : ℝ)
  | 10 => (6864277 / 1000000000000 : ℝ)
  | 11 => (6705867 / 1000000000000 : ℝ)
  | 12 => (3272603 / 500000000000 : ℝ)
  | 13 => (6382281 / 1000000000000 : ℝ)
  | 14 => (6217077 / 1000000000000 : ℝ)
  | 15 => (3024791 / 500000000000 : ℝ)
  | 16 => (5879781 / 1000000000000 : ℝ)
  | 17 => (285383 / 50000000000 : ℝ)
  | 18 => (1106641 / 200000000000 : ℝ)
  | 19 => (5356403 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch041Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((820 : ℝ) + (j.val : ℝ)) / 1600)
      (((820 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch041Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch041Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((820 : ℝ) + (j.val : ℝ)) / 1600)
    (((820 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch041Neg25WeightLower j.val) (hpThetaShiftThreeBatch041Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch041Neg25WeightLower, hpThetaShiftThreeBatch041Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch041Neg25_integral_bounds :
    (8059503 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (8385209 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (820 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch041Lower hpThetaJensenCellsBatch041Upper
    hpThetaShiftThreeBatch041Neg25WeightLower hpThetaShiftThreeBatch041Neg25WeightUpper hpThetaJensenCellsBatch041_bounds hpThetaShiftThreeBatch041Neg25_weight_bounds
  have hl : (8059503 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch041Lower j * hpThetaShiftThreeBatch041Neg25WeightLower j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftThreeBatch041Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftThreeBatch041Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch041Lower j * hpThetaShiftThreeBatch041Neg25WeightUpper j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftThreeBatch041Neg25WeightUpper j) / 1600) ≤ (8385209 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftThreeBatch041Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (820 : ℝ) / 1600 = 41 / 80 by norm_num,
    show ((820 : ℝ) + 20) / 1600 = (41 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch041Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch041Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch041Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch041Neg25_integral_bounds
end HodgeProofHP
