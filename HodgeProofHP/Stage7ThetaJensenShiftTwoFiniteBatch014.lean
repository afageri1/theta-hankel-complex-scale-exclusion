/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch014

/-! Exact signed weight and batch integral certificates, batch 14 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch014Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (10579707 / 500000000000 : ℝ)
  | 1 => (4229223 / 200000000000 : ℝ)
  | 2 => (21127307 / 1000000000000 : ℝ)
  | 3 => (21102893 / 1000000000000 : ℝ)
  | 4 => (842911 / 40000000000 : ℝ)
  | 5 => (10518429 / 500000000000 : ℝ)
  | 6 => (10497521 / 500000000000 : ℝ)
  | 7 => (2094723 / 100000000000 : ℝ)
  | 8 => (835733 / 40000000000 : ℝ)
  | 9 => (20833229 / 1000000000000 : ℝ)
  | 10 => (10383421 / 500000000000 : ℝ)
  | 11 => (20694067 / 1000000000000 : ℝ)
  | 12 => (5153701 / 250000000000 : ℝ)
  | 13 => (4105791 / 200000000000 : ℝ)
  | 14 => (10218211 / 500000000000 : ℝ)
  | 15 => (4067421 / 200000000000 : ℝ)
  | 16 => (2528863 / 125000000000 : ℝ)
  | 17 => (10058861 / 500000000000 : ℝ)
  | 18 => (9998729 / 500000000000 : ℝ)
  | 19 => (9935007 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch014Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (211673 / 10000000000 : ℝ)
  | 1 => (4231883 / 200000000000 : ℝ)
  | 2 => (5286529 / 250000000000 : ℝ)
  | 3 => (5281827 / 250000000000 : ℝ)
  | 4 => (10551447 / 500000000000 : ℝ)
  | 5 => (2634097 / 125000000000 : ℝ)
  | 6 => (21036859 / 1000000000000 : ℝ)
  | 7 => (20995043 / 1000000000000 : ℝ)
  | 8 => (20947231 / 1000000000000 : ℝ)
  | 9 => (10446663 / 500000000000 : ℝ)
  | 10 => (2083323 / 100000000000 : ℝ)
  | 11 => (20766843 / 1000000000000 : ℝ)
  | 12 => (5173517 / 250000000000 : ℝ)
  | 13 => (4122961 / 200000000000 : ℝ)
  | 14 => (5132239 / 250000000000 : ℝ)
  | 15 => (20436423 / 1000000000000 : ℝ)
  | 16 => (10168553 / 500000000000 : ℝ)
  | 17 => (4046181 / 200000000000 : ℝ)
  | 18 => (20117723 / 1000000000000 : ℝ)
  | 19 => (19997459 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch014Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((280 : ℝ) + (j.val : ℝ)) / 1600)
      (((280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch014Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch014Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((280 : ℝ) + (j.val : ℝ)) / 1600)
    (((280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch014Neg100WeightLower j.val) (hpThetaShiftTwoBatch014Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch014Neg100WeightLower, hpThetaShiftTwoBatch014Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch014Neg100_integral_bounds :
    (336201181 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (341219133 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch014Lower hpThetaJensenCellsBatch014Upper
    hpThetaShiftTwoBatch014Neg100WeightLower hpThetaShiftTwoBatch014Neg100WeightUpper hpThetaJensenCellsBatch014_bounds hpThetaShiftTwoBatch014Neg100_weight_bounds
  have hl : (336201181 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch014Lower j * hpThetaShiftTwoBatch014Neg100WeightLower j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftTwoBatch014Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftTwoBatch014Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch014Lower j * hpThetaShiftTwoBatch014Neg100WeightUpper j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftTwoBatch014Neg100WeightUpper j) / 1600) ≤ (341219133 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftTwoBatch014Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (280 : ℝ) / 1600 = 14 / 80 by norm_num,
    show ((280 : ℝ) + 20) / 1600 = (14 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch014Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (37874753 / 1000000000000 : ℝ)
  | 1 => (298213 / 7812500000 : ℝ)
  | 2 => (38466261 / 1000000000000 : ℝ)
  | 3 => (19379833 / 500000000000 : ℝ)
  | 4 => (39051401 / 1000000000000 : ℝ)
  | 5 => (39341387 / 1000000000000 : ℝ)
  | 6 => (4953693 / 125000000000 : ℝ)
  | 7 => (2494737 / 62500000000 : ℝ)
  | 8 => (804001 / 20000000000 : ℝ)
  | 9 => (20241117 / 500000000000 : ℝ)
  | 10 => (40762263 / 1000000000000 : ℝ)
  | 11 => (10260013 / 250000000000 : ℝ)
  | 12 => (41315517 / 1000000000000 : ℝ)
  | 13 => (41588573 / 1000000000000 : ℝ)
  | 14 => (41859133 / 1000000000000 : ℝ)
  | 15 => (4212711 / 100000000000 : ℝ)
  | 16 => (42392417 / 1000000000000 : ℝ)
  | 17 => (21327483 / 500000000000 : ℝ)
  | 18 => (21457333 / 500000000000 : ℝ)
  | 19 => (43171429 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch014Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (7634253 / 200000000000 : ℝ)
  | 1 => (19233131 / 500000000000 : ℝ)
  | 2 => (38759667 / 1000000000000 : ℝ)
  | 3 => (19525701 / 500000000000 : ℝ)
  | 4 => (9835347 / 250000000000 : ℝ)
  | 5 => (7925909 / 200000000000 : ℝ)
  | 6 => (39915793 / 1000000000000 : ℝ)
  | 7 => (40200051 / 1000000000000 : ℝ)
  | 8 => (8096447 / 200000000000 : ℝ)
  | 9 => (5095283 / 125000000000 : ℝ)
  | 10 => (41040053 / 1000000000000 : ℝ)
  | 11 => (20657759 / 500000000000 : ℝ)
  | 12 => (20794287 / 500000000000 : ℝ)
  | 13 => (20929567 / 500000000000 : ℝ)
  | 14 => (42127111 / 1000000000000 : ℝ)
  | 15 => (21196209 / 500000000000 : ℝ)
  | 16 => (42654967 / 1000000000000 : ℝ)
  | 17 => (42914667 / 1000000000000 : ℝ)
  | 18 => (4317143 / 100000000000 : ℝ)
  | 19 => (10856291 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch014Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((280 : ℝ) + (j.val : ℝ)) / 1600)
      (((280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch014Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch014Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((280 : ℝ) + (j.val : ℝ)) / 1600)
    (((280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch014Neg65WeightLower j.val) (hpThetaShiftTwoBatch014Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch014Neg65WeightLower, hpThetaShiftTwoBatch014Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch014Neg65_integral_bounds :
    (658835021 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (671158919 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch014Lower hpThetaJensenCellsBatch014Upper
    hpThetaShiftTwoBatch014Neg65WeightLower hpThetaShiftTwoBatch014Neg65WeightUpper hpThetaJensenCellsBatch014_bounds hpThetaShiftTwoBatch014Neg65_weight_bounds
  have hl : (658835021 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch014Lower j * hpThetaShiftTwoBatch014Neg65WeightLower j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftTwoBatch014Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftTwoBatch014Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch014Lower j * hpThetaShiftTwoBatch014Neg65WeightUpper j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftTwoBatch014Neg65WeightUpper j) / 1600) ≤ (671158919 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftTwoBatch014Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (280 : ℝ) / 1600 = 14 / 80 by norm_num,
    show ((280 : ℝ) + 20) / 1600 = (14 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch014Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (12235987 / 250000000000 : ℝ)
  | 1 => (1236423 / 25000000000 : ℝ)
  | 2 => (6246453 / 125000000000 : ℝ)
  | 3 => (12622003 / 250000000000 : ℝ)
  | 4 => (25503019 / 500000000000 : ℝ)
  | 5 => (10305131 / 200000000000 : ℝ)
  | 6 => (13011703 / 250000000000 : ℝ)
  | 7 => (52569461 / 1000000000000 : ℝ)
  | 8 => (3318347 / 62500000000 : ℝ)
  | 9 => (53619033 / 1000000000000 : ℝ)
  | 10 => (13536463 / 250000000000 : ℝ)
  | 11 => (13668489 / 250000000000 : ℝ)
  | 12 => (55203293 / 1000000000000 : ℝ)
  | 13 => (3483363 / 62500000000 : ℝ)
  | 14 => (11253089 / 200000000000 : ℝ)
  | 15 => (14199537 / 250000000000 : ℝ)
  | 16 => (28665931 / 500000000000 : ℝ)
  | 17 => (1808329 / 31250000000 : ℝ)
  | 18 => (58402087 / 1000000000000 : ℝ)
  | 19 => (58938481 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch014Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (49456921 / 1000000000000 : ℝ)
  | 1 => (399773 / 8000000000 : ℝ)
  | 2 => (50488013 / 1000000000000 : ℝ)
  | 3 => (51006039 / 1000000000000 : ℝ)
  | 4 => (6440707 / 125000000000 : ℝ)
  | 5 => (52046813 / 1000000000000 : ℝ)
  | 6 => (26284731 / 500000000000 : ℝ)
  | 7 => (53093553 / 1000000000000 : ℝ)
  | 8 => (26809517 / 500000000000 : ℝ)
  | 9 => (54145853 / 1000000000000 : ℝ)
  | 10 => (54673957 / 1000000000000 : ℝ)
  | 11 => (27601647 / 500000000000 : ℝ)
  | 12 => (55733809 / 1000000000000 : ℝ)
  | 13 => (28132723 / 500000000000 : ℝ)
  | 14 => (56798149 / 1000000000000 : ℝ)
  | 15 => (57331863 / 1000000000000 : ℝ)
  | 16 => (57866529 / 1000000000000 : ℝ)
  | 17 => (7300261 / 125000000000 : ℝ)
  | 18 => (29469241 / 500000000000 : ℝ)
  | 19 => (59475651 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch014Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((280 : ℝ) + (j.val : ℝ)) / 1600)
      (((280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch014Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch014Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((280 : ℝ) + (j.val : ℝ)) / 1600)
    (((280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch014Neg45WeightLower j.val) (hpThetaShiftTwoBatch014Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch014Neg45WeightLower, hpThetaShiftTwoBatch014Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch014Neg45_integral_bounds :
    (437421653 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (446900359 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch014Lower hpThetaJensenCellsBatch014Upper
    hpThetaShiftTwoBatch014Neg45WeightLower hpThetaShiftTwoBatch014Neg45WeightUpper hpThetaJensenCellsBatch014_bounds hpThetaShiftTwoBatch014Neg45_weight_bounds
  have hl : (437421653 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch014Lower j * hpThetaShiftTwoBatch014Neg45WeightLower j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftTwoBatch014Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftTwoBatch014Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch014Lower j * hpThetaShiftTwoBatch014Neg45WeightUpper j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftTwoBatch014Neg45WeightUpper j) / 1600) ≤ (446900359 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftTwoBatch014Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (280 : ℝ) / 1600 = 14 / 80 by norm_num,
    show ((280 : ℝ) + 20) / 1600 = (14 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch014Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (61173559 / 1000000000000 : ℝ)
  | 1 => (3870991 / 62500000000 : ℝ)
  | 2 => (31351967 / 500000000000 : ℝ)
  | 3 => (63477793 / 1000000000000 : ℝ)
  | 4 => (32128717 / 500000000000 : ℝ)
  | 5 => (32521429 / 500000000000 : ℝ)
  | 6 => (4114629 / 62500000000 : ℝ)
  | 7 => (66631051 / 1000000000000 : ℝ)
  | 8 => (67433817 / 1000000000000 : ℝ)
  | 9 => (34121181 / 500000000000 : ℝ)
  | 10 => (34528341 / 500000000000 : ℝ)
  | 11 => (34938387 / 500000000000 : ℝ)
  | 12 => (17675659 / 250000000000 : ℝ)
  | 13 => (71534263 / 1000000000000 : ℝ)
  | 14 => (1447433 / 20000000000 : ℝ)
  | 15 => (73214793 / 1000000000000 : ℝ)
  | 16 => (37031843 / 500000000000 : ℝ)
  | 17 => (37459161 / 500000000000 : ℝ)
  | 18 => (15155739 / 200000000000 : ℝ)
  | 19 => (38322399 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch014Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (61935857 / 1000000000000 : ℝ)
  | 1 => (12540787 / 200000000000 : ℝ)
  | 2 => (31738897 / 500000000000 : ℝ)
  | 3 => (12851487 / 200000000000 : ℝ)
  | 4 => (65042859 / 1000000000000 : ℝ)
  | 5 => (13166813 / 200000000000 : ℝ)
  | 6 => (16657763 / 250000000000 : ℝ)
  | 7 => (33716909 / 500000000000 : ℝ)
  | 8 => (68242363 / 1000000000000 : ℝ)
  | 9 => (69056683 / 1000000000000 : ℝ)
  | 10 => (2795071 / 40000000000 : ℝ)
  | 11 => (70702637 / 1000000000000 : ℝ)
  | 12 => (8941783 / 125000000000 : ℝ)
  | 13 => (72371651 / 1000000000000 : ℝ)
  | 14 => (36607397 / 500000000000 : ℝ)
  | 15 => (74063687 / 1000000000000 : ℝ)
  | 16 => (74918323 / 1000000000000 : ℝ)
  | 17 => (9472337 / 125000000000 : ℝ)
  | 18 => (76644799 / 1000000000000 : ℝ)
  | 19 => (4844789 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch014Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((280 : ℝ) + (j.val : ℝ)) / 1600)
      (((280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch014Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch014Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((280 : ℝ) + (j.val : ℝ)) / 1600)
    (((280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch014Neg25WeightLower j.val) (hpThetaShiftTwoBatch014Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch014Neg25WeightLower, hpThetaShiftTwoBatch014Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch014Neg25_integral_bounds :
    (278883037 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (1142094747 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch014Lower hpThetaJensenCellsBatch014Upper
    hpThetaShiftTwoBatch014Neg25WeightLower hpThetaShiftTwoBatch014Neg25WeightUpper hpThetaJensenCellsBatch014_bounds hpThetaShiftTwoBatch014Neg25_weight_bounds
  have hl : (278883037 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch014Lower j * hpThetaShiftTwoBatch014Neg25WeightLower j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftTwoBatch014Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftTwoBatch014Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch014Lower j * hpThetaShiftTwoBatch014Neg25WeightUpper j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftTwoBatch014Neg25WeightUpper j) / 1600) ≤ (1142094747 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftTwoBatch014Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (280 : ℝ) / 1600 = 14 / 80 by norm_num,
    show ((280 : ℝ) + 20) / 1600 = (14 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch014Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch014Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch014Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch014Neg25_integral_bounds
end HodgeProofHP
