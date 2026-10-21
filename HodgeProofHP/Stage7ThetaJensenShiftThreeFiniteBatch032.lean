/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch032

/-! Exact signed weight and batch integral certificates, batch 32 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch032Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-102203 / 25000000000 : ℝ)
  | 1 => (-1019451 / 250000000000 : ℝ)
  | 2 => (-4066233 / 1000000000000 : ℝ)
  | 3 => (-4053383 / 1000000000000 : ℝ)
  | 4 => (-1009807 / 250000000000 : ℝ)
  | 5 => (-62871 / 15625000000 : ℝ)
  | 6 => (-801381 / 200000000000 : ℝ)
  | 7 => (-1994343 / 500000000000 : ℝ)
  | 8 => (-198453 / 50000000000 : ℝ)
  | 9 => (-3948001 / 1000000000000 : ℝ)
  | 10 => (-3925483 / 1000000000000 : ℝ)
  | 11 => (-3901479 / 1000000000000 : ℝ)
  | 12 => (-3875963 / 1000000000000 : ℝ)
  | 13 => (-3848907 / 1000000000000 : ℝ)
  | 14 => (-955071 / 250000000000 : ℝ)
  | 15 => (-3790067 / 1000000000000 : ℝ)
  | 16 => (-3758227 / 1000000000000 : ℝ)
  | 17 => (-58199 / 15625000000 : ℝ)
  | 18 => (-3689567 / 1000000000000 : ℝ)
  | 19 => (-3652691 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch032Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4077803 / 1000000000000 : ℝ)
  | 1 => (-508279 / 125000000000 : ℝ)
  | 2 => (-2026691 / 500000000000 : ℝ)
  | 3 => (-4039227 / 1000000000000 : ℝ)
  | 4 => (-4023743 / 1000000000000 : ℝ)
  | 5 => (-500863 / 125000000000 : ℝ)
  | 6 => (-797737 / 200000000000 : ℝ)
  | 7 => (-3969059 / 1000000000000 : ℝ)
  | 8 => (-987 / 250000000 : ℝ)
  | 9 => (-1962741 / 500000000000 : ℝ)
  | 10 => (-1950739 / 500000000000 : ℝ)
  | 11 => (-1937981 / 500000000000 : ℝ)
  | 12 => (-1924453 / 500000000000 : ℝ)
  | 13 => (-3820283 / 1000000000000 : ℝ)
  | 14 => (-1895033 / 500000000000 : ℝ)
  | 15 => (-1879113 / 500000000000 : ℝ)
  | 16 => (-744947 / 200000000000 : ℝ)
  | 17 => (-1844783 / 500000000000 : ℝ)
  | 18 => (-365269 / 100000000000 : ℝ)
  | 19 => (-1807039 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch032Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((640 : ℝ) + (j.val : ℝ)) / 1600)
      (((640 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch032Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch032Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((640 : ℝ) + (j.val : ℝ)) / 1600)
    (((640 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch032Neg100WeightLower j.val) (hpThetaShiftThreeBatch032Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch032Neg100WeightLower, hpThetaShiftThreeBatch032Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch032Neg100_integral_bounds :
    (-4026549 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-7888703 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (640 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch032Lower hpThetaJensenCellsBatch032Upper
    hpThetaShiftThreeBatch032Neg100WeightLower hpThetaShiftThreeBatch032Neg100WeightUpper hpThetaJensenCellsBatch032_bounds hpThetaShiftThreeBatch032Neg100_weight_bounds
  have hl : (-4026549 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch032Lower j * hpThetaShiftThreeBatch032Neg100WeightLower j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftThreeBatch032Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftThreeBatch032Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch032Lower j * hpThetaShiftThreeBatch032Neg100WeightUpper j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftThreeBatch032Neg100WeightUpper j) / 1600) ≤ (-7888703 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftThreeBatch032Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (640 : ℝ) / 1600 = 32 / 80 by norm_num,
    show ((640 : ℝ) + 20) / 1600 = (32 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch032Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-221359 / 40000000000 : ℝ)
  | 1 => (-5604139 / 1000000000000 : ℝ)
  | 2 => (-354661 / 62500000000 : ℝ)
  | 3 => (-2872639 / 500000000000 : ℝ)
  | 4 => (-2908119 / 500000000000 : ℝ)
  | 5 => (-735931 / 125000000000 : ℝ)
  | 6 => (-59589 / 10000000000 : ℝ)
  | 7 => (-3015293 / 500000000000 : ℝ)
  | 8 => (-6102497 / 1000000000000 : ℝ)
  | 9 => (-49397 / 8000000000 : ℝ)
  | 10 => (-78087 / 12500000000 : ℝ)
  | 11 => (-1263899 / 200000000000 : ℝ)
  | 12 => (-319611 / 50000000000 : ℝ)
  | 13 => (-51721 / 8000000000 : ℝ)
  | 14 => (-6538201 / 1000000000000 : ℝ)
  | 15 => (-3305719 / 500000000000 : ℝ)
  | 16 => (-6684827 / 1000000000000 : ℝ)
  | 17 => (-1689589 / 250000000000 : ℝ)
  | 18 => (-427001 / 62500000000 : ℝ)
  | 19 => (-1726449 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch032Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5464091 / 1000000000000 : ℝ)
  | 1 => (-2766987 / 500000000000 : ℝ)
  | 2 => (-2802069 / 500000000000 : ℝ)
  | 3 => (-226983 / 40000000000 : ℝ)
  | 4 => (-5745277 / 1000000000000 : ℝ)
  | 5 => (-5816237 / 1000000000000 : ℝ)
  | 6 => (-5887447 / 1000000000000 : ℝ)
  | 7 => (-5958899 / 1000000000000 : ℝ)
  | 8 => (-1206117 / 200000000000 : ℝ)
  | 9 => (-190703 / 31250000000 : ℝ)
  | 10 => (-192957 / 31250000000 : ℝ)
  | 11 => (-6246959 / 1000000000000 : ℝ)
  | 12 => (-3159747 / 500000000000 : ℝ)
  | 13 => (-6392219 / 1000000000000 : ℝ)
  | 14 => (-1616281 / 250000000000 : ℝ)
  | 15 => (-32691 / 5000000000 : ℝ)
  | 16 => (-6611437 / 1000000000000 : ℝ)
  | 17 => (-3342413 / 500000000000 : ℝ)
  | 18 => (-1351671 / 200000000000 : ℝ)
  | 19 => (-1366403 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch032Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((640 : ℝ) + (j.val : ℝ)) / 1600)
      (((640 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch032Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch032Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((640 : ℝ) + (j.val : ℝ)) / 1600)
    (((640 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch032Neg70WeightLower j.val) (hpThetaShiftThreeBatch032Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch032Neg70WeightLower, hpThetaShiftThreeBatch032Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch032Neg70_integral_bounds :
    (-5099441 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-12417421 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (640 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch032Lower hpThetaJensenCellsBatch032Upper
    hpThetaShiftThreeBatch032Neg70WeightLower hpThetaShiftThreeBatch032Neg70WeightUpper hpThetaJensenCellsBatch032_bounds hpThetaShiftThreeBatch032Neg70_weight_bounds
  have hl : (-5099441 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch032Lower j * hpThetaShiftThreeBatch032Neg70WeightLower j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftThreeBatch032Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftThreeBatch032Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch032Lower j * hpThetaShiftThreeBatch032Neg70WeightUpper j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftThreeBatch032Neg70WeightUpper j) / 1600) ≤ (-12417421 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftThreeBatch032Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (640 : ℝ) / 1600 = 32 / 80 by norm_num,
    show ((640 : ℝ) + 20) / 1600 = (32 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch032Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (36993 / 200000000000 : ℝ)
  | 1 => (13151 / 100000000000 : ℝ)
  | 2 => (4827 / 62500000000 : ℝ)
  | 3 => (177 / 8000000000 : ℝ)
  | 4 => (-4227 / 125000000000 : ℝ)
  | 5 => (-90597 / 1000000000000 : ℝ)
  | 6 => (-148223 / 1000000000000 : ℝ)
  | 7 => (-2067 / 10000000000 : ℝ)
  | 8 => (-266033 / 1000000000000 : ℝ)
  | 9 => (-81557 / 250000000000 : ℝ)
  | 10 => (-387289 / 1000000000000 : ℝ)
  | 11 => (-449223 / 1000000000000 : ℝ)
  | 12 => (-256017 / 500000000000 : ℝ)
  | 13 => (-575729 / 1000000000000 : ℝ)
  | 14 => (-80039 / 125000000000 : ℝ)
  | 15 => (-176447 / 250000000000 : ℝ)
  | 16 => (-772163 / 1000000000000 : ℝ)
  | 17 => (-419721 / 500000000000 : ℝ)
  | 18 => (-90763 / 100000000000 : ℝ)
  | 19 => (-976733 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch032Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (59401 / 250000000000 : ℝ)
  | 1 => (92483 / 500000000000 : ℝ)
  | 2 => (131511 / 1000000000000 : ℝ)
  | 3 => (77233 / 1000000000000 : ℝ)
  | 4 => (11063 / 500000000000 : ℝ)
  | 5 => (-6763 / 200000000000 : ℝ)
  | 6 => (-22649 / 250000000000 : ℝ)
  | 7 => (-74111 / 500000000000 : ℝ)
  | 8 => (-206699 / 1000000000000 : ℝ)
  | 9 => (-16627 / 62500000000 : ℝ)
  | 10 => (-326227 / 1000000000000 : ℝ)
  | 11 => (-48411 / 125000000000 : ℝ)
  | 12 => (-224611 / 500000000000 : ℝ)
  | 13 => (-512033 / 1000000000000 : ℝ)
  | 14 => (-35983 / 62500000000 : ℝ)
  | 15 => (-640311 / 1000000000000 : ℝ)
  | 16 => (-705787 / 1000000000000 : ℝ)
  | 17 => (-386081 / 500000000000 : ℝ)
  | 18 => (-839441 / 1000000000000 : ℝ)
  | 19 => (-907629 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch032Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((640 : ℝ) + (j.val : ℝ)) / 1600)
      (((640 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch032Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch032Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((640 : ℝ) + (j.val : ℝ)) / 1600)
    (((640 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch032Neg45WeightLower j.val) (hpThetaShiftThreeBatch032Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch032Neg45WeightLower, hpThetaShiftThreeBatch032Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch032Neg45_integral_bounds :
    (-59191 / 40000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-1209499 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (640 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch032Lower hpThetaJensenCellsBatch032Upper
    hpThetaShiftThreeBatch032Neg45WeightLower hpThetaShiftThreeBatch032Neg45WeightUpper hpThetaJensenCellsBatch032_bounds hpThetaShiftThreeBatch032Neg45_weight_bounds
  have hl : (-59191 / 40000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch032Lower j * hpThetaShiftThreeBatch032Neg45WeightLower j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftThreeBatch032Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftThreeBatch032Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch032Lower j * hpThetaShiftThreeBatch032Neg45WeightUpper j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftThreeBatch032Neg45WeightUpper j) / 1600) ≤ (-1209499 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftThreeBatch032Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (640 : ℝ) / 1600 = 32 / 80 by norm_num,
    show ((640 : ℝ) + 20) / 1600 = (32 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch032Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (5491871 / 500000000000 : ℝ)
  | 1 => (5516063 / 500000000000 : ℝ)
  | 2 => (11080307 / 1000000000000 : ℝ)
  | 3 => (2782069 / 250000000000 : ℝ)
  | 4 => (11176029 / 1000000000000 : ℝ)
  | 5 => (11223559 / 1000000000000 : ℝ)
  | 6 => (563543 / 50000000000 : ℝ)
  | 7 => (5658963 / 500000000000 : ℝ)
  | 8 => (45459 / 4000000000 : ℝ)
  | 9 => (5705663 / 500000000000 : ℝ)
  | 10 => (11457647 / 1000000000000 : ℝ)
  | 11 => (2875927 / 250000000000 : ℝ)
  | 12 => (23099 / 2000000000 : ℝ)
  | 13 => (11595019 / 1000000000000 : ℝ)
  | 14 => (181879 / 15625000000 : ℝ)
  | 15 => (5842603 / 500000000000 : ℝ)
  | 16 => (11729861 / 1000000000000 : ℝ)
  | 17 => (2354843 / 200000000000 : ℝ)
  | 18 => (5909131 / 500000000000 : ℝ)
  | 19 => (11861993 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch032Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (11032127 / 1000000000000 : ℝ)
  | 1 => (2770077 / 250000000000 : ℝ)
  | 2 => (11128277 / 1000000000000 : ℝ)
  | 3 => (1117603 / 100000000000 : ℝ)
  | 4 => (280589 / 25000000000 : ℝ)
  | 5 => (11270861 / 1000000000000 : ℝ)
  | 6 => (11317927 / 1000000000000 : ℝ)
  | 7 => (11364751 / 1000000000000 : ℝ)
  | 8 => (11411327 / 1000000000000 : ℝ)
  | 9 => (716103 / 62500000000 : ℝ)
  | 10 => (11503709 / 1000000000000 : ℝ)
  | 11 => (11549501 / 1000000000000 : ℝ)
  | 12 => (579751 / 50000000000 : ℝ)
  | 13 => (11640257 / 1000000000000 : ℝ)
  | 14 => (11685207 / 1000000000000 : ℝ)
  | 15 => (5864931 / 500000000000 : ℝ)
  | 16 => (1471777 / 125000000000 : ℝ)
  | 17 => (11818263 / 1000000000000 : ℝ)
  | 18 => (5930997 / 500000000000 : ℝ)
  | 19 => (11905403 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch032Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((640 : ℝ) + (j.val : ℝ)) / 1600)
      (((640 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch032Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch032Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((640 : ℝ) + (j.val : ℝ)) / 1600)
    (((640 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch032Neg25WeightLower j.val) (hpThetaShiftThreeBatch032Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch032Neg25WeightLower, hpThetaShiftThreeBatch032Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch032Neg25_integral_bounds :
    (46284619 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (4715649 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (640 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch032Lower hpThetaJensenCellsBatch032Upper
    hpThetaShiftThreeBatch032Neg25WeightLower hpThetaShiftThreeBatch032Neg25WeightUpper hpThetaJensenCellsBatch032_bounds hpThetaShiftThreeBatch032Neg25_weight_bounds
  have hl : (46284619 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch032Lower j * hpThetaShiftThreeBatch032Neg25WeightLower j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftThreeBatch032Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftThreeBatch032Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch032Lower j * hpThetaShiftThreeBatch032Neg25WeightUpper j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftThreeBatch032Neg25WeightUpper j) / 1600) ≤ (4715649 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftThreeBatch032Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (640 : ℝ) / 1600 = 32 / 80 by norm_num,
    show ((640 : ℝ) + 20) / 1600 = (32 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch032Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch032Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch032Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch032Neg25_integral_bounds
end HodgeProofHP
