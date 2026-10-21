/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch056

/-! Exact signed weight and batch integral certificates, batch 56 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch056Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-267129783 / 125000000000 : ℝ)
  | 1 => (-17431619 / 8000000000 : ℝ)
  | 2 => (-1110748309 / 500000000000 : ℝ)
  | 3 => (-452935751 / 200000000000 : ℝ)
  | 4 => (-2308506627 / 1000000000000 : ℝ)
  | 5 => (-2352988157 / 1000000000000 : ℝ)
  | 6 => (-2398131349 / 1000000000000 : ℝ)
  | 7 => (-244394429 / 100000000000 : ℝ)
  | 8 => (-49808703 / 20000000000 : ℝ)
  | 9 => (-2537612181 / 1000000000000 : ℝ)
  | 10 => (-1292741861 / 500000000000 : ℝ)
  | 11 => (-1317029097 / 500000000000 : ℝ)
  | 12 => (-2683344107 / 1000000000000 : ℝ)
  | 13 => (-341668757 / 125000000000 : ℝ)
  | 14 => (-696021181 / 250000000000 : ℝ)
  | 15 => (-35444461 / 12500000000 : ℝ)
  | 16 => (-1443887693 / 500000000000 : ℝ)
  | 17 => (-2940749189 / 1000000000000 : ℝ)
  | 18 => (-299448733 / 100000000000 : ℝ)
  | 19 => (-3048998939 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch056Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2095746601 / 1000000000000 : ℝ)
  | 1 => (-2137038263 / 1000000000000 : ℝ)
  | 2 => (-1089476187 / 500000000000 : ℝ)
  | 3 => (-2221496617 / 1000000000000 : ℝ)
  | 4 => (-1132339377 / 500000000000 : ℝ)
  | 5 => (-1154253313 / 500000000000 : ℝ)
  | 6 => (-588247039 / 250000000000 : ℝ)
  | 7 => (-599532837 / 250000000000 : ℝ)
  | 8 => (-2443944289 / 1000000000000 : ℝ)
  | 9 => (-2490435149 / 1000000000000 : ℝ)
  | 10 => (-126880609 / 50000000000 : ℝ)
  | 11 => (-2585483721 / 1000000000000 : ℝ)
  | 12 => (-2634058193 / 1000000000000 : ℝ)
  | 13 => (-1341672053 / 500000000000 : ℝ)
  | 14 => (-546670011 / 200000000000 : ℝ)
  | 15 => (-2784084723 / 1000000000000 : ℝ)
  | 16 => (-2835556879 / 1000000000000 : ℝ)
  | 17 => (-577555077 / 200000000000 : ℝ)
  | 18 => (-735187297 / 250000000000 : ℝ)
  | 19 => (-2994487329 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch056Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1120 : ℝ) + (j.val : ℝ)) / 1600)
      (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch056Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch056Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1120 : ℝ) + (j.val : ℝ)) / 1600)
    (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch056Neg100WeightLower j.val) (hpThetaShiftThreeBatch056Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch056Neg100WeightLower, hpThetaShiftThreeBatch056Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch056Neg100_integral_bounds :
    (-135439403 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-65033681 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch056Lower hpThetaJensenCellsBatch056Upper
    hpThetaShiftThreeBatch056Neg100WeightLower hpThetaShiftThreeBatch056Neg100WeightUpper hpThetaJensenCellsBatch056_bounds hpThetaShiftThreeBatch056Neg100_weight_bounds
  have hl : (-135439403 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch056Lower j * hpThetaShiftThreeBatch056Neg100WeightLower j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftThreeBatch056Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftThreeBatch056Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch056Lower j * hpThetaShiftThreeBatch056Neg100WeightUpper j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftThreeBatch056Neg100WeightUpper j) / 1600) ≤ (-65033681 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftThreeBatch056Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1120 : ℝ) / 1600 = 56 / 80 by norm_num,
    show ((1120 : ℝ) + 20) / 1600 = (56 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch056Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (369548777 / 1000000000000 : ℝ)
  | 1 => (369374977 / 1000000000000 : ℝ)
  | 2 => (73826907 / 200000000000 : ℝ)
  | 3 => (184413049 / 500000000000 : ℝ)
  | 4 => (368448299 / 1000000000000 : ℝ)
  | 5 => (367999749 / 1000000000000 : ℝ)
  | 6 => (183739521 / 500000000000 : ℝ)
  | 7 => (91721189 / 250000000000 : ℝ)
  | 8 => (366215447 / 1000000000000 : ℝ)
  | 9 => (365469653 / 1000000000000 : ℝ)
  | 10 => (72929179 / 200000000000 : ℝ)
  | 11 => (22733917 / 62500000000 : ℝ)
  | 12 => (181379233 / 500000000000 : ℝ)
  | 13 => (180845869 / 500000000000 : ℝ)
  | 14 => (360540929 / 1000000000000 : ℝ)
  | 15 => (359304461 / 1000000000000 : ℝ)
  | 16 => (71596147 / 200000000000 : ℝ)
  | 17 => (356568133 / 1000000000000 : ℝ)
  | 18 => (71013003 / 200000000000 : ℝ)
  | 19 => (8836743 / 25000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch056Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (92414317 / 250000000000 : ℝ)
  | 1 => (184774389 / 500000000000 : ℝ)
  | 2 => (184687489 / 500000000000 : ℝ)
  | 3 => (46141817 / 125000000000 : ℝ)
  | 4 => (368826099 / 1000000000000 : ℝ)
  | 5 => (3684483 / 10000000000 : ℝ)
  | 6 => (1471999 / 4000000000 : ℝ)
  | 7 => (367479043 / 1000000000000 : ℝ)
  | 8 => (366884757 / 1000000000000 : ℝ)
  | 9 => (45776931 / 125000000000 : ℝ)
  | 10 => (182734827 / 500000000000 : ℝ)
  | 11 => (45580737 / 125000000000 : ℝ)
  | 12 => (363742673 / 1000000000000 : ℝ)
  | 13 => (362758467 / 1000000000000 : ℝ)
  | 14 => (361691739 / 1000000000000 : ℝ)
  | 15 => (36054093 / 100000000000 : ℝ)
  | 16 => (179652231 / 500000000000 : ℝ)
  | 17 => (5593449 / 15625000000 : ℝ)
  | 18 => (178284067 / 500000000000 : ℝ)
  | 19 => (44383127 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch056Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1120 : ℝ) + (j.val : ℝ)) / 1600)
      (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch056Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch056Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1120 : ℝ) + (j.val : ℝ)) / 1600)
    (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch056Neg70WeightLower j.val) (hpThetaShiftThreeBatch056Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch056Neg70WeightLower, hpThetaShiftThreeBatch056Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch056Neg70_integral_bounds :
    (9453917 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (19364289 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch056Lower hpThetaJensenCellsBatch056Upper
    hpThetaShiftThreeBatch056Neg70WeightLower hpThetaShiftThreeBatch056Neg70WeightUpper hpThetaJensenCellsBatch056_bounds hpThetaShiftThreeBatch056Neg70_weight_bounds
  have hl : (9453917 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch056Lower j * hpThetaShiftThreeBatch056Neg70WeightLower j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftThreeBatch056Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftThreeBatch056Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch056Lower j * hpThetaShiftThreeBatch056Neg70WeightUpper j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftThreeBatch056Neg70WeightUpper j) / 1600) ≤ (19364289 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftThreeBatch056Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1120 : ℝ) / 1600 = 56 / 80 by norm_num,
    show ((1120 : ℝ) + 20) / 1600 = (56 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch056Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (126830579 / 1000000000000 : ℝ)
  | 1 => (129360403 / 1000000000000 : ℝ)
  | 2 => (16489327 / 125000000000 : ℝ)
  | 3 => (134493321 / 1000000000000 : ℝ)
  | 4 => (137096617 / 1000000000000 : ℝ)
  | 5 => (27944921 / 200000000000 : ℝ)
  | 6 => (142377383 / 1000000000000 : ℝ)
  | 7 => (18131881 / 125000000000 : ℝ)
  | 8 => (73878849 / 500000000000 : ℝ)
  | 9 => (37621357 / 250000000000 : ℝ)
  | 10 => (153238333 / 1000000000000 : ℝ)
  | 11 => (78008253 / 500000000000 : ℝ)
  | 12 => (3970501 / 25000000000 : ℝ)
  | 13 => (80824513 / 500000000000 : ℝ)
  | 14 => (32900711 / 200000000000 : ℝ)
  | 15 => (33476743 / 200000000000 : ℝ)
  | 16 => (34057919 / 200000000000 : ℝ)
  | 17 => (173221281 / 1000000000000 : ℝ)
  | 18 => (88089429 / 500000000000 : ℝ)
  | 19 => (179162411 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch056Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (32340101 / 250000000000 : ℝ)
  | 1 => (131914617 / 1000000000000 : ℝ)
  | 2 => (67246661 / 500000000000 : ℝ)
  | 3 => (68548309 / 500000000000 : ℝ)
  | 4 => (69862303 / 500000000000 : ℝ)
  | 5 => (17797173 / 125000000000 : ℝ)
  | 6 => (145055049 / 1000000000000 : ℝ)
  | 7 => (147757699 / 1000000000000 : ℝ)
  | 8 => (150485429 / 1000000000000 : ℝ)
  | 9 => (76619167 / 500000000000 : ℝ)
  | 10 => (156016507 / 1000000000000 : ℝ)
  | 11 => (158820041 / 1000000000000 : ℝ)
  | 12 => (161649027 / 1000000000000 : ℝ)
  | 13 => (41125889 / 250000000000 : ℝ)
  | 14 => (41845929 / 250000000000 : ℝ)
  | 15 => (42572399 / 250000000000 : ℝ)
  | 16 => (86610641 / 500000000000 : ℝ)
  | 17 => (176178859 / 1000000000000 : ℝ)
  | 18 => (44790603 / 250000000000 : ℝ)
  | 19 => (182172023 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch056Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1120 : ℝ) + (j.val : ℝ)) / 1600)
      (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch056Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch056Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1120 : ℝ) + (j.val : ℝ)) / 1600)
    (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch056Neg45WeightLower j.val) (hpThetaShiftThreeBatch056Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch056Neg45WeightLower, hpThetaShiftThreeBatch056Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch056Neg45_integral_bounds :
    (7844953 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (4081817 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch056Lower hpThetaJensenCellsBatch056Upper
    hpThetaShiftThreeBatch056Neg45WeightLower hpThetaShiftThreeBatch056Neg45WeightUpper hpThetaJensenCellsBatch056_bounds hpThetaShiftThreeBatch056Neg45_weight_bounds
  have hl : (7844953 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch056Lower j * hpThetaShiftThreeBatch056Neg45WeightLower j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftThreeBatch056Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftThreeBatch056Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch056Lower j * hpThetaShiftThreeBatch056Neg45WeightUpper j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftThreeBatch056Neg45WeightUpper j) / 1600) ≤ (4081817 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftThreeBatch056Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1120 : ℝ) / 1600 = 56 / 80 by norm_num,
    show ((1120 : ℝ) + 20) / 1600 = (56 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch056Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-167761687 / 1000000000000 : ℝ)
  | 1 => (-168737061 / 1000000000000 : ℝ)
  | 2 => (-84856151 / 500000000000 : ℝ)
  | 3 => (-170687349 / 1000000000000 : ℝ)
  | 4 => (-85831069 / 500000000000 : ℝ)
  | 5 => (-2697447 / 15625000000 : ℝ)
  | 6 => (-173610693 / 1000000000000 : ℝ)
  | 7 => (-17458433 / 100000000000 : ℝ)
  | 8 => (-175557453 / 1000000000000 : ℝ)
  | 9 => (-35305999 / 200000000000 : ℝ)
  | 10 => (-177501891 / 1000000000000 : ℝ)
  | 11 => (-89236537 / 500000000000 : ℝ)
  | 12 => (-7177739 / 40000000000 : ℝ)
  | 13 => (-90206513 / 500000000000 : ℝ)
  | 14 => (-181381657 / 1000000000000 : ℝ)
  | 15 => (-1823493 / 10000000000 : ℝ)
  | 16 => (-91657941 / 500000000000 : ℝ)
  | 17 => (-92140667 / 500000000000 : ℝ)
  | 18 => (-92622791 / 500000000000 : ℝ)
  | 19 => (-37241711 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch056Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-83393121 / 500000000000 : ℝ)
  | 1 => (-83880843 / 500000000000 : ℝ)
  | 2 => (-8436853 / 50000000000 : ℝ)
  | 3 => (-169712301 / 1000000000000 : ℝ)
  | 4 => (-42671837 / 250000000000 : ℝ)
  | 5 => (-171662137 / 1000000000000 : ℝ)
  | 6 => (-172636607 / 1000000000000 : ℝ)
  | 7 => (-43402673 / 250000000000 : ℝ)
  | 8 => (-174584329 / 1000000000000 : ℝ)
  | 9 => (-43889363 / 250000000000 : ℝ)
  | 10 => (-88264997 / 500000000000 : ℝ)
  | 11 => (-17750189 / 100000000000 : ℝ)
  | 12 => (-178473073 / 1000000000000 : ℝ)
  | 13 => (-89721737 / 500000000000 : ℝ)
  | 14 => (-7216521 / 40000000000 : ℝ)
  | 15 => (-22672707 / 125000000000 : ℝ)
  | 16 => (-182349299 / 1000000000000 : ℝ)
  | 17 => (-183315881 / 1000000000000 : ℝ)
  | 18 => (-184281333 / 1000000000000 : ℝ)
  | 19 => (-185245581 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch056Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1120 : ℝ) + (j.val : ℝ)) / 1600)
      (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch056Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch056Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1120 : ℝ) + (j.val : ℝ)) / 1600)
    (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch056Neg25WeightLower j.val) (hpThetaShiftThreeBatch056Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch056Neg25WeightLower, hpThetaShiftThreeBatch056Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch056Neg25_integral_bounds :
    (-9370793 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-9118899 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch056Lower hpThetaJensenCellsBatch056Upper
    hpThetaShiftThreeBatch056Neg25WeightLower hpThetaShiftThreeBatch056Neg25WeightUpper hpThetaJensenCellsBatch056_bounds hpThetaShiftThreeBatch056Neg25_weight_bounds
  have hl : (-9370793 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch056Lower j * hpThetaShiftThreeBatch056Neg25WeightLower j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftThreeBatch056Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftThreeBatch056Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch056Lower j * hpThetaShiftThreeBatch056Neg25WeightUpper j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftThreeBatch056Neg25WeightUpper j) / 1600) ≤ (-9118899 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftThreeBatch056Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1120 : ℝ) / 1600 = 56 / 80 by norm_num,
    show ((1120 : ℝ) + 20) / 1600 = (56 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch056Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch056Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch056Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch056Neg25_integral_bounds
end HodgeProofHP
