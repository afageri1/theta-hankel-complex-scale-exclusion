/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch051

/-! Exact signed weight and batch integral certificates, batch 51 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch051Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-428433313247 / 125000000000 : ℝ)
  | 1 => (-108517657217 / 31250000000 : ℝ)
  | 2 => (-1759053819277 / 500000000000 : ℝ)
  | 3 => (-891024428861 / 250000000000 : ℝ)
  | 4 => (-902634667059 / 250000000000 : ℝ)
  | 5 => (-3657433923613 / 1000000000000 : ℝ)
  | 6 => (-1852393464209 / 500000000000 : ℝ)
  | 7 => (-469075143717 / 125000000000 : ℝ)
  | 8 => (-380088007499 / 100000000000 : ℝ)
  | 9 => (-1924813606013 / 500000000000 : ℝ)
  | 10 => (-779769217841 / 200000000000 : ℝ)
  | 11 => (-1974270127747 / 500000000000 : ℝ)
  | 12 => (-1999356640279 / 500000000000 : ℝ)
  | 13 => (-126542773589 / 31250000000 : ℝ)
  | 14 => (-128140946553 / 31250000000 : ℝ)
  | 15 => (-2076070758701 / 500000000000 : ℝ)
  | 16 => (-4204266091333 / 1000000000000 : ℝ)
  | 17 => (-4256887686007 / 1000000000000 : ℝ)
  | 18 => (-2155004998597 / 500000000000 : ℝ)
  | 19 => (-2181818371001 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch051Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1691404348447 / 500000000000 : ℝ)
  | 1 => (-137098660239 / 40000000000 : ℝ)
  | 2 => (-3472565030943 / 1000000000000 : ℝ)
  | 3 => (-3518107638553 / 1000000000000 : ℝ)
  | 4 => (-3564097715443 / 1000000000000 : ℝ)
  | 5 => (-722107733647 / 200000000000 : ℝ)
  | 6 => (-914358480903 / 250000000000 : ℝ)
  | 7 => (-3704786928417 / 1000000000000 : ℝ)
  | 8 => (-750520229947 / 200000000000 : ℝ)
  | 9 => (-3800880074989 / 1000000000000 : ℝ)
  | 10 => (-153985088481 / 40000000000 : ℝ)
  | 11 => (-974711522301 / 250000000000 : ℝ)
  | 12 => (-3948540255493 / 1000000000000 : ℝ)
  | 13 => (-3998713280557 / 1000000000000 : ℝ)
  | 14 => (-4049368754847 / 1000000000000 : ℝ)
  | 15 => (-820102057939 / 200000000000 : ℝ)
  | 16 => (-4152141517401 / 1000000000000 : ℝ)
  | 17 => (-1051066522833 / 250000000000 : ℝ)
  | 18 => (-2128443843003 / 500000000000 : ℝ)
  | 19 => (-4310009997193 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch051Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1020 : ℝ) + (j.val : ℝ)) / 1600)
      (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch051Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch051Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1020 : ℝ) + (j.val : ℝ)) / 1600)
    (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch051Neg100WeightLower j.val) (hpThetaShiftOneBatch051Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch051Neg100WeightLower, hpThetaShiftOneBatch051Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch051Neg100_integral_bounds :
    (-345589154537 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-167252950407 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1020 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch051Lower hpThetaJensenCellsBatch051Upper
    hpThetaShiftOneBatch051Neg100WeightLower hpThetaShiftOneBatch051Neg100WeightUpper hpThetaJensenCellsBatch051_bounds hpThetaShiftOneBatch051Neg100_weight_bounds
  have hl : (-345589154537 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch051Lower j * hpThetaShiftOneBatch051Neg100WeightLower j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftOneBatch051Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftOneBatch051Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch051Lower j * hpThetaShiftOneBatch051Neg100WeightUpper j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftOneBatch051Neg100WeightUpper j) / 1600) ≤ (-167252950407 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftOneBatch051Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1020 : ℝ) / 1600 = 51 / 80 by norm_num,
    show ((1020 : ℝ) + 20) / 1600 = (51 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch051Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (29298896603 / 200000000000 : ℝ)
  | 1 => (142998304801 / 1000000000000 : ℝ)
  | 2 => (139434623463 / 1000000000000 : ℝ)
  | 3 => (212191807 / 1562500000 : ℝ)
  | 4 => (66051008319 / 500000000000 : ℝ)
  | 5 => (128331712013 / 1000000000000 : ℝ)
  | 6 => (124491145941 / 1000000000000 : ℝ)
  | 7 => (120579617003 / 1000000000000 : ℝ)
  | 8 => (58298209497 / 500000000000 : ℝ)
  | 9 => (56270420453 / 500000000000 : ℝ)
  | 10 => (54206083451 / 500000000000 : ℝ)
  | 11 => (104209676293 / 1000000000000 : ℝ)
  | 12 => (24983160879 / 250000000000 : ℝ)
  | 13 => (23895084527 / 250000000000 : ℝ)
  | 14 => (45576012343 / 500000000000 : ℝ)
  | 15 => (86646962921 / 1000000000000 : ℝ)
  | 16 => (41032203757 / 500000000000 : ℝ)
  | 17 => (38701804087 / 500000000000 : ℝ)
  | 18 => (36331904797 / 500000000000 : ℝ)
  | 19 => (67844251427 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch051Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3748095899 / 25000000000 : ℝ)
  | 1 => (18311810377 / 125000000000 : ℝ)
  | 2 => (71499152401 / 500000000000 : ℝ)
  | 3 => (17429327933 / 125000000000 : ℝ)
  | 4 => (135802756481 / 1000000000000 : ℝ)
  | 5 => (132102016639 / 1000000000000 : ℝ)
  | 6 => (64165856007 / 500000000000 : ℝ)
  | 7 => (62245572971 / 500000000000 : ℝ)
  | 8 => (30144904251 / 250000000000 : ℝ)
  | 9 => (23319283799 / 200000000000 : ℝ)
  | 10 => (112540840907 / 1000000000000 : ℝ)
  | 11 => (108412166903 / 1000000000000 : ℝ)
  | 12 => (52104838147 / 500000000000 : ℝ)
  | 13 => (99932643517 / 1000000000000 : ℝ)
  | 14 => (95580338109 / 1000000000000 : ℝ)
  | 15 => (91152024687 / 1000000000000 : ℝ)
  | 16 => (43323481461 / 500000000000 : ℝ)
  | 17 => (16412881503 / 200000000000 : ℝ)
  | 18 => (3096144327 / 40000000000 : ℝ)
  | 19 => (14532761919 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch051Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1020 : ℝ) + (j.val : ℝ)) / 1600)
      (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch051Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch051Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1020 : ℝ) + (j.val : ℝ)) / 1600)
    (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch051Neg65WeightLower j.val) (hpThetaShiftOneBatch051Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch051Neg65WeightLower, hpThetaShiftOneBatch051Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch051Neg65_integral_bounds :
    (19432267951 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (20550923633 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1020 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch051Lower hpThetaJensenCellsBatch051Upper
    hpThetaShiftOneBatch051Neg65WeightLower hpThetaShiftOneBatch051Neg65WeightUpper hpThetaJensenCellsBatch051_bounds hpThetaShiftOneBatch051Neg65_weight_bounds
  have hl : (19432267951 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch051Lower j * hpThetaShiftOneBatch051Neg65WeightLower j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftOneBatch051Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftOneBatch051Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch051Lower j * hpThetaShiftOneBatch051Neg65WeightUpper j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftOneBatch051Neg65WeightUpper j) / 1600) ≤ (20550923633 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftOneBatch051Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1020 : ℝ) / 1600 = 51 / 80 by norm_num,
    show ((1020 : ℝ) + 20) / 1600 = (51 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch051Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (197291895101 / 1000000000000 : ℝ)
  | 1 => (49714451003 / 250000000000 : ℝ)
  | 2 => (5010661863 / 25000000000 : ℝ)
  | 3 => (12624865169 / 62500000000 : ℝ)
  | 4 => (1628574751 / 8000000000 : ℝ)
  | 5 => (6410887893 / 31250000000 : ℝ)
  | 6 => (103363741287 / 500000000000 : ℝ)
  | 7 => (26038623357 / 125000000000 : ℝ)
  | 8 => (1679142861 / 8000000000 : ℝ)
  | 9 => (26434878287 / 125000000000 : ℝ)
  | 10 => (213067423487 / 1000000000000 : ℝ)
  | 11 => (107328989511 / 500000000000 : ℝ)
  | 12 => (108125310959 / 500000000000 : ℝ)
  | 13 => (217845280387 / 1000000000000 : ℝ)
  | 14 => (109720940913 / 500000000000 : ℝ)
  | 15 => (13815022051 / 62500000000 : ℝ)
  | 16 => (44528123823 / 200000000000 : ℝ)
  | 17 => (112121302827 / 500000000000 : ℝ)
  | 18 => (56461559133 / 250000000000 : ℝ)
  | 19 => (227451435011 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch051Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (198857804013 / 1000000000000 : ℝ)
  | 1 => (200426474521 / 1000000000000 : ℝ)
  | 2 => (40399568541 / 200000000000 : ℝ)
  | 3 => (50892960969 / 250000000000 : ℝ)
  | 4 => (205148412577 / 1000000000000 : ℝ)
  | 5 => (8269099303 / 40000000000 : ℝ)
  | 6 => (208308986857 / 1000000000000 : ℝ)
  | 7 => (104946428813 / 500000000000 : ℝ)
  | 8 => (211479026297 / 1000000000000 : ℝ)
  | 9 => (832294623 / 3906250000 : ℝ)
  | 10 => (214657979023 / 1000000000000 : ℝ)
  | 11 => (216250621919 / 1000000000000 : ℝ)
  | 12 => (54461320097 / 250000000000 : ℝ)
  | 13 => (219441881827 / 1000000000000 : ℝ)
  | 14 => (221040352817 / 1000000000000 : ℝ)
  | 15 => (55660154779 / 250000000000 : ℝ)
  | 16 => (44848521131 / 200000000000 : ℝ)
  | 17 => (225846236533 / 1000000000000 : ℝ)
  | 18 => (56862858753 / 250000000000 : ℝ)
  | 19 => (28632265439 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch051Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1020 : ℝ) + (j.val : ℝ)) / 1600)
      (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch051Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch051Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1020 : ℝ) + (j.val : ℝ)) / 1600)
    (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch051Neg40WeightLower j.val) (hpThetaShiftOneBatch051Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch051Neg40WeightLower, hpThetaShiftOneBatch051Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch051Neg40_integral_bounds :
    (9282303929 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (38158154407 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1020 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch051Lower hpThetaJensenCellsBatch051Upper
    hpThetaShiftOneBatch051Neg40WeightLower hpThetaShiftOneBatch051Neg40WeightUpper hpThetaJensenCellsBatch051_bounds hpThetaShiftOneBatch051Neg40_weight_bounds
  have hl : (9282303929 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch051Lower j * hpThetaShiftOneBatch051Neg40WeightLower j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftOneBatch051Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftOneBatch051Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch051Lower j * hpThetaShiftOneBatch051Neg40WeightUpper j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftOneBatch051Neg40WeightUpper j) / 1600) ≤ (38158154407 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftOneBatch051Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1020 : ℝ) / 1600 = 51 / 80 by norm_num,
    show ((1020 : ℝ) + 20) / 1600 = (51 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch051Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-40642937043 / 500000000000 : ℝ)
  | 1 => (-81194722879 / 1000000000000 : ℝ)
  | 2 => (-20275081709 / 250000000000 : ℝ)
  | 3 => (-2531333433 / 31250000000 : ℝ)
  | 4 => (-20225433959 / 250000000000 : ℝ)
  | 5 => (-8079750867 / 100000000000 : ℝ)
  | 6 => (-80689972249 / 1000000000000 : ℝ)
  | 7 => (-16115822093 / 200000000000 : ℝ)
  | 8 => (-80464907207 / 1000000000000 : ℝ)
  | 9 => (-20086836591 / 250000000000 : ℝ)
  | 10 => (-80226411823 / 1000000000000 : ℝ)
  | 11 => (-40051043737 / 500000000000 : ℝ)
  | 12 => (-19993589301 / 250000000000 : ℝ)
  | 13 => (-9980400613 / 125000000000 : ℝ)
  | 14 => (-39854307231 / 500000000000 : ℝ)
  | 15 => (-79570569771 / 1000000000000 : ℝ)
  | 16 => (-3177162189 / 40000000000 : ℝ)
  | 17 => (-39642026609 / 500000000000 : ℝ)
  | 18 => (-1582710983 / 20000000000 : ℝ)
  | 19 => (-78983526421 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch051Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-40597361439 / 500000000000 : ℝ)
  | 1 => (-16220065367 / 200000000000 : ℝ)
  | 2 => (-16200533971 / 200000000000 : ℝ)
  | 3 => (-16180347167 / 200000000000 : ℝ)
  | 4 => (-80797508669 / 1000000000000 : ℝ)
  | 5 => (-10086246531 / 125000000000 : ℝ)
  | 6 => (-1259048601 / 15625000000 : ℝ)
  | 7 => (-40232453603 / 500000000000 : ℝ)
  | 8 => (-80347346363 / 1000000000000 : ℝ)
  | 9 => (-40113205911 / 500000000000 : ℝ)
  | 10 => (-80102087473 / 1000000000000 : ℝ)
  | 11 => (-79974357203 / 1000000000000 : ℝ)
  | 12 => (-79843204903 / 1000000000000 : ℝ)
  | 13 => (-79708614461 / 1000000000000 : ℝ)
  | 14 => (-7957056977 / 100000000000 : ℝ)
  | 15 => (-19857263681 / 250000000000 : ℝ)
  | 16 => (-79284053217 / 1000000000000 : ℝ)
  | 17 => (-79135549149 / 1000000000000 : ℝ)
  | 18 => (-3949176321 / 50000000000 : ℝ)
  | 19 => (-9853496117 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch051Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1020 : ℝ) + (j.val : ℝ)) / 1600)
      (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch051Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch051Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1020 : ℝ) + (j.val : ℝ)) / 1600)
    (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch051Neg20WeightLower j.val) (hpThetaShiftOneBatch051Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch051Neg20WeightLower, hpThetaShiftOneBatch051Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch051Neg20_integral_bounds :
    (-7180293683 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-14056871021 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1020 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch051Lower hpThetaJensenCellsBatch051Upper
    hpThetaShiftOneBatch051Neg20WeightLower hpThetaShiftOneBatch051Neg20WeightUpper hpThetaJensenCellsBatch051_bounds hpThetaShiftOneBatch051Neg20_weight_bounds
  have hl : (-7180293683 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch051Lower j * hpThetaShiftOneBatch051Neg20WeightLower j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftOneBatch051Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftOneBatch051Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch051Lower j * hpThetaShiftOneBatch051Neg20WeightUpper j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftOneBatch051Neg20WeightUpper j) / 1600) ≤ (-14056871021 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftOneBatch051Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1020 : ℝ) / 1600 = 51 / 80 by norm_num,
    show ((1020 : ℝ) + 20) / 1600 = (51 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch051Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch051Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch051Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch051Neg20_integral_bounds
end HodgeProofHP
