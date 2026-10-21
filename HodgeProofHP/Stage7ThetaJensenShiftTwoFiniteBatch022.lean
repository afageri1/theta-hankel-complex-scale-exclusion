/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch022

/-! Exact signed weight and batch integral certificates, batch 22 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch022Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-52025857 / 500000000000 : ℝ)
  | 1 => (-105713451 / 1000000000000 : ℝ)
  | 2 => (-107381819 / 1000000000000 : ℝ)
  | 3 => (-54528291 / 500000000000 : ℝ)
  | 4 => (-55368749 / 500000000000 : ℝ)
  | 5 => (-175663 / 1562500000 : ℝ)
  | 6 => (-28529199 / 250000000000 : ℝ)
  | 7 => (-28953667 / 250000000000 : ℝ)
  | 8 => (-117517673 / 1000000000000 : ℝ)
  | 9 => (-14903193 / 125000000000 : ℝ)
  | 10 => (-60469003 / 500000000000 : ℝ)
  | 11 => (-6132739 / 50000000000 : ℝ)
  | 12 => (-124375581 / 1000000000000 : ℝ)
  | 13 => (-126100119 / 1000000000000 : ℝ)
  | 14 => (-63914049 / 500000000000 : ℝ)
  | 15 => (-8097451 / 62500000000 : ℝ)
  | 16 => (-26258633 / 200000000000 : ℝ)
  | 17 => (-133029633 / 1000000000000 : ℝ)
  | 18 => (-1347683 / 10000000000 : ℝ)
  | 19 => (-136508843 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch022Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-51198419 / 500000000000 : ℝ)
  | 1 => (-104051713 / 1000000000000 : ℝ)
  | 2 => (-2114269 / 20000000000 : ℝ)
  | 3 => (-53690909 / 500000000000 : ℝ)
  | 4 => (-109056581 / 1000000000000 : ℝ)
  | 5 => (-110737497 / 1000000000000 : ℝ)
  | 6 => (-112424319 / 1000000000000 : ℝ)
  | 7 => (-22823359 / 200000000000 : ℝ)
  | 8 => (-115814667 / 1000000000000 : ℝ)
  | 9 => (-14689709 / 125000000000 : ℝ)
  | 10 => (-119225543 / 1000000000000 : ℝ)
  | 11 => (-24187601 / 200000000000 : ℝ)
  | 12 => (-122654779 / 1000000000000 : ℝ)
  | 13 => (-6218779 / 50000000000 : ℝ)
  | 14 => (-63050059 / 500000000000 : ℝ)
  | 15 => (-127828097 / 1000000000000 : ℝ)
  | 16 => (-25911843 / 200000000000 : ℝ)
  | 17 => (-32823291 / 250000000000 : ℝ)
  | 18 => (-519647 / 3906250000 : ℝ)
  | 19 => (-134768299 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch022Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((440 : ℝ) + (j.val : ℝ)) / 1600)
      (((440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch022Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch022Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((440 : ℝ) + (j.val : ℝ)) / 1600)
    (((440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch022Neg100WeightLower j.val) (hpThetaShiftTwoBatch022Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch022Neg100WeightLower, hpThetaShiftTwoBatch022Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch022Neg100_integral_bounds :
    (-248259413 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-75505033 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch022Lower hpThetaJensenCellsBatch022Upper
    hpThetaShiftTwoBatch022Neg100WeightLower hpThetaShiftTwoBatch022Neg100WeightUpper hpThetaJensenCellsBatch022_bounds hpThetaShiftTwoBatch022Neg100_weight_bounds
  have hl : (-248259413 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch022Lower j * hpThetaShiftTwoBatch022Neg100WeightLower j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftTwoBatch022Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftTwoBatch022Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch022Lower j * hpThetaShiftTwoBatch022Neg100WeightUpper j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftTwoBatch022Neg100WeightUpper j) / 1600) ≤ (-75505033 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftTwoBatch022Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (440 : ℝ) / 1600 = 22 / 80 by norm_num,
    show ((440 : ℝ) + 20) / 1600 = (22 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch022Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3207451 / 1000000000000 : ℝ)
  | 1 => (-225513 / 50000000000 : ℝ)
  | 2 => (-2915821 / 500000000000 : ℝ)
  | 3 => (-3585831 / 500000000000 : ℝ)
  | 4 => (-853039 / 100000000000 : ℝ)
  | 5 => (-619243 / 62500000000 : ℝ)
  | 6 => (-11304221 / 1000000000000 : ℝ)
  | 7 => (-12719449 / 1000000000000 : ℝ)
  | 8 => (-442301 / 31250000000 : ℝ)
  | 9 => (-3901707 / 250000000000 : ℝ)
  | 10 => (-4269773 / 250000000000 : ℝ)
  | 11 => (-18570479 / 1000000000000 : ℝ)
  | 12 => (-20081041 / 1000000000000 : ℝ)
  | 13 => (-21610827 / 1000000000000 : ℝ)
  | 14 => (-4631977 / 200000000000 : ℝ)
  | 15 => (-24728263 / 1000000000000 : ℝ)
  | 16 => (-26316003 / 1000000000000 : ℝ)
  | 17 => (-6980787 / 250000000000 : ℝ)
  | 18 => (-14774869 / 500000000000 : ℝ)
  | 19 => (-3119581 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch022Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1923141 / 1000000000000 : ℝ)
  | 1 => (-64149 / 20000000000 : ℝ)
  | 2 => (-4510259 / 1000000000000 : ℝ)
  | 3 => (-5831641 / 1000000000000 : ℝ)
  | 4 => (-7171661 / 1000000000000 : ℝ)
  | 5 => (-8530389 / 1000000000000 : ℝ)
  | 6 => (-9907887 / 1000000000000 : ℝ)
  | 7 => (-565211 / 50000000000 : ℝ)
  | 8 => (-1589931 / 125000000000 : ℝ)
  | 9 => (-14153631 / 1000000000000 : ℝ)
  | 10 => (-15606827 / 1000000000000 : ℝ)
  | 11 => (-17079091 / 1000000000000 : ℝ)
  | 12 => (-9285239 / 500000000000 : ℝ)
  | 13 => (-251013 / 12500000000 : ℝ)
  | 14 => (-10805413 / 500000000000 : ℝ)
  | 15 => (-5789971 / 250000000000 : ℝ)
  | 16 => (-12364131 / 500000000000 : ℝ)
  | 17 => (-13158001 / 500000000000 : ℝ)
  | 18 => (-27923147 / 1000000000000 : ℝ)
  | 19 => (-29549737 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch022Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((440 : ℝ) + (j.val : ℝ)) / 1600)
      (((440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch022Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch022Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((440 : ℝ) + (j.val : ℝ)) / 1600)
    (((440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch022Neg65WeightLower j.val) (hpThetaShiftTwoBatch022Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch022Neg65WeightLower, hpThetaShiftTwoBatch022Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch022Neg65_integral_bounds :
    (-170555603 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-153451591 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch022Lower hpThetaJensenCellsBatch022Upper
    hpThetaShiftTwoBatch022Neg65WeightLower hpThetaShiftTwoBatch022Neg65WeightUpper hpThetaJensenCellsBatch022_bounds hpThetaShiftTwoBatch022Neg65_weight_bounds
  have hl : (-170555603 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch022Lower j * hpThetaShiftTwoBatch022Neg65WeightLower j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftTwoBatch022Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftTwoBatch022Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch022Lower j * hpThetaShiftTwoBatch022Neg65WeightUpper j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftTwoBatch022Neg65WeightUpper j) / 1600) ≤ (-153451591 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftTwoBatch022Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (440 : ℝ) / 1600 = 22 / 80 by norm_num,
    show ((440 : ℝ) + 20) / 1600 = (22 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch022Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (10051501 / 100000000000 : ℝ)
  | 1 => (100170833 / 1000000000000 : ℝ)
  | 2 => (79849 / 800000000 : ℝ)
  | 3 => (99436113 / 1000000000000 : ℝ)
  | 4 => (49522637 / 500000000000 : ℝ)
  | 5 => (49319293 / 500000000000 : ℝ)
  | 6 => (98215901 / 1000000000000 : ℝ)
  | 7 => (9777707 / 100000000000 : ℝ)
  | 8 => (48660973 / 500000000000 : ℝ)
  | 9 => (48425191 / 500000000000 : ℝ)
  | 10 => (96362229 / 1000000000000 : ℝ)
  | 11 => (95857341 / 1000000000000 : ℝ)
  | 12 => (95335569 / 1000000000000 : ℝ)
  | 13 => (94796767 / 1000000000000 : ℝ)
  | 14 => (47120393 / 500000000000 : ℝ)
  | 15 => (93667479 / 1000000000000 : ℝ)
  | 16 => (93076701 / 1000000000000 : ℝ)
  | 17 => (92468303 / 1000000000000 : ℝ)
  | 18 => (91842139 / 1000000000000 : ℝ)
  | 19 => (91198063 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch022Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (10084393 / 100000000000 : ℝ)
  | 1 => (100515011 / 1000000000000 : ℝ)
  | 2 => (50085417 / 500000000000 : ℝ)
  | 3 => (99811251 / 1000000000000 : ℝ)
  | 4 => (49718057 / 500000000000 : ℝ)
  | 5 => (3961811 / 40000000000 : ℝ)
  | 6 => (98638587 / 1000000000000 : ℝ)
  | 7 => (49107951 / 500000000000 : ℝ)
  | 8 => (97777071 / 1000000000000 : ℝ)
  | 9 => (97321947 / 1000000000000 : ℝ)
  | 10 => (96850383 / 1000000000000 : ℝ)
  | 11 => (9636223 / 100000000000 : ℝ)
  | 12 => (47928671 / 500000000000 : ℝ)
  | 13 => (9533557 / 100000000000 : ℝ)
  | 14 => (2962399 / 31250000000 : ℝ)
  | 15 => (94240787 / 1000000000000 : ℝ)
  | 16 => (2341687 / 25000000000 : ℝ)
  | 17 => (46538351 / 500000000000 : ℝ)
  | 18 => (5779269 / 62500000000 : ℝ)
  | 19 => (4592107 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch022Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((440 : ℝ) + (j.val : ℝ)) / 1600)
      (((440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch022Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch022Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((440 : ℝ) + (j.val : ℝ)) / 1600)
    (((440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch022Neg45WeightLower j.val) (hpThetaShiftTwoBatch022Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch022Neg45WeightLower, hpThetaShiftTwoBatch022Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch022Neg45_integral_bounds :
    (123100297 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (62653847 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch022Lower hpThetaJensenCellsBatch022Upper
    hpThetaShiftTwoBatch022Neg45WeightLower hpThetaShiftTwoBatch022Neg45WeightUpper hpThetaJensenCellsBatch022_bounds hpThetaShiftTwoBatch022Neg45_weight_bounds
  have hl : (123100297 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch022Lower j * hpThetaShiftTwoBatch022Neg45WeightLower j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftTwoBatch022Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftTwoBatch022Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch022Lower j * hpThetaShiftTwoBatch022Neg45WeightUpper j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftTwoBatch022Neg45WeightUpper j) / 1600) ≤ (62653847 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftTwoBatch022Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (440 : ℝ) / 1600 = 22 / 80 by norm_num,
    show ((440 : ℝ) + 20) / 1600 = (22 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch022Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (120751647 / 500000000000 : ℝ)
  | 1 => (242783283 / 1000000000000 : ℝ)
  | 2 => (30507597 / 125000000000 : ℝ)
  | 3 => (245335659 / 1000000000000 : ℝ)
  | 4 => (49321563 / 200000000000 : ℝ)
  | 5 => (24787713 / 100000000000 : ℝ)
  | 6 => (49828697 / 200000000000 : ℝ)
  | 7 => (62601691 / 250000000000 : ℝ)
  | 8 => (251666847 / 1000000000000 : ℝ)
  | 9 => (126461807 / 500000000000 : ℝ)
  | 10 => (127088473 / 500000000000 : ℝ)
  | 11 => (255426721 / 1000000000000 : ℝ)
  | 12 => (128336409 / 500000000000 : ℝ)
  | 13 => (257915113 / 1000000000000 : ℝ)
  | 14 => (64788371 / 250000000000 : ℝ)
  | 15 => (65096951 / 250000000000 : ℝ)
  | 16 => (5232359 / 20000000000 : ℝ)
  | 17 => (65710949 / 250000000000 : ℝ)
  | 18 => (264065213 / 1000000000000 : ℝ)
  | 19 => (66320519 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch022Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (60695821 / 250000000000 : ℝ)
  | 1 => (244060777 / 1000000000000 : ℝ)
  | 2 => (12266783 / 50000000000 : ℝ)
  | 3 => (30825977 / 125000000000 : ℝ)
  | 4 => (247877131 / 1000000000000 : ℝ)
  | 5 => (124571743 / 500000000000 : ℝ)
  | 6 => (50081353 / 200000000000 : ℝ)
  | 7 => (7864589 / 31250000000 : ℝ)
  | 8 => (50584723 / 200000000000 : ℝ)
  | 9 => (254176947 / 1000000000000 : ℝ)
  | 10 => (127713361 / 500000000000 : ℝ)
  | 11 => (256672819 / 1000000000000 : ℝ)
  | 12 => (128957557 / 500000000000 : ℝ)
  | 13 => (51830697 / 200000000000 : ℝ)
  | 14 => (52077561 / 200000000000 : ℝ)
  | 15 => (261617951 / 1000000000000 : ℝ)
  | 16 => (262843797 / 1000000000000 : ℝ)
  | 17 => (132032607 / 500000000000 : ℝ)
  | 18 => (265282077 / 1000000000000 : ℝ)
  | 19 => (16655891 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch022Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((440 : ℝ) + (j.val : ℝ)) / 1600)
      (((440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch022Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch022Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((440 : ℝ) + (j.val : ℝ)) / 1600)
    (((440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch022Neg25WeightLower j.val) (hpThetaShiftTwoBatch022Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch022Neg25WeightLower, hpThetaShiftTwoBatch022Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch022Neg25_integral_bounds :
    (2588351371 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (1317321669 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch022Lower hpThetaJensenCellsBatch022Upper
    hpThetaShiftTwoBatch022Neg25WeightLower hpThetaShiftTwoBatch022Neg25WeightUpper hpThetaJensenCellsBatch022_bounds hpThetaShiftTwoBatch022Neg25_weight_bounds
  have hl : (2588351371 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch022Lower j * hpThetaShiftTwoBatch022Neg25WeightLower j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftTwoBatch022Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftTwoBatch022Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch022Lower j * hpThetaShiftTwoBatch022Neg25WeightUpper j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftTwoBatch022Neg25WeightUpper j) / 1600) ≤ (1317321669 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftTwoBatch022Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (440 : ℝ) / 1600 = 22 / 80 by norm_num,
    show ((440 : ℝ) + 20) / 1600 = (22 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch022Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch022Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch022Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch022Neg25_integral_bounds
end HodgeProofHP
