/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch049

/-! Exact signed weight and batch integral certificates, batch 49 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch049Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1584600067 / 125000000000 : ℝ)
  | 1 => (-13066811961 / 1000000000000 : ℝ)
  | 2 => (-2692672357 / 200000000000 : ℝ)
  | 3 => (-2773306029 / 200000000000 : ℝ)
  | 4 => (-1784549743 / 125000000000 : ℝ)
  | 5 => (-734652343 / 50000000000 : ℝ)
  | 6 => (-15116559347 / 1000000000000 : ℝ)
  | 7 => (-3109403729 / 200000000000 : ℝ)
  | 8 => (-999031799 / 62500000000 : ℝ)
  | 9 => (-513409831 / 31250000000 : ℝ)
  | 10 => (-16880921697 / 1000000000000 : ℝ)
  | 11 => (-17340016537 / 1000000000000 : ℝ)
  | 12 => (-17806486363 / 1000000000000 : ℝ)
  | 13 => (-1142526203 / 62500000000 : ℝ)
  | 14 => (-4690476023 / 250000000000 : ℝ)
  | 15 => (-9625515313 / 500000000000 : ℝ)
  | 16 => (-19747889423 / 1000000000000 : ℝ)
  | 17 => (-20252571897 / 1000000000000 : ℝ)
  | 18 => (-20765170319 / 1000000000000 : ℝ)
  | 19 => (-21285777813 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch049Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6146624067 / 500000000000 : ℝ)
  | 1 => (-2535360107 / 200000000000 : ℝ)
  | 2 => (-326670299 / 25000000000 : ℝ)
  | 3 => (-1682920223 / 125000000000 : ℝ)
  | 4 => (-433329067 / 31250000000 : ℝ)
  | 5 => (-14276397943 / 1000000000000 : ℝ)
  | 6 => (-14693046859 / 1000000000000 : ℝ)
  | 7 => (-7558279673 / 500000000000 : ℝ)
  | 8 => (-3886754661 / 250000000000 : ℝ)
  | 9 => (-15984508783 / 1000000000000 : ℝ)
  | 10 => (-16429114591 / 1000000000000 : ℝ)
  | 11 => (-527528803 / 31250000000 : ℝ)
  | 12 => (-2167502067 / 125000000000 : ℝ)
  | 13 => (-8903243181 / 500000000000 : ℝ)
  | 14 => (-18280419247 / 1000000000000 : ℝ)
  | 15 => (-18761904091 / 1000000000000 : ℝ)
  | 16 => (-30801649 / 1600000000 : ℝ)
  | 17 => (-9873944711 / 500000000000 : ℝ)
  | 18 => (-2531571487 / 125000000000 : ℝ)
  | 19 => (-10382585159 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch049Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((980 : ℝ) + (j.val : ℝ)) / 1600)
      (((980 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch049Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch049Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((980 : ℝ) + (j.val : ℝ)) / 1600)
    (((980 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch049Neg100WeightLower j.val) (hpThetaShiftTwoBatch049Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch049Neg100WeightLower, hpThetaShiftTwoBatch049Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch049Neg100_integral_bounds :
    (-1147344059 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-4380988843 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (980 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch049Lower hpThetaJensenCellsBatch049Upper
    hpThetaShiftTwoBatch049Neg100WeightLower hpThetaShiftTwoBatch049Neg100WeightUpper hpThetaJensenCellsBatch049_bounds hpThetaShiftTwoBatch049Neg100_weight_bounds
  have hl : (-1147344059 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch049Lower j * hpThetaShiftTwoBatch049Neg100WeightLower j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftTwoBatch049Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftTwoBatch049Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch049Lower j * hpThetaShiftTwoBatch049Neg100WeightUpper j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftTwoBatch049Neg100WeightUpper j) / 1600) ≤ (-4380988843 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftTwoBatch049Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (980 : ℝ) / 1600 = 49 / 80 by norm_num,
    show ((980 : ℝ) + 20) / 1600 = (49 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch049Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3944108557 / 500000000000 : ℝ)
  | 1 => (3971020339 / 500000000000 : ℝ)
  | 2 => (1599142301 / 200000000000 : ℝ)
  | 3 => (4024610241 / 500000000000 : ℝ)
  | 4 => (8102558367 / 1000000000000 : ℝ)
  | 5 => (4077857891 / 500000000000 : ℝ)
  | 6 => (513042701 / 62500000000 : ℝ)
  | 7 => (8261451021 / 1000000000000 : ℝ)
  | 8 => (8314009413 / 1000000000000 : ℝ)
  | 9 => (8366348469 / 1000000000000 : ℝ)
  | 10 => (13469533 / 1600000000 : ℝ)
  | 11 => (8470328177 / 1000000000000 : ℝ)
  | 12 => (213048707 / 25000000000 : ℝ)
  | 13 => (1071663493 / 125000000000 : ℝ)
  | 14 => (8624396533 / 1000000000000 : ℝ)
  | 15 => (2168800817 / 250000000000 : ℝ)
  | 16 => (4362858609 / 500000000000 : ℝ)
  | 17 => (2193981827 / 250000000000 : ℝ)
  | 18 => (8825822309 / 1000000000000 : ℝ)
  | 19 => (8875390841 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch049Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (7942040679 / 1000000000000 : ℝ)
  | 1 => (3997855753 / 500000000000 : ℝ)
  | 2 => (8049220483 / 1000000000000 : ℝ)
  | 3 => (253204949 / 31250000000 : ℝ)
  | 4 => (8155715783 / 1000000000000 : ℝ)
  | 5 => (8208683217 / 1000000000000 : ℝ)
  | 6 => (4130725511 / 500000000000 : ℝ)
  | 7 => (4157004707 / 500000000000 : ℝ)
  | 8 => (836634847 / 100000000000 : ℝ)
  | 9 => (4209229063 / 500000000000 : ℝ)
  | 10 => (4235164089 / 500000000000 : ℝ)
  | 11 => (8521948281 / 1000000000000 : ℝ)
  | 12 => (1714661589 / 200000000000 : ℝ)
  | 13 => (4312198267 / 500000000000 : ℝ)
  | 14 => (8675203269 / 1000000000000 : ℝ)
  | 15 => (8725717219 / 1000000000000 : ℝ)
  | 16 => (8775927309 / 1000000000000 : ℝ)
  | 17 => (882582231 / 100000000000 : ℝ)
  | 18 => (4437695421 / 500000000000 : ℝ)
  | 19 => (4462310687 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch049Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((980 : ℝ) + (j.val : ℝ)) / 1600)
      (((980 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch049Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch049Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((980 : ℝ) + (j.val : ℝ)) / 1600)
    (((980 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch049Neg65WeightLower j.val) (hpThetaShiftTwoBatch049Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch049Neg65WeightLower, hpThetaShiftTwoBatch049Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch049Neg65_integral_bounds :
    (1133947769 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (1163076793 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (980 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch049Lower hpThetaJensenCellsBatch049Upper
    hpThetaShiftTwoBatch049Neg65WeightLower hpThetaShiftTwoBatch049Neg65WeightUpper hpThetaJensenCellsBatch049_bounds hpThetaShiftTwoBatch049Neg65_weight_bounds
  have hl : (1133947769 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch049Lower j * hpThetaShiftTwoBatch049Neg65WeightLower j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftTwoBatch049Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftTwoBatch049Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch049Lower j * hpThetaShiftTwoBatch049Neg65WeightUpper j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftTwoBatch049Neg65WeightUpper j) / 1600) ≤ (1163076793 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftTwoBatch049Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (980 : ℝ) / 1600 = 49 / 80 by norm_num,
    show ((980 : ℝ) + 20) / 1600 = (49 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch049Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (781705813 / 500000000000 : ℝ)
  | 1 => (802006101 / 500000000000 : ℝ)
  | 2 => (164498309 / 100000000000 : ℝ)
  | 3 => (843162717 / 500000000000 : ℝ)
  | 4 => (1728040361 / 1000000000000 : ℝ)
  | 5 => (221266123 / 125000000000 : ℝ)
  | 6 => (1812592401 / 1000000000000 : ℝ)
  | 7 => (1855431691 / 1000000000000 : ℝ)
  | 8 => (1898647919 / 1000000000000 : ℝ)
  | 9 => (971121067 / 500000000000 : ℝ)
  | 10 => (496553841 / 250000000000 : ℝ)
  | 11 => (16244549 / 8000000000 : ℝ)
  | 12 => (2075302911 / 1000000000000 : ℝ)
  | 13 => (1060209601 / 500000000000 : ℝ)
  | 14 => (270739807 / 125000000000 : ℝ)
  | 15 => (442360323 / 200000000000 : ℝ)
  | 16 => (1129034801 / 500000000000 : ℝ)
  | 17 => (1152361661 / 500000000000 : ℝ)
  | 18 => (1175881829 / 500000000000 : ℝ)
  | 19 => (599797869 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch049Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1604012203 / 1000000000000 : ℝ)
  | 1 => (1644983091 / 1000000000000 : ℝ)
  | 2 => (337265087 / 200000000000 : ℝ)
  | 3 => (864020181 / 500000000000 : ℝ)
  | 4 => (354025797 / 200000000000 : ℝ)
  | 5 => (906296201 / 500000000000 : ℝ)
  | 6 => (463857923 / 250000000000 : ℝ)
  | 7 => (23733099 / 12500000000 : ℝ)
  | 8 => (388448427 / 200000000000 : ℝ)
  | 9 => (397243073 / 200000000000 : ℝ)
  | 10 => (1015284313 / 500000000000 : ℝ)
  | 11 => (2026663 / 976562500 : ℝ)
  | 12 => (2120419203 / 1000000000000 : ℝ)
  | 13 => (2165918457 / 1000000000000 : ℝ)
  | 14 => (138237601 / 62500000000 : ℝ)
  | 15 => (2258069603 / 1000000000000 : ℝ)
  | 16 => (2304723323 / 1000000000000 : ℝ)
  | 17 => (2351763659 / 1000000000000 : ℝ)
  | 18 => (2399191477 / 1000000000000 : ℝ)
  | 19 => (1223503811 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch049Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((980 : ℝ) + (j.val : ℝ)) / 1600)
      (((980 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch049Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch049Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((980 : ℝ) + (j.val : ℝ)) / 1600)
    (((980 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch049Neg45WeightLower j.val) (hpThetaShiftTwoBatch049Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch049Neg45WeightLower, hpThetaShiftTwoBatch049Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch049Neg45_integral_bounds :
    (529727039 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (138039149 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (980 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch049Lower hpThetaJensenCellsBatch049Upper
    hpThetaShiftTwoBatch049Neg45WeightLower hpThetaShiftTwoBatch049Neg45WeightUpper hpThetaJensenCellsBatch049_bounds hpThetaShiftTwoBatch049Neg45_weight_bounds
  have hl : (529727039 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch049Lower j * hpThetaShiftTwoBatch049Neg45WeightLower j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftTwoBatch049Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftTwoBatch049Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch049Lower j * hpThetaShiftTwoBatch049Neg45WeightUpper j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftTwoBatch049Neg45WeightUpper j) / 1600) ≤ (138039149 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftTwoBatch049Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (980 : ℝ) / 1600 = 49 / 80 by norm_num,
    show ((980 : ℝ) + 20) / 1600 = (49 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch049Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3016701977 / 1000000000000 : ℝ)
  | 1 => (-3029514781 / 1000000000000 : ℝ)
  | 2 => (-1521140257 / 500000000000 : ℝ)
  | 3 => (-305499811 / 100000000000 : ℝ)
  | 4 => (-6135333 / 2000000000 : ℝ)
  | 5 => (-3080284607 / 1000000000000 : ℝ)
  | 6 => (-773212837 / 250000000000 : ℝ)
  | 7 => (-24260669 / 7812500000 : ℝ)
  | 8 => (-1558913181 / 500000000000 : ℝ)
  | 9 => (-1565116217 / 500000000000 : ℝ)
  | 10 => (-3142582737 / 1000000000000 : ℝ)
  | 11 => (-630975231 / 200000000000 : ℝ)
  | 12 => (-1583555781 / 500000000000 : ℝ)
  | 13 => (-3179287827 / 1000000000000 : ℝ)
  | 14 => (-3191403813 / 1000000000000 : ℝ)
  | 15 => (-25627667 / 8000000000 : ℝ)
  | 16 => (-80386259 / 25000000000 : ℝ)
  | 17 => (-806844653 / 250000000000 : ℝ)
  | 18 => (-3239241963 / 1000000000000 : ℝ)
  | 19 => (-3251039243 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch049Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-600768631 / 200000000000 : ℝ)
  | 1 => (-377087747 / 125000000000 : ℝ)
  | 2 => (-151475739 / 50000000000 : ℝ)
  | 3 => (-3042280513 / 1000000000000 : ℝ)
  | 4 => (-3054998109 / 1000000000000 : ℝ)
  | 5 => (-3067666499 / 1000000000000 : ℝ)
  | 6 => (-1540142303 / 500000000000 : ℝ)
  | 7 => (-3092851347 / 1000000000000 : ℝ)
  | 8 => (-3105365631 / 1000000000000 : ℝ)
  | 9 => (-3117826361 / 1000000000000 : ℝ)
  | 10 => (-3130232433 / 1000000000000 : ℝ)
  | 11 => (-196411421 / 62500000000 : ℝ)
  | 12 => (-1577438077 / 500000000000 : ℝ)
  | 13 => (-3167111561 / 1000000000000 : ℝ)
  | 14 => (-1589643913 / 500000000000 : ℝ)
  | 15 => (-797850953 / 250000000000 : ℝ)
  | 16 => (-1601729187 / 500000000000 : ℝ)
  | 17 => (-3215450359 / 1000000000000 : ℝ)
  | 18 => (-3227378611 / 1000000000000 : ℝ)
  | 19 => (-1619620981 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch049Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((980 : ℝ) + (j.val : ℝ)) / 1600)
      (((980 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch049Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch049Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((980 : ℝ) + (j.val : ℝ)) / 1600)
    (((980 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch049Neg25WeightLower j.val) (hpThetaShiftTwoBatch049Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch049Neg25WeightLower, hpThetaShiftTwoBatch049Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch049Neg25_integral_bounds :
    (-864800823 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-8450173 / 10000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (980 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch049Lower hpThetaJensenCellsBatch049Upper
    hpThetaShiftTwoBatch049Neg25WeightLower hpThetaShiftTwoBatch049Neg25WeightUpper hpThetaJensenCellsBatch049_bounds hpThetaShiftTwoBatch049Neg25_weight_bounds
  have hl : (-864800823 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch049Lower j * hpThetaShiftTwoBatch049Neg25WeightLower j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftTwoBatch049Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftTwoBatch049Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch049Lower j * hpThetaShiftTwoBatch049Neg25WeightUpper j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftTwoBatch049Neg25WeightUpper j) / 1600) ≤ (-8450173 / 10000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftTwoBatch049Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (980 : ℝ) / 1600 = 49 / 80 by norm_num,
    show ((980 : ℝ) + 20) / 1600 = (49 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch049Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch049Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch049Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch049Neg25_integral_bounds
end HodgeProofHP
