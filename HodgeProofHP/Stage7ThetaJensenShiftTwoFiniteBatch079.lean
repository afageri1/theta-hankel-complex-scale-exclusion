/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch079

/-! Exact signed weight and batch integral certificates, batch 79 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch079Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-15363263811617 / 1000000000000 : ℝ)
  | 1 => (-7737871879063 / 500000000000 : ℝ)
  | 2 => (-15588948307789 / 1000000000000 : ℝ)
  | 3 => (-3140576305339 / 200000000000 : ℝ)
  | 4 => (-15817547500531 / 1000000000000 : ℝ)
  | 5 => (-3186590066933 / 200000000000 : ℝ)
  | 6 => (-8024547077113 / 500000000000 : ℝ)
  | 7 => (-8082991552091 / 500000000000 : ℝ)
  | 8 => (-8141810674711 / 500000000000 : ℝ)
  | 9 => (-16402013074837 / 1000000000000 : ℝ)
  | 10 => (-8260581242699 / 500000000000 : ℝ)
  | 11 => (-4160268451561 / 250000000000 : ℝ)
  | 12 => (-8380875641377 / 500000000000 : ℝ)
  | 13 => (-4220799795159 / 250000000000 : ℝ)
  | 14 => (-2125677723251 / 125000000000 : ℝ)
  | 15 => (-17128423405477 / 1000000000000 : ℝ)
  | 16 => (-690088334649 / 40000000000 : ℝ)
  | 17 => (-1737678101609 / 100000000000 : ℝ)
  | 18 => (-17502145723651 / 1000000000000 : ℝ)
  | 19 => (-17628306878307 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch079Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3050300884339 / 200000000000 : ℝ)
  | 1 => (-480101994113 / 31250000000 : ℝ)
  | 2 => (-24761190013 / 1600000000 : ℝ)
  | 3 => (-3897237076947 / 250000000000 : ℝ)
  | 4 => (-7851440763347 / 500000000000 : ℝ)
  | 5 => (-1581754750053 / 100000000000 : ℝ)
  | 6 => (-1991618791833 / 125000000000 : ℝ)
  | 7 => (-641963766169 / 40000000000 : ℝ)
  | 8 => (-16165983104181 / 1000000000000 : ℝ)
  | 9 => (-16283621349421 / 1000000000000 : ℝ)
  | 10 => (-4100503268709 / 250000000000 : ℝ)
  | 11 => (-16521162485397 / 1000000000000 : ℝ)
  | 12 => (-16641073806243 / 1000000000000 : ℝ)
  | 13 => (-16761751282753 / 1000000000000 : ℝ)
  | 14 => (-3376639836127 / 200000000000 : ℝ)
  | 15 => (-17005421786007 / 1000000000000 : ℝ)
  | 16 => (-4282105851369 / 250000000000 : ℝ)
  | 17 => (-1078263022889 / 62500000000 : ℝ)
  | 18 => (-17376781016089 / 1000000000000 : ℝ)
  | 19 => (-350042914473 / 20000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch079Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1580 : ℝ) + (j.val : ℝ)) / 1600)
      (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch079Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch079Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1580 : ℝ) + (j.val : ℝ)) / 1600)
    (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch079Neg100WeightLower j.val) (hpThetaShiftTwoBatch079Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch079Neg100WeightLower, hpThetaShiftTwoBatch079Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch079Neg100_integral_bounds :
    (-75237281 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-144350061 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch079Lower hpThetaJensenCellsBatch079Upper
    hpThetaShiftTwoBatch079Neg100WeightLower hpThetaShiftTwoBatch079Neg100WeightUpper hpThetaJensenCellsBatch079_bounds hpThetaShiftTwoBatch079Neg100_weight_bounds
  have hl : (-75237281 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch079Lower j * hpThetaShiftTwoBatch079Neg100WeightLower j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftTwoBatch079Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftTwoBatch079Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch079Lower j * hpThetaShiftTwoBatch079Neg100WeightUpper j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftTwoBatch079Neg100WeightUpper j) / 1600) ≤ (-144350061 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftTwoBatch079Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1580 : ℝ) / 1600 = 79 / 80 by norm_num,
    show ((1580 : ℝ) + 20) / 1600 = (79 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch079Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1317544326091 / 500000000000 : ℝ)
  | 1 => (-2656981993907 / 1000000000000 : ℝ)
  | 2 => (-1339515295391 / 500000000000 : ℝ)
  | 3 => (-1350617690343 / 500000000000 : ℝ)
  | 4 => (-2723597306277 / 1000000000000 : ℝ)
  | 5 => (-2746117315021 / 1000000000000 : ℝ)
  | 6 => (-2768796359207 / 1000000000000 : ℝ)
  | 7 => (-697908848993 / 250000000000 : ℝ)
  | 8 => (-703658846829 / 250000000000 : ℝ)
  | 9 => (-2837797300127 / 1000000000000 : ℝ)
  | 10 => (-1430561053101 / 500000000000 : ℝ)
  | 11 => (-2884610782263 / 1000000000000 : ℝ)
  | 12 => (-1454132154991 / 500000000000 : ℝ)
  | 13 => (-2932083676001 / 1000000000000 : ℝ)
  | 14 => (-2956069871951 / 1000000000000 : ℝ)
  | 15 => (-2980223894477 / 1000000000000 : ℝ)
  | 16 => (-600909349051 / 200000000000 : ℝ)
  | 17 => (-3029039431013 / 1000000000000 : ℝ)
  | 18 => (-1526851481779 / 500000000000 : ℝ)
  | 19 => (-3078538359789 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch079Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1306674816249 / 500000000000 : ℝ)
  | 1 => (-2635088652181 / 1000000000000 : ℝ)
  | 2 => (-1328490996953 / 500000000000 : ℝ)
  | 3 => (-2679030590781 / 1000000000000 : ℝ)
  | 4 => (-540247076137 / 200000000000 : ℝ)
  | 5 => (-680899326569 / 250000000000 : ℝ)
  | 6 => (-137305865751 / 50000000000 : ℝ)
  | 7 => (-1384398179603 / 500000000000 : ℝ)
  | 8 => (-2791635395971 / 1000000000000 : ℝ)
  | 9 => (-562927077463 / 200000000000 : ℝ)
  | 10 => (-1418898650063 / 500000000000 : ℝ)
  | 11 => (-2861122106201 / 1000000000000 : ℝ)
  | 12 => (-1442305391131 / 500000000000 : ℝ)
  | 13 => (-2908264309981 / 1000000000000 : ℝ)
  | 14 => (-733020919 / 250000000 : ℝ)
  | 15 => (-59121397439 / 20000000000 : ℝ)
  | 16 => (-745055973619 / 250000000000 : ℝ)
  | 17 => (-1502273372627 / 500000000000 : ℝ)
  | 18 => (-757259857753 / 250000000000 : ℝ)
  | 19 => (-3053702963557 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch079Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1580 : ℝ) + (j.val : ℝ)) / 1600)
      (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch079Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch079Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1580 : ℝ) + (j.val : ℝ)) / 1600)
    (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch079Neg65WeightLower j.val) (hpThetaShiftTwoBatch079Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch079Neg65WeightLower, hpThetaShiftTwoBatch079Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch079Neg65_integral_bounds :
    (-2603049 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-6236809 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch079Lower hpThetaJensenCellsBatch079Upper
    hpThetaShiftTwoBatch079Neg65WeightLower hpThetaShiftTwoBatch079Neg65WeightUpper hpThetaJensenCellsBatch079_bounds hpThetaShiftTwoBatch079Neg65_weight_bounds
  have hl : (-2603049 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch079Lower j * hpThetaShiftTwoBatch079Neg65WeightLower j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftTwoBatch079Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftTwoBatch079Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch079Lower j * hpThetaShiftTwoBatch079Neg65WeightUpper j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftTwoBatch079Neg65WeightUpper j) / 1600) ≤ (-6236809 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftTwoBatch079Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1580 : ℝ) / 1600 = 79 / 80 by norm_num,
    show ((1580 : ℝ) + 20) / 1600 = (79 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch079Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-22208384773 / 62500000000 : ℝ)
  | 1 => (-359408696787 / 1000000000000 : ℝ)
  | 2 => (-181759158841 / 500000000000 : ℝ)
  | 3 => (-7353265203 / 20000000000 : ℝ)
  | 4 => (-46480470829 / 125000000000 : ℝ)
  | 5 => (-376060080923 / 1000000000000 : ℝ)
  | 6 => (-190156224087 / 500000000000 : ℝ)
  | 7 => (-384601114903 / 1000000000000 : ℝ)
  | 8 => (-388926328993 / 1000000000000 : ℝ)
  | 9 => (-98322084927 / 250000000000 : ℝ)
  | 10 => (-397687397691 / 1000000000000 : ℝ)
  | 11 => (-12566367343 / 31250000000 : ℝ)
  | 12 => (-406597664989 / 1000000000000 : ℝ)
  | 13 => (-411109382561 / 1000000000000 : ℝ)
  | 14 => (-207829581963 / 500000000000 : ℝ)
  | 15 => (-84049453347 / 200000000000 : ℝ)
  | 16 => (-212436975029 / 500000000000 : ℝ)
  | 17 => (-42953947439 / 100000000000 : ℝ)
  | 18 => (-434244101661 / 1000000000000 : ℝ)
  | 19 => (-438988095239 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch079Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-70258891333 / 200000000000 : ℝ)
  | 1 => (-355334156367 / 1000000000000 : ℝ)
  | 2 => (-179704348393 / 500000000000 : ℝ)
  | 3 => (-363518317681 / 1000000000000 : ℝ)
  | 4 => (-367663260149 / 1000000000000 : ℝ)
  | 5 => (-371843766631 / 1000000000000 : ℝ)
  | 6 => (-188030040461 / 500000000000 : ℝ)
  | 7 => (-380312448173 / 1000000000000 : ℝ)
  | 8 => (-192300557451 / 500000000000 : ℝ)
  | 9 => (-12153947781 / 31250000000 : ℝ)
  | 10 => (-393288339707 / 1000000000000 : ℝ)
  | 11 => (-39768739769 / 100000000000 : ℝ)
  | 12 => (-16084950199 / 40000000000 : ℝ)
  | 13 => (-101649416247 / 250000000000 : ℝ)
  | 14 => (-2569433641 / 6250000000 : ℝ)
  | 15 => (-16626366557 / 40000000000 : ℝ)
  | 16 => (-210123633367 / 500000000000 : ℝ)
  | 17 => (-424873950057 / 1000000000000 : ℝ)
  | 18 => (-429539474389 / 1000000000000 : ℝ)
  | 19 => (-21712205083 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch079Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1580 : ℝ) + (j.val : ℝ)) / 1600)
      (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch079Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch079Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1580 : ℝ) + (j.val : ℝ)) / 1600)
    (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch079Neg45WeightLower j.val) (hpThetaShiftTwoBatch079Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch079Neg45WeightLower, hpThetaShiftTwoBatch079Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch079Neg45_integral_bounds :
    (-450749 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-34457 / 10000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch079Lower hpThetaJensenCellsBatch079Upper
    hpThetaShiftTwoBatch079Neg45WeightLower hpThetaShiftTwoBatch079Neg45WeightUpper hpThetaJensenCellsBatch079_bounds hpThetaShiftTwoBatch079Neg45_weight_bounds
  have hl : (-450749 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch079Lower j * hpThetaShiftTwoBatch079Neg45WeightLower j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftTwoBatch079Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftTwoBatch079Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch079Lower j * hpThetaShiftTwoBatch079Neg45WeightUpper j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftTwoBatch079Neg45WeightUpper j) / 1600) ≤ (-34457 / 10000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftTwoBatch079Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1580 : ℝ) / 1600 = 79 / 80 by norm_num,
    show ((1580 : ℝ) + 20) / 1600 = (79 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch079Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2131143189 / 40000000000 : ℝ)
  | 1 => (53504423391 / 1000000000000 : ℝ)
  | 2 => (53729881801 / 1000000000000 : ℝ)
  | 3 => (6744367551 / 125000000000 : ℝ)
  | 4 => (27089792269 / 500000000000 : ℝ)
  | 5 => (6800474923 / 125000000000 : ℝ)
  | 6 => (10925514001 / 200000000000 : ℝ)
  | 7 => (54850881327 / 1000000000000 : ℝ)
  | 8 => (11014743629 / 200000000000 : ℝ)
  | 9 => (27648032557 / 500000000000 : ℝ)
  | 10 => (27758953379 / 500000000000 : ℝ)
  | 11 => (55739227461 / 1000000000000 : ℝ)
  | 12 => (55960011471 / 1000000000000 : ℝ)
  | 13 => (28090121449 / 500000000000 : ℝ)
  | 14 => (28199952857 / 500000000000 : ℝ)
  | 15 => (56618983749 / 1000000000000 : ℝ)
  | 16 => (7104682587 / 125000000000 : ℝ)
  | 17 => (7131915013 / 125000000000 : ℝ)
  | 18 => (2863627269 / 50000000000 : ℝ)
  | 19 => (5748911979 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch079Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1672013231 / 31250000000 : ℝ)
  | 1 => (26864940901 / 500000000000 : ℝ)
  | 2 => (53954940409 / 1000000000000 : ℝ)
  | 3 => (54179584539 / 1000000000000 : ℝ)
  | 4 => (10880759877 / 200000000000 : ℝ)
  | 5 => (27313785003 / 500000000000 : ℝ)
  | 6 => (3428180083 / 62500000000 : ℝ)
  | 7 => (27536859073 / 500000000000 : ℝ)
  | 8 => (11059213023 / 200000000000 : ℝ)
  | 9 => (55517906759 / 1000000000000 : ℝ)
  | 10 => (27869613731 / 500000000000 : ℝ)
  | 11 => (3497500717 / 62500000000 : ℝ)
  | 12 => (56180242899 / 1000000000000 : ℝ)
  | 13 => (11279981143 / 200000000000 : ℝ)
  | 14 => (45295187 / 800000000 : ℝ)
  | 15 => (56837460697 / 1000000000000 : ℝ)
  | 16 => (11411064021 / 200000000000 : ℝ)
  | 17 => (57272545381 / 1000000000000 : ℝ)
  | 18 => (57489119791 / 1000000000000 : ℝ)
  | 19 => (7213128307 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch079Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1580 : ℝ) + (j.val : ℝ)) / 1600)
      (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch079Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch079Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1580 : ℝ) + (j.val : ℝ)) / 1600)
    (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch079Neg25WeightLower j.val) (hpThetaShiftTwoBatch079Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch079Neg25WeightLower, hpThetaShiftTwoBatch079Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch079Neg25_integral_bounds :
    (490297 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (254723 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch079Lower hpThetaJensenCellsBatch079Upper
    hpThetaShiftTwoBatch079Neg25WeightLower hpThetaShiftTwoBatch079Neg25WeightUpper hpThetaJensenCellsBatch079_bounds hpThetaShiftTwoBatch079Neg25_weight_bounds
  have hl : (490297 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch079Lower j * hpThetaShiftTwoBatch079Neg25WeightLower j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftTwoBatch079Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftTwoBatch079Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch079Lower j * hpThetaShiftTwoBatch079Neg25WeightUpper j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftTwoBatch079Neg25WeightUpper j) / 1600) ≤ (254723 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftTwoBatch079Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1580 : ℝ) / 1600 = 79 / 80 by norm_num,
    show ((1580 : ℝ) + 20) / 1600 = (79 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch079Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch079Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch079Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch079Neg25_integral_bounds
end HodgeProofHP
