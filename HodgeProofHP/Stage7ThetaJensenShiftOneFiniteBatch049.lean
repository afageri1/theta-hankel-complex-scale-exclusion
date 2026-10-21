/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch049

/-! Exact signed weight and batch integral certificates, batch 49 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch049Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-975582917113 / 500000000000 : ℝ)
  | 1 => (-990529710491 / 500000000000 : ℝ)
  | 2 => (-1005638510211 / 500000000000 : ℝ)
  | 3 => (-2041821289781 / 1000000000000 : ℝ)
  | 4 => (-1036347451473 / 500000000000 : ℝ)
  | 5 => (-16436723051 / 7812500000 : ℝ)
  | 6 => (-1067720469971 / 500000000000 : ℝ)
  | 7 => (-2167318795487 / 1000000000000 : ℝ)
  | 8 => (-2199536858421 / 1000000000000 : ℝ)
  | 9 => (-1116048943523 / 500000000000 : ℝ)
  | 10 => (-113250232839 / 50000000000 : ℝ)
  | 11 => (-574564990061 / 250000000000 : ℝ)
  | 12 => (-2331866607337 / 1000000000000 : ℝ)
  | 13 => (-2365827425317 / 1000000000000 : ℝ)
  | 14 => (-600036314721 / 250000000000 : ℝ)
  | 15 => (-486964594051 / 200000000000 : ℝ)
  | 16 => (-617465859813 / 250000000000 : ℝ)
  | 17 => (-1252634781689 / 500000000000 : ℝ)
  | 18 => (-1270522128951 / 500000000000 : ℝ)
  | 19 => (-2577190455937 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch049Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1921593619483 / 1000000000000 : ℝ)
  | 1 => (-78046633369 / 40000000000 : ℝ)
  | 2 => (-1981059420981 / 1000000000000 : ℝ)
  | 3 => (-2011277020421 / 1000000000000 : ℝ)
  | 4 => (-102091064489 / 50000000000 : ℝ)
  | 5 => (-414538980589 / 200000000000 : ℝ)
  | 6 => (-2103900550527 / 1000000000000 : ℝ)
  | 7 => (-2135440939941 / 1000000000000 : ℝ)
  | 8 => (-1083659397743 / 500000000000 : ℝ)
  | 9 => (-109976842921 / 50000000000 : ℝ)
  | 10 => (-446419577409 / 200000000000 : ℝ)
  | 11 => (-2265004656779 / 1000000000000 : ℝ)
  | 12 => (-2298259960243 / 1000000000000 : ℝ)
  | 13 => (-291483325917 / 125000000000 : ℝ)
  | 14 => (-591456856329 / 250000000000 : ℝ)
  | 15 => (-2400145258883 / 1000000000000 : ℝ)
  | 16 => (-1217411485127 / 500000000000 : ℝ)
  | 17 => (-2469863439251 / 1000000000000 : ℝ)
  | 18 => (-2505269563377 / 1000000000000 : ℝ)
  | 19 => (-2541044257901 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch049Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((980 : ℝ) + (j.val : ℝ)) / 1600)
      (((980 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch049Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch049Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((980 : ℝ) + (j.val : ℝ)) / 1600)
    (((980 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch049Neg100WeightLower j.val) (hpThetaShiftOneBatch049Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch049Neg100WeightLower, hpThetaShiftOneBatch049Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch049Neg100_integral_bounds :
    (-619437386639 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-598817019319 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (980 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch049Lower hpThetaJensenCellsBatch049Upper
    hpThetaShiftOneBatch049Neg100WeightLower hpThetaShiftOneBatch049Neg100WeightUpper hpThetaJensenCellsBatch049_bounds hpThetaShiftOneBatch049Neg100_weight_bounds
  have hl : (-619437386639 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch049Lower j * hpThetaShiftOneBatch049Neg100WeightLower j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftOneBatch049Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftOneBatch049Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch049Lower j * hpThetaShiftOneBatch049Neg100WeightUpper j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftOneBatch049Neg100WeightUpper j) / 1600) ≤ (-598817019319 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftOneBatch049Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (980 : ℝ) / 1600 = 49 / 80 by norm_num,
    show ((980 : ℝ) + 20) / 1600 = (49 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch049Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (47653933877 / 200000000000 : ℝ)
  | 1 => (118482532779 / 500000000000 : ℝ)
  | 2 => (58904166389 / 250000000000 : ℝ)
  | 3 => (234223956651 / 1000000000000 : ℝ)
  | 4 => (9311456891 / 40000000000 : ℝ)
  | 5 => (231303541999 / 1000000000000 : ℝ)
  | 6 => (229774791517 / 1000000000000 : ℝ)
  | 7 => (114099821311 / 500000000000 : ℝ)
  | 8 => (56644390797 / 250000000000 : ℝ)
  | 9 => (56227004287 / 250000000000 : ℝ)
  | 10 => (8927618579 / 40000000000 : ℝ)
  | 11 => (55356090291 / 250000000000 : ℝ)
  | 12 => (109804579603 / 500000000000 : ℝ)
  | 13 => (108872153287 / 500000000000 : ℝ)
  | 14 => (215829247197 / 1000000000000 : ℝ)
  | 15 => (13366463809 / 62500000000 : ℝ)
  | 16 => (105923131799 / 500000000000 : ℝ)
  | 17 => (104888603421 / 500000000000 : ℝ)
  | 18 => (207655678233 / 1000000000000 : ℝ)
  | 19 => (102740550591 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch049Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (239530985947 / 1000000000000 : ℝ)
  | 1 => (119134834693 / 500000000000 : ℝ)
  | 2 => (236965065559 / 1000000000000 : ℝ)
  | 3 => (235616665557 / 1000000000000 : ℝ)
  | 4 => (58555989163 / 250000000000 : ℝ)
  | 5 => (58196605569 / 250000000000 : ℝ)
  | 6 => (115651771 / 500000000 : ℝ)
  | 7 => (114887395759 / 500000000000 : ℝ)
  | 8 => (228199642623 / 1000000000000 : ℝ)
  | 9 => (226577563189 / 1000000000000 : ℝ)
  | 10 => (224908017149 / 1000000000000 : ℝ)
  | 11 => (55797616119 / 250000000000 : ℝ)
  | 12 => (44284872233 / 200000000000 : ℝ)
  | 13 => (219609159207 / 1000000000000 : ℝ)
  | 14 => (8709772263 / 40000000000 : ℝ)
  | 15 => (107914623599 / 500000000000 : ℝ)
  | 16 => (42772684189 / 200000000000 : ℝ)
  | 17 => (211846263599 / 1000000000000 : ℝ)
  | 18 => (209777206843 / 1000000000000 : ℝ)
  | 19 => (103827839117 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch049Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((980 : ℝ) + (j.val : ℝ)) / 1600)
      (((980 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch049Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch049Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((980 : ℝ) + (j.val : ℝ)) / 1600)
    (((980 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch049Neg65WeightLower j.val) (hpThetaShiftOneBatch049Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch049Neg65WeightLower, hpThetaShiftOneBatch049Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch049Neg65_integral_bounds :
    (2426083601 / 40000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (3893240871 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (980 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch049Lower hpThetaJensenCellsBatch049Upper
    hpThetaShiftOneBatch049Neg65WeightLower hpThetaShiftOneBatch049Neg65WeightUpper hpThetaJensenCellsBatch049_bounds hpThetaShiftOneBatch049Neg65_weight_bounds
  have hl : (2426083601 / 40000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch049Lower j * hpThetaShiftOneBatch049Neg65WeightLower j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftOneBatch049Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftOneBatch049Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch049Lower j * hpThetaShiftOneBatch049Neg65WeightUpper j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftOneBatch049Neg65WeightUpper j) / 1600) ≤ (3893240871 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftOneBatch049Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (980 : ℝ) / 1600 = 49 / 80 by norm_num,
    show ((980 : ℝ) + 20) / 1600 = (49 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch049Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (34391060949 / 250000000000 : ℝ)
  | 1 => (69487756219 / 500000000000 : ℝ)
  | 2 => (140391522557 / 1000000000000 : ℝ)
  | 3 => (141812237267 / 1000000000000 : ℝ)
  | 4 => (143237619087 / 1000000000000 : ℝ)
  | 5 => (72333814969 / 500000000000 : ℝ)
  | 6 => (146102231137 / 1000000000000 : ℝ)
  | 7 => (73770691699 / 500000000000 : ℝ)
  | 8 => (148985046821 / 1000000000000 : ℝ)
  | 9 => (150433180893 / 1000000000000 : ℝ)
  | 10 => (151885744481 / 1000000000000 : ℝ)
  | 11 => (15334269583 / 100000000000 : ℝ)
  | 12 => (1935049907 / 12500000000 : ℝ)
  | 13 => (156269591657 / 1000000000000 : ℝ)
  | 14 => (78869724737 / 500000000000 : ℝ)
  | 15 => (39803380431 / 250000000000 : ℝ)
  | 16 => (160691763477 / 1000000000000 : ℝ)
  | 17 => (162174129157 / 1000000000000 : ℝ)
  | 18 => (163660572533 / 1000000000000 : ℝ)
  | 19 => (82575523361 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch049Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (138975512439 / 1000000000000 : ℝ)
  | 1 => (70195761279 / 500000000000 : ℝ)
  | 2 => (35453059317 / 250000000000 : ℝ)
  | 3 => (8952351193 / 62500000000 : ℝ)
  | 4 => (144667629939 / 1000000000000 : ℝ)
  | 5 => (73051115569 / 500000000000 : ℝ)
  | 6 => (147541383399 / 1000000000000 : ℝ)
  | 7 => (74492523411 / 500000000000 : ℝ)
  | 8 => (75216590447 / 500000000000 : ℝ)
  | 9 => (75942872241 / 500000000000 : ℝ)
  | 10 => (153342695831 / 1000000000000 : ℝ)
  | 11 => (154803992561 / 1000000000000 : ℝ)
  | 12 => (78134795829 / 500000000000 : ℝ)
  | 13 => (6309577979 / 40000000000 : ℝ)
  | 14 => (6368540869 / 40000000000 : ℝ)
  | 15 => (80345881739 / 500000000000 : ℝ)
  | 16 => (81087064579 / 500000000000 : ℝ)
  | 17 => (81830286267 / 500000000000 : ℝ)
  | 18 => (165151046723 / 1000000000000 : ℝ)
  | 19 => (8332275209 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch049Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((980 : ℝ) + (j.val : ℝ)) / 1600)
      (((980 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch049Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch049Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((980 : ℝ) + (j.val : ℝ)) / 1600)
    (((980 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch049Neg40WeightLower j.val) (hpThetaShiftOneBatch049Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch049Neg40WeightLower, hpThetaShiftOneBatch049Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch049Neg40_integral_bounds :
    (5104743307 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (8406022821 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (980 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch049Lower hpThetaJensenCellsBatch049Upper
    hpThetaShiftOneBatch049Neg40WeightLower hpThetaShiftOneBatch049Neg40WeightUpper hpThetaJensenCellsBatch049_bounds hpThetaShiftOneBatch049Neg40_weight_bounds
  have hl : (5104743307 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch049Lower j * hpThetaShiftOneBatch049Neg40WeightLower j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftOneBatch049Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftOneBatch049Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch049Lower j * hpThetaShiftOneBatch049Neg40WeightUpper j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftOneBatch049Neg40WeightUpper j) / 1600) ≤ (8406022821 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftOneBatch049Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (980 : ℝ) / 1600 = 49 / 80 by norm_num,
    show ((980 : ℝ) + 20) / 1600 = (49 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch049Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-20620203501 / 250000000000 : ℝ)
  | 1 => (-41251859283 / 500000000000 : ℝ)
  | 2 => (-82524000597 / 1000000000000 : ℝ)
  | 3 => (-41270822179 / 500000000000 : ℝ)
  | 4 => (-20639158523 / 250000000000 : ℝ)
  | 5 => (-8256895403 / 100000000000 : ℝ)
  | 6 => (-20644647097 / 250000000000 : ℝ)
  | 7 => (-16517104273 / 200000000000 : ℝ)
  | 8 => (-82589737149 / 1000000000000 : ℝ)
  | 9 => (-41295609957 / 500000000000 : ℝ)
  | 10 => (-41295616893 / 500000000000 : ℝ)
  | 11 => (-41294976909 / 500000000000 : ℝ)
  | 12 => (-8258592301 / 100000000000 : ℝ)
  | 13 => (-10322388953 / 125000000000 : ℝ)
  | 14 => (-82569503781 / 1000000000000 : ℝ)
  | 15 => (-8255708359 / 100000000000 : ℝ)
  | 16 => (-82541835149 / 1000000000000 : ℝ)
  | 17 => (-16504748509 / 200000000000 : ℝ)
  | 18 => (-20625697463 / 250000000000 : ℝ)
  | 19 => (-41239480567 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch049Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-20613825659 / 250000000000 : ℝ)
  | 1 => (-82480814003 / 1000000000000 : ℝ)
  | 2 => (-16500743713 / 200000000000 : ℝ)
  | 3 => (-20631000149 / 250000000000 : ℝ)
  | 4 => (-82541644357 / 1000000000000 : ℝ)
  | 5 => (-82556634091 / 1000000000000 : ℝ)
  | 6 => (-82568954029 / 1000000000000 : ℝ)
  | 7 => (-82578588387 / 1000000000000 : ℝ)
  | 8 => (-20646380341 / 250000000000 : ℝ)
  | 9 => (-20647434287 / 250000000000 : ℝ)
  | 10 => (-82589953817 / 1000000000000 : ℝ)
  | 11 => (-82585923009 / 1000000000000 : ℝ)
  | 12 => (-82579111623 / 1000000000000 : ℝ)
  | 13 => (-4128475189 / 50000000000 : ℝ)
  | 14 => (-82557083589 / 1000000000000 : ℝ)
  | 15 => (-20635458787 / 250000000000 : ℝ)
  | 16 => (-5157733909 / 62500000000 : ℝ)
  | 17 => (-82502789851 / 1000000000000 : ℝ)
  | 18 => (-82478961133 / 1000000000000 : ℝ)
  | 19 => (-20613060111 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch049Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((980 : ℝ) + (j.val : ℝ)) / 1600)
      (((980 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch049Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch049Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((980 : ℝ) + (j.val : ℝ)) / 1600)
    (((980 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch049Neg20WeightLower j.val) (hpThetaShiftOneBatch049Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch049Neg20WeightLower, hpThetaShiftOneBatch049Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch049Neg20_integral_bounds :
    (-22800141501 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (49 / 80 : ℝ) ((49 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-11181655937 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (980 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch049Lower hpThetaJensenCellsBatch049Upper
    hpThetaShiftOneBatch049Neg20WeightLower hpThetaShiftOneBatch049Neg20WeightUpper hpThetaJensenCellsBatch049_bounds hpThetaShiftOneBatch049Neg20_weight_bounds
  have hl : (-22800141501 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch049Lower j * hpThetaShiftOneBatch049Neg20WeightLower j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftOneBatch049Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftOneBatch049Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch049Lower j * hpThetaShiftOneBatch049Neg20WeightUpper j)
        (hpThetaJensenCellsBatch049Upper j * hpThetaShiftOneBatch049Neg20WeightUpper j) / 1600) ≤ (-11181655937 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch049Lower, hpThetaJensenCellsBatch049Upper,
      hpThetaShiftOneBatch049Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (980 : ℝ) / 1600 = 49 / 80 by norm_num,
    show ((980 : ℝ) + 20) / 1600 = (49 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch049Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch049Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch049Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch049Neg20_integral_bounds
end HodgeProofHP
