/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch035

/-! Exact signed weight and batch integral certificates, batch 35 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch035Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (13395916329 / 100000000000 : ℝ)
  | 1 => (134891654769 / 1000000000000 : ℝ)
  | 2 => (16977237087 / 125000000000 : ℝ)
  | 3 => (13673765107 / 100000000000 : ℝ)
  | 4 => (8603167299 / 62500000000 : ℝ)
  | 5 => (17319591201 / 125000000000 : ℝ)
  | 6 => (34863890539 / 250000000000 : ℝ)
  | 7 => (35086730967 / 250000000000 : ℝ)
  | 8 => (141230560981 / 1000000000000 : ℝ)
  | 9 => (142106216503 / 1000000000000 : ℝ)
  | 10 => (142973630191 / 1000000000000 : ℝ)
  | 11 => (35958134631 / 250000000000 : ℝ)
  | 12 => (5787306987 / 40000000000 : ℝ)
  | 13 => (18190471061 / 125000000000 : ℝ)
  | 14 => (146355546453 / 1000000000000 : ℝ)
  | 15 => (36794432919 / 250000000000 : ℝ)
  | 16 => (147990043857 / 1000000000000 : ℝ)
  | 17 => (148792199259 / 1000000000000 : ℝ)
  | 18 => (4674497209 / 31250000000 : ℝ)
  | 19 => (7518244373 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch035Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (13489165477 / 100000000000 : ℝ)
  | 1 => (135817896697 / 1000000000000 : ℝ)
  | 2 => (136737651071 / 1000000000000 : ℝ)
  | 3 => (27530135357 / 200000000000 : ℝ)
  | 4 => (138556729609 / 1000000000000 : ℝ)
  | 5 => (139455562157 / 1000000000000 : ℝ)
  | 6 => (140346923869 / 1000000000000 : ℝ)
  | 7 => (70615280491 / 500000000000 : ℝ)
  | 8 => (17763277063 / 125000000000 : ℝ)
  | 9 => (8935851887 / 62500000000 : ℝ)
  | 10 => (5753301541 / 40000000000 : ℝ)
  | 11 => (36170668669 / 250000000000 : ℝ)
  | 12 => (145523768489 / 1000000000000 : ℝ)
  | 13 => (73177773227 / 500000000000 : ℝ)
  | 14 => (147177731677 / 1000000000000 : ℝ)
  | 15 => (73995021929 / 500000000000 : ℝ)
  | 16 => (7439609963 / 50000000000 : ℝ)
  | 17 => (149583910689 / 1000000000000 : ℝ)
  | 18 => (150364887461 / 1000000000000 : ℝ)
  | 19 => (7556741769 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch035Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((700 : ℝ) + (j.val : ℝ)) / 1600)
      (((700 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch035Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch035Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((700 : ℝ) + (j.val : ℝ)) / 1600)
    (((700 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch035Neg100WeightLower j.val) (hpThetaShiftOneBatch035Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch035Neg100WeightLower, hpThetaShiftOneBatch035Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch035Neg100_integral_bounds :
    (40064015721 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (409274988101 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (700 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch035Lower hpThetaJensenCellsBatch035Upper
    hpThetaShiftOneBatch035Neg100WeightLower hpThetaShiftOneBatch035Neg100WeightUpper hpThetaJensenCellsBatch035_bounds hpThetaShiftOneBatch035Neg100_weight_bounds
  have hl : (40064015721 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch035Lower j * hpThetaShiftOneBatch035Neg100WeightLower j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftOneBatch035Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftOneBatch035Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch035Lower j * hpThetaShiftOneBatch035Neg100WeightUpper j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftOneBatch035Neg100WeightUpper j) / 1600) ≤ (409274988101 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftOneBatch035Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (700 : ℝ) / 1600 = 35 / 80 by norm_num,
    show ((700 : ℝ) + 20) / 1600 = (35 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch035Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4328114777 / 200000000000 : ℝ)
  | 1 => (22356321263 / 1000000000000 : ℝ)
  | 2 => (23078154613 / 1000000000000 : ℝ)
  | 3 => (4761215149 / 200000000000 : ℝ)
  | 4 => (3067510747 / 125000000000 : ℝ)
  | 5 => (25280186119 / 1000000000000 : ℝ)
  | 6 => (6506594121 / 250000000000 : ℝ)
  | 7 => (836833027 / 31250000000 : ℝ)
  | 8 => (13768513269 / 500000000000 : ℝ)
  | 9 => (14150742129 / 500000000000 : ℝ)
  | 10 => (14536014123 / 500000000000 : ℝ)
  | 11 => (29848656189 / 1000000000000 : ℝ)
  | 12 => (30631365233 / 1000000000000 : ℝ)
  | 13 => (31420151973 / 1000000000000 : ℝ)
  | 14 => (6443002491 / 200000000000 : ℝ)
  | 15 => (412699277 / 12500000000 : ℝ)
  | 16 => (33822936007 / 1000000000000 : ℝ)
  | 17 => (17317994171 / 500000000000 : ℝ)
  | 18 => (8863773233 / 250000000000 : ℝ)
  | 19 => (36280242961 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch035Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1397270079 / 62500000000 : ℝ)
  | 1 => (11539077307 / 500000000000 : ℝ)
  | 2 => (11903037873 / 500000000000 : ℝ)
  | 3 => (24540085977 / 1000000000000 : ℝ)
  | 4 => (632004653 / 25000000000 : ℝ)
  | 5 => (5205275297 / 200000000000 : ℝ)
  | 6 => (5355731373 / 200000000000 : ℝ)
  | 7 => (27537026539 / 1000000000000 : ℝ)
  | 8 => (28301484259 / 1000000000000 : ℝ)
  | 9 => (29072028247 / 1000000000000 : ℝ)
  | 10 => (2984865619 / 100000000000 : ℝ)
  | 11 => (15315682617 / 500000000000 : ℝ)
  | 12 => (15710075987 / 500000000000 : ℝ)
  | 13 => (4026876557 / 125000000000 : ℝ)
  | 14 => (33015942161 / 1000000000000 : ℝ)
  | 15 => (4227867001 / 125000000000 : ℝ)
  | 16 => (34635988343 / 1000000000000 : ℝ)
  | 17 => (35455092933 / 1000000000000 : ℝ)
  | 18 => (18140121481 / 500000000000 : ℝ)
  | 19 => (18555715511 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch035Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((700 : ℝ) + (j.val : ℝ)) / 1600)
      (((700 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch035Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch035Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((700 : ℝ) + (j.val : ℝ)) / 1600)
    (((700 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch035Neg65WeightLower j.val) (hpThetaShiftOneBatch035Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch035Neg65WeightLower, hpThetaShiftOneBatch035Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch035Neg65_integral_bounds :
    (80632965023 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (8408502661 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (700 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch035Lower hpThetaJensenCellsBatch035Upper
    hpThetaShiftOneBatch035Neg65WeightLower hpThetaShiftOneBatch035Neg65WeightUpper hpThetaJensenCellsBatch035_bounds hpThetaShiftOneBatch035Neg65_weight_bounds
  have hl : (80632965023 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch035Lower j * hpThetaShiftOneBatch035Neg65WeightLower j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftOneBatch035Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftOneBatch035Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch035Lower j * hpThetaShiftOneBatch035Neg65WeightUpper j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftOneBatch035Neg65WeightUpper j) / 1600) ≤ (8408502661 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftOneBatch035Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (700 : ℝ) / 1600 = 35 / 80 by norm_num,
    show ((700 : ℝ) + 20) / 1600 = (35 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch035Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1032390687 / 25000000000 : ℝ)
  | 1 => (-8258880853 / 200000000000 : ℝ)
  | 2 => (-8258086529 / 200000000000 : ℝ)
  | 3 => (-8256733619 / 200000000000 : ℝ)
  | 4 => (-20637044071 / 500000000000 : ℝ)
  | 5 => (-41261670291 / 1000000000000 : ℝ)
  | 6 => (-20623196011 / 500000000000 : ℝ)
  | 7 => (-8245646159 / 200000000000 : ℝ)
  | 8 => (-41207164049 / 1000000000000 : ℝ)
  | 9 => (-41183169203 / 1000000000000 : ℝ)
  | 10 => (-8231244731 / 200000000000 : ℝ)
  | 11 => (-20563152393 / 500000000000 : ℝ)
  | 12 => (-41093389961 / 1000000000000 : ℝ)
  | 13 => (-20528728263 / 500000000000 : ℝ)
  | 14 => (-41018481813 / 1000000000000 : ℝ)
  | 15 => (-20488221569 / 500000000000 : ℝ)
  | 16 => (-8186263561 / 200000000000 : ℝ)
  | 17 => (-20441541553 / 500000000000 : ℝ)
  | 18 => (-40831716317 / 1000000000000 : ℝ)
  | 19 => (-10194298677 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch035Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5161800533 / 125000000000 : ℝ)
  | 1 => (-10322608161 / 250000000000 : ℝ)
  | 2 => (-20641834047 / 500000000000 : ℝ)
  | 3 => (-41274088141 / 1000000000000 : ℝ)
  | 4 => (-4126167029 / 100000000000 : ℝ)
  | 5 => (-41246392021 / 1000000000000 : ℝ)
  | 6 => (-20614115397 / 500000000000 : ℝ)
  | 7 => (-2575447753 / 62500000000 : ℝ)
  | 8 => (-20591584601 / 500000000000 : ℝ)
  | 9 => (-20578111827 / 500000000000 : ℝ)
  | 10 => (-8225260957 / 200000000000 : ℝ)
  | 11 => (-1027334749 / 25000000000 : ℝ)
  | 12 => (-1642298261 / 40000000000 : ℝ)
  | 13 => (-10254620453 / 250000000000 : ℝ)
  | 14 => (-40976443137 / 1000000000000 : ℝ)
  | 15 => (-10232829451 / 250000000000 : ℝ)
  | 16 => (-8176616621 / 200000000000 : ℝ)
  | 17 => (-10207929079 / 250000000000 : ℝ)
  | 18 => (-40777194707 / 1000000000000 : ℝ)
  | 19 => (-8143899107 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch035Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((700 : ℝ) + (j.val : ℝ)) / 1600)
      (((700 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch035Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch035Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((700 : ℝ) + (j.val : ℝ)) / 1600)
    (((700 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch035Neg40WeightLower j.val) (hpThetaShiftOneBatch035Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch035Neg40WeightLower, hpThetaShiftOneBatch035Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch035Neg40_integral_bounds :
    (-117643009377 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-57889401799 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (700 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch035Lower hpThetaJensenCellsBatch035Upper
    hpThetaShiftOneBatch035Neg40WeightLower hpThetaShiftOneBatch035Neg40WeightUpper hpThetaJensenCellsBatch035_bounds hpThetaShiftOneBatch035Neg40_weight_bounds
  have hl : (-117643009377 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch035Lower j * hpThetaShiftOneBatch035Neg40WeightLower j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftOneBatch035Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftOneBatch035Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch035Lower j * hpThetaShiftOneBatch035Neg40WeightUpper j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftOneBatch035Neg40WeightUpper j) / 1600) ≤ (-57889401799 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftOneBatch035Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (700 : ℝ) / 1600 = 35 / 80 by norm_num,
    show ((700 : ℝ) + 20) / 1600 = (35 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch035Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5997866457 / 250000000000 : ℝ)
  | 1 => (-12118777359 / 500000000000 : ℝ)
  | 2 => (-3060520651 / 125000000000 : ℝ)
  | 3 => (-12365645869 / 500000000000 : ℝ)
  | 4 => (-12489464353 / 500000000000 : ℝ)
  | 5 => (-12613535233 / 500000000000 : ℝ)
  | 6 => (-6368927833 / 250000000000 : ℝ)
  | 7 => (-1028993823 / 40000000000 : ℝ)
  | 8 => (-25974467421 / 1000000000000 : ℝ)
  | 9 => (-13112285529 / 500000000000 : ℝ)
  | 10 => (-26475150629 / 1000000000000 : ℝ)
  | 11 => (-26726200233 / 1000000000000 : ℝ)
  | 12 => (-2697771393 / 100000000000 : ℝ)
  | 13 => (-13614842867 / 500000000000 : ℝ)
  | 14 => (-27482109619 / 1000000000000 : ℝ)
  | 15 => (-5546995903 / 200000000000 : ℝ)
  | 16 => (-27988289309 / 1000000000000 : ℝ)
  | 17 => (-28242032847 / 1000000000000 : ℝ)
  | 18 => (-2849620393 / 100000000000 : ℝ)
  | 19 => (-28750796317 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch035Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4749180811 / 200000000000 : ℝ)
  | 1 => (-23991465827 / 1000000000000 : ℝ)
  | 2 => (-24237554717 / 1000000000000 : ℝ)
  | 3 => (-24484165207 / 1000000000000 : ℝ)
  | 4 => (-24731291737 / 1000000000000 : ℝ)
  | 5 => (-4995785741 / 200000000000 : ℝ)
  | 6 => (-5045414093 / 200000000000 : ℝ)
  | 7 => (-25475711331 / 1000000000000 : ℝ)
  | 8 => (-12862422787 / 500000000000 : ℝ)
  | 9 => (-1298723371 / 50000000000 : ℝ)
  | 10 => (-26224571057 / 1000000000000 : ℝ)
  | 11 => (-6618787657 / 250000000000 : ℝ)
  | 12 => (-3340775029 / 125000000000 : ℝ)
  | 13 => (-26977713929 / 1000000000000 : ℝ)
  | 14 => (-27229685733 / 1000000000000 : ℝ)
  | 15 => (-13741054809 / 500000000000 : ℝ)
  | 16 => (-13867489757 / 500000000000 : ℝ)
  | 17 => (-6997072327 / 250000000000 : ℝ)
  | 18 => (-14121016423 / 500000000000 : ℝ)
  | 19 => (-28496203929 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch035Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((700 : ℝ) + (j.val : ℝ)) / 1600)
      (((700 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch035Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch035Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((700 : ℝ) + (j.val : ℝ)) / 1600)
    (((700 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch035Neg20WeightLower j.val) (hpThetaShiftOneBatch035Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch035Neg20WeightLower, hpThetaShiftOneBatch035Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch035Neg20_integral_bounds :
    (-2351361157 / 31250000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-3669850907 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (700 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch035Lower hpThetaJensenCellsBatch035Upper
    hpThetaShiftOneBatch035Neg20WeightLower hpThetaShiftOneBatch035Neg20WeightUpper hpThetaJensenCellsBatch035_bounds hpThetaShiftOneBatch035Neg20_weight_bounds
  have hl : (-2351361157 / 31250000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch035Lower j * hpThetaShiftOneBatch035Neg20WeightLower j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftOneBatch035Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftOneBatch035Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch035Lower j * hpThetaShiftOneBatch035Neg20WeightUpper j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftOneBatch035Neg20WeightUpper j) / 1600) ≤ (-3669850907 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftOneBatch035Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (700 : ℝ) / 1600 = 35 / 80 by norm_num,
    show ((700 : ℝ) + 20) / 1600 = (35 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch035Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch035Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch035Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch035Neg20_integral_bounds
end HodgeProofHP
