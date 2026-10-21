/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch034

/-! Exact signed weight and batch integral certificates, batch 34 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch034Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (28584252471 / 250000000000 : ℝ)
  | 1 => (57674537857 / 500000000000 : ℝ)
  | 2 => (58179518773 / 500000000000 : ℝ)
  | 3 => (117366714421 / 1000000000000 : ℝ)
  | 4 => (59185961373 / 500000000000 : ℝ)
  | 5 => (119374476271 / 1000000000000 : ℝ)
  | 6 => (120374186069 / 1000000000000 : ℝ)
  | 7 => (3792839391 / 31250000000 : ℝ)
  | 8 => (122364305249 / 1000000000000 : ℝ)
  | 9 => (123354323183 / 1000000000000 : ℝ)
  | 10 => (62170357223 / 500000000000 : ℝ)
  | 11 => (125323276381 / 1000000000000 : ℝ)
  | 12 => (126301803513 / 1000000000000 : ℝ)
  | 13 => (12727608753 / 100000000000 : ℝ)
  | 14 => (128245917259 / 1000000000000 : ℝ)
  | 15 => (1615138483 / 12500000000 : ℝ)
  | 16 => (8135709669 / 62500000000 : ℝ)
  | 17 => (8195407847 / 62500000000 : ℝ)
  | 18 => (5283054733 / 40000000000 : ℝ)
  | 19 => (26604131437 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch034Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (23069815143 / 200000000000 : ℝ)
  | 1 => (116359037547 / 1000000000000 : ℝ)
  | 2 => (58683357211 / 500000000000 : ℝ)
  | 3 => (118371922747 / 1000000000000 : ℝ)
  | 4 => (7460904767 / 62500000000 : ℝ)
  | 5 => (12037418607 / 100000000000 : ℝ)
  | 6 => (121370860513 / 1000000000000 : ℝ)
  | 7 => (489457221 / 4000000000 : ℝ)
  | 8 => (7709645199 / 62500000000 : ℝ)
  | 9 => (124340714447 / 1000000000000 : ℝ)
  | 10 => (62661638191 / 500000000000 : ℝ)
  | 11 => (63150901757 / 500000000000 : ℝ)
  | 12 => (127276087531 / 1000000000000 : ℝ)
  | 13 => (6412295863 / 50000000000 : ℝ)
  | 14 => (129211078641 / 1000000000000 : ℝ)
  | 15 => (26034270941 / 200000000000 : ℝ)
  | 16 => (131126525553 / 1000000000000 : ℝ)
  | 17 => (66038184163 / 500000000000 : ℝ)
  | 18 => (66510328593 / 500000000000 : ℝ)
  | 19 => (133959163291 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch034Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((680 : ℝ) + (j.val : ℝ)) / 1600)
      (((680 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch034Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch034Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((680 : ℝ) + (j.val : ℝ)) / 1600)
    (((680 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch034Neg100WeightLower j.val) (hpThetaShiftOneBatch034Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch034Neg100WeightLower, hpThetaShiftOneBatch034Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch034Neg100_integral_bounds :
    (98726163173 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (404084320173 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (680 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch034Lower hpThetaJensenCellsBatch034Upper
    hpThetaShiftOneBatch034Neg100WeightLower hpThetaShiftOneBatch034Neg100WeightUpper hpThetaJensenCellsBatch034_bounds hpThetaShiftOneBatch034Neg100_weight_bounds
  have hl : (98726163173 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch034Lower j * hpThetaShiftOneBatch034Neg100WeightLower j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftOneBatch034Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftOneBatch034Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch034Lower j * hpThetaShiftOneBatch034Neg100WeightUpper j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftOneBatch034Neg100WeightUpper j) / 1600) ≤ (404084320173 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftOneBatch034Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (680 : ℝ) / 1600 = 34 / 80 by norm_num,
    show ((680 : ℝ) + 20) / 1600 = (34 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch034Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2149184891 / 250000000000 : ℝ)
  | 1 => (2297965483 / 250000000000 : ℝ)
  | 2 => (1958587693 / 200000000000 : ℝ)
  | 3 => (519998987 / 50000000000 : ℝ)
  | 4 => (5506497973 / 500000000000 : ℝ)
  | 5 => (2907999219 / 250000000000 : ℝ)
  | 6 => (12256991927 / 1000000000000 : ℝ)
  | 7 => (3221997523 / 250000000000 : ℝ)
  | 8 => (13524999953 / 1000000000000 : ℝ)
  | 9 => (177100371 / 12500000000 : ℝ)
  | 10 => (7408543511 / 500000000000 : ℝ)
  | 11 => (7736089653 / 500000000000 : ℝ)
  | 12 => (645332537 / 40000000000 : ℝ)
  | 13 => (16800495841 / 1000000000000 : ℝ)
  | 14 => (8736866287 / 500000000000 : ℝ)
  | 15 => (9076514599 / 500000000000 : ℝ)
  | 16 => (3767678167 / 200000000000 : ℝ)
  | 17 => (2441227769 / 125000000000 : ℝ)
  | 18 => (10113663677 / 500000000000 : ℝ)
  | 19 => (20930910177 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch034Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (9191861933 / 1000000000000 : ℝ)
  | 1 => (4896469233 / 500000000000 : ℝ)
  | 2 => (10399979741 / 1000000000000 : ℝ)
  | 3 => (11012995947 / 1000000000000 : ℝ)
  | 4 => (11631996877 / 1000000000000 : ℝ)
  | 5 => (1532123991 / 125000000000 : ℝ)
  | 6 => (12887990093 / 1000000000000 : ℝ)
  | 7 => (6762499977 / 500000000000 : ℝ)
  | 8 => (14168029681 / 1000000000000 : ℝ)
  | 9 => (14817087023 / 1000000000000 : ℝ)
  | 10 => (15472179307 / 1000000000000 : ℝ)
  | 11 => (8066656713 / 500000000000 : ℝ)
  | 12 => (8400247921 / 500000000000 : ℝ)
  | 13 => (698949303 / 40000000000 : ℝ)
  | 14 => (18153029199 / 1000000000000 : ℝ)
  | 15 => (4709597709 / 250000000000 : ℝ)
  | 16 => (19529822153 / 1000000000000 : ℝ)
  | 17 => (4045465471 / 200000000000 : ℝ)
  | 18 => (10465455089 / 500000000000 : ℝ)
  | 19 => (10820286943 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch034Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((680 : ℝ) + (j.val : ℝ)) / 1600)
      (((680 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch034Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch034Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((680 : ℝ) + (j.val : ℝ)) / 1600)
    (((680 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch034Neg65WeightLower j.val) (hpThetaShiftOneBatch034Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch034Neg65WeightLower, hpThetaShiftOneBatch034Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch034Neg65_integral_bounds :
    (46202080271 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (49015705217 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (680 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch034Lower hpThetaJensenCellsBatch034Upper
    hpThetaShiftOneBatch034Neg65WeightLower hpThetaShiftOneBatch034Neg65WeightUpper hpThetaJensenCellsBatch034_bounds hpThetaShiftOneBatch034Neg65_weight_bounds
  have hl : (46202080271 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch034Lower j * hpThetaShiftOneBatch034Neg65WeightLower j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftOneBatch034Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftOneBatch034Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch034Lower j * hpThetaShiftOneBatch034Neg65WeightUpper j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftOneBatch034Neg65WeightUpper j) / 1600) ≤ (49015705217 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftOneBatch034Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (680 : ℝ) / 1600 = 34 / 80 by norm_num,
    show ((680 : ℝ) + 20) / 1600 = (34 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch034Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-40821683757 / 1000000000000 : ℝ)
  | 1 => (-20434447663 / 500000000000 : ℝ)
  | 2 => (-40913757177 / 1000000000000 : ℝ)
  | 3 => (-40956247481 / 1000000000000 : ℝ)
  | 4 => (-4099634437 / 100000000000 : ℝ)
  | 5 => (-41034025937 / 1000000000000 : ℝ)
  | 6 => (-41069270237 / 1000000000000 : ℝ)
  | 7 => (-41102055289 / 1000000000000 : ℝ)
  | 8 => (-1285386221 / 31250000000 : ℝ)
  | 9 => (-20580079767 / 500000000000 : ℝ)
  | 10 => (-5148179323 / 125000000000 : ℝ)
  | 11 => (-41208162099 / 1000000000000 : ℝ)
  | 12 => (-515353999 / 12500000000 : ℝ)
  | 13 => (-41245885859 / 1000000000000 : ℝ)
  | 14 => (-20630418847 / 500000000000 : ℝ)
  | 15 => (-41273153171 / 1000000000000 : ℝ)
  | 16 => (-41282810007 / 1000000000000 : ℝ)
  | 17 => (-4128978589 / 100000000000 : ℝ)
  | 18 => (-20647029239 / 500000000000 : ℝ)
  | 19 => (-20647802701 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch034Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-20386072129 / 500000000000 : ℝ)
  | 1 => (-10205420939 / 250000000000 : ℝ)
  | 2 => (-1634755813 / 40000000000 : ℝ)
  | 3 => (-5114219647 / 125000000000 : ℝ)
  | 4 => (-1023906187 / 25000000000 : ℝ)
  | 5 => (-40996344369 / 1000000000000 : ℝ)
  | 6 => (-2564626621 / 62500000000 : ℝ)
  | 7 => (-10267317559 / 250000000000 : ℝ)
  | 8 => (-5137756911 / 125000000000 : ℝ)
  | 9 => (-41132359071 / 1000000000000 : ℝ)
  | 10 => (-41160159533 / 1000000000000 : ℝ)
  | 11 => (-41185434583 / 1000000000000 : ℝ)
  | 12 => (-20604081049 / 500000000000 : ℝ)
  | 13 => (-41228319919 / 1000000000000 : ℝ)
  | 14 => (-20622942929 / 500000000000 : ℝ)
  | 15 => (-41260837693 / 1000000000000 : ℝ)
  | 16 => (-4127315317 / 100000000000 : ℝ)
  | 17 => (-20641405003 / 500000000000 : ℝ)
  | 18 => (-41289785889 / 1000000000000 : ℝ)
  | 19 => (-41294058477 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch034Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((680 : ℝ) + (j.val : ℝ)) / 1600)
      (((680 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch034Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch034Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((680 : ℝ) + (j.val : ℝ)) / 1600)
    (((680 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch034Neg40WeightLower j.val) (hpThetaShiftOneBatch034Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch034Neg40WeightLower, hpThetaShiftOneBatch034Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch034Neg40_integral_bounds :
    (-133409708079 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-131329963209 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (680 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch034Lower hpThetaJensenCellsBatch034Upper
    hpThetaShiftOneBatch034Neg40WeightLower hpThetaShiftOneBatch034Neg40WeightUpper hpThetaJensenCellsBatch034_bounds hpThetaShiftOneBatch034Neg40_weight_bounds
  have hl : (-133409708079 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch034Lower j * hpThetaShiftOneBatch034Neg40WeightLower j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftOneBatch034Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftOneBatch034Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch034Lower j * hpThetaShiftOneBatch034Neg40WeightUpper j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftOneBatch034Neg40WeightUpper j) / 1600) ≤ (-131329963209 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftOneBatch034Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (680 : ℝ) / 1600 = 34 / 80 by norm_num,
    show ((680 : ℝ) + 20) / 1600 = (34 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch034Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4796853667 / 250000000000 : ℝ)
  | 1 => (-19421968557 / 1000000000000 : ℝ)
  | 2 => (-19657146451 / 1000000000000 : ℝ)
  | 3 => (-159143549 / 8000000000 : ℝ)
  | 4 => (-1258084707 / 62500000000 : ℝ)
  | 5 => (-4073275341 / 200000000000 : ℝ)
  | 6 => (-20604002953 / 1000000000000 : ℝ)
  | 7 => (-20842229167 / 1000000000000 : ℝ)
  | 8 => (-21081050413 / 1000000000000 : ℝ)
  | 9 => (-533011543 / 25000000000 : ℝ)
  | 10 => (-2156045807 / 100000000000 : ℝ)
  | 11 => (-2725129301 / 125000000000 : ℝ)
  | 12 => (-4408437127 / 200000000000 : ℝ)
  | 13 => (-2228390661 / 100000000000 : ℝ)
  | 14 => (-2815774019 / 125000000000 : ℝ)
  | 15 => (-22769037037 / 1000000000000 : ℝ)
  | 16 => (-11506217999 / 500000000000 : ℝ)
  | 17 => (-23256383729 / 1000000000000 : ℝ)
  | 18 => (-11750437439 / 500000000000 : ℝ)
  | 19 => (-2968238007 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch034Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-18953489467 / 1000000000000 : ℝ)
  | 1 => (-19187414667 / 1000000000000 : ℝ)
  | 2 => (-4855492139 / 250000000000 : ℝ)
  | 3 => (-393142929 / 20000000000 : ℝ)
  | 4 => (-2486617953 / 125000000000 : ℝ)
  | 5 => (-20129355311 / 1000000000000 : ℝ)
  | 6 => (-79556159 / 3906250000 : ℝ)
  | 7 => (-2575500369 / 125000000000 : ℝ)
  | 8 => (-10421114583 / 500000000000 : ℝ)
  | 9 => (-5270262603 / 250000000000 : ℝ)
  | 10 => (-21320461719 / 1000000000000 : ℝ)
  | 11 => (-21560458069 / 1000000000000 : ℝ)
  | 12 => (-21801034407 / 1000000000000 : ℝ)
  | 13 => (-11021092817 / 500000000000 : ℝ)
  | 14 => (-22283906609 / 1000000000000 : ℝ)
  | 15 => (-22526192151 / 1000000000000 : ℝ)
  | 16 => (-5692259259 / 250000000000 : ℝ)
  | 17 => (-23012435997 / 1000000000000 : ℝ)
  | 18 => (-1453523983 / 62500000000 : ℝ)
  | 19 => (-23500874877 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch034Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((680 : ℝ) + (j.val : ℝ)) / 1600)
      (((680 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch034Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch034Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((680 : ℝ) + (j.val : ℝ)) / 1600)
    (((680 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch034Neg20WeightLower j.val) (hpThetaShiftOneBatch034Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch034Neg20WeightLower, hpThetaShiftOneBatch034Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch034Neg20_integral_bounds :
    (-34711593723 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-67619742941 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (680 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch034Lower hpThetaJensenCellsBatch034Upper
    hpThetaShiftOneBatch034Neg20WeightLower hpThetaShiftOneBatch034Neg20WeightUpper hpThetaJensenCellsBatch034_bounds hpThetaShiftOneBatch034Neg20_weight_bounds
  have hl : (-34711593723 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch034Lower j * hpThetaShiftOneBatch034Neg20WeightLower j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftOneBatch034Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftOneBatch034Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch034Lower j * hpThetaShiftOneBatch034Neg20WeightUpper j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftOneBatch034Neg20WeightUpper j) / 1600) ≤ (-67619742941 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftOneBatch034Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (680 : ℝ) / 1600 = 34 / 80 by norm_num,
    show ((680 : ℝ) + 20) / 1600 = (34 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch034Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch034Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch034Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch034Neg20_integral_bounds
end HodgeProofHP
