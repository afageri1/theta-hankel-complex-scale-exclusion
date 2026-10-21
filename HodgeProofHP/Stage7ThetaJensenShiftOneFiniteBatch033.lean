/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch033

/-! Exact signed weight and batch integral certificates, batch 33 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch033Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4695506911 / 50000000000 : ℝ)
  | 1 => (593313411 / 6250000000 : ℝ)
  | 2 => (19190229747 / 200000000000 : ℝ)
  | 3 => (24243253589 / 250000000000 : ℝ)
  | 4 => (97995607621 / 1000000000000 : ℝ)
  | 5 => (99018791299 / 1000000000000 : ℝ)
  | 6 => (100042425903 / 1000000000000 : ℝ)
  | 7 => (25266592419 / 250000000000 : ℝ)
  | 8 => (51045239283 / 500000000000 : ℝ)
  | 9 => (103114606209 / 1000000000000 : ℝ)
  | 10 => (52069301953 / 500000000000 : ℝ)
  | 11 => (52581160303 / 500000000000 : ℝ)
  | 12 => (331830009 / 3125000000 : ℝ)
  | 13 => (107208294903 / 1000000000000 : ℝ)
  | 14 => (21646047687 / 200000000000 : ℝ)
  | 15 => (27312818199 / 250000000000 : ℝ)
  | 16 => (55135617423 / 500000000000 : ℝ)
  | 17 => (111289958967 / 1000000000000 : ℝ)
  | 18 => (22461455407 / 200000000000 : ℝ)
  | 19 => (28330754601 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch033Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (94930145761 / 1000000000000 : ℝ)
  | 1 => (1499236699 / 15625000000 : ℝ)
  | 2 => (96973014357 / 1000000000000 : ℝ)
  | 3 => (48997803811 / 500000000000 : ℝ)
  | 4 => (990187913 / 10000000000 : ℝ)
  | 5 => (6252651619 / 62500000000 : ℝ)
  | 6 => (101066369677 / 1000000000000 : ℝ)
  | 7 => (102090478567 / 1000000000000 : ℝ)
  | 8 => (10311460621 / 100000000000 : ℝ)
  | 9 => (104138603907 / 1000000000000 : ℝ)
  | 10 => (105162320607 / 1000000000000 : ℝ)
  | 11 => (331830009 / 3125000000 : ℝ)
  | 12 => (13401036863 / 125000000000 : ℝ)
  | 13 => (27057559609 / 250000000000 : ℝ)
  | 14 => (109251272797 / 1000000000000 : ℝ)
  | 15 => (110271234847 / 1000000000000 : ℝ)
  | 16 => (13911244871 / 125000000000 : ℝ)
  | 17 => (28076819259 / 250000000000 : ℝ)
  | 18 => (22664603681 / 200000000000 : ℝ)
  | 19 => (22867401977 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch033Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((660 : ℝ) + (j.val : ℝ)) / 1600)
      (((660 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch033Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch033Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((660 : ℝ) + (j.val : ℝ)) / 1600)
    (((660 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch033Neg100WeightLower j.val) (hpThetaShiftOneBatch033Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch033Neg100WeightLower, hpThetaShiftOneBatch033Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch033Neg100_integral_bounds :
    (186523062549 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (1911826113 / 5000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (660 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch033Lower hpThetaJensenCellsBatch033Upper
    hpThetaShiftOneBatch033Neg100WeightLower hpThetaShiftOneBatch033Neg100WeightUpper hpThetaJensenCellsBatch033_bounds hpThetaShiftOneBatch033Neg100_weight_bounds
  have hl : (186523062549 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch033Lower j * hpThetaShiftOneBatch033Neg100WeightLower j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftOneBatch033Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftOneBatch033Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch033Lower j * hpThetaShiftOneBatch033Neg100WeightUpper j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftOneBatch033Neg100WeightUpper j) / 1600) ≤ (1911826113 / 5000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftOneBatch033Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (660 : ℝ) / 1600 = 33 / 80 by norm_num,
    show ((660 : ℝ) + 20) / 1600 = (33 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch033Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-129678417 / 62500000000 : ℝ)
  | 1 => (-1596039207 / 1000000000000 : ℝ)
  | 2 => (-1111555247 / 1000000000000 : ℝ)
  | 3 => (-155346363 / 250000000000 : ℝ)
  | 4 => (-125512779 / 1000000000000 : ℝ)
  | 5 => (376079519 / 1000000000000 : ℝ)
  | 6 => (441703943 / 500000000000 : ℝ)
  | 7 => (174561057 / 125000000000 : ℝ)
  | 8 => (478834263 / 250000000000 : ℝ)
  | 9 => (121998459 / 50000000000 : ℝ)
  | 10 => (1485200013 / 500000000000 : ℝ)
  | 11 => (3506644449 / 1000000000000 : ℝ)
  | 12 => (253044811 / 62500000000 : ℝ)
  | 13 => (2298315901 / 500000000000 : ℝ)
  | 14 => (5150402779 / 1000000000000 : ℝ)
  | 15 => (1142008683 / 200000000000 : ℝ)
  | 16 => (6275566871 / 1000000000000 : ℝ)
  | 17 => (136939719 / 20000000000 : ℝ)
  | 18 => (7424313099 / 1000000000000 : ℝ)
  | 19 => (8007560399 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch033Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-798019603 / 500000000000 : ℝ)
  | 1 => (-555777623 / 500000000000 : ℝ)
  | 2 => (-621385451 / 1000000000000 : ℝ)
  | 3 => (-62756389 / 500000000000 : ℝ)
  | 4 => (2350497 / 6250000000 : ℝ)
  | 5 => (883407887 / 1000000000000 : ℝ)
  | 6 => (1396488457 / 1000000000000 : ℝ)
  | 7 => (1915337053 / 1000000000000 : ℝ)
  | 8 => (2439969181 / 1000000000000 : ℝ)
  | 9 => (2970400027 / 1000000000000 : ℝ)
  | 10 => (70132889 / 20000000000 : ℝ)
  | 11 => (4048716977 / 1000000000000 : ℝ)
  | 12 => (4596631803 / 1000000000000 : ℝ)
  | 13 => (257520139 / 50000000000 : ℝ)
  | 14 => (713755427 / 125000000000 : ℝ)
  | 15 => (784445859 / 125000000000 : ℝ)
  | 16 => (6846985951 / 1000000000000 : ℝ)
  | 17 => (74243131 / 10000000000 : ℝ)
  | 18 => (20018901 / 2500000000 : ℝ)
  | 19 => (1719347913 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch033Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((660 : ℝ) + (j.val : ℝ)) / 1600)
      (((660 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch033Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch033Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((660 : ℝ) + (j.val : ℝ)) / 1600)
    (((660 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch033Neg65WeightLower j.val) (hpThetaShiftOneBatch033Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch033Neg65WeightLower, hpThetaShiftOneBatch033Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch033Neg65_integral_bounds :
    (9709857571 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (5915268771 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (660 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch033Lower hpThetaJensenCellsBatch033Upper
    hpThetaShiftOneBatch033Neg65WeightLower hpThetaShiftOneBatch033Neg65WeightUpper hpThetaJensenCellsBatch033_bounds hpThetaShiftOneBatch033Neg65_weight_bounds
  have hl : (9709857571 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch033Lower j * hpThetaShiftOneBatch033Neg65WeightLower j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftOneBatch033Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftOneBatch033Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch033Lower j * hpThetaShiftOneBatch033Neg65WeightUpper j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftOneBatch033Neg65WeightUpper j) / 1600) ≤ (5915268771 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftOneBatch033Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (660 : ℝ) / 1600 = 33 / 80 by norm_num,
    show ((660 : ℝ) + 20) / 1600 = (33 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch033Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-19708623963 / 500000000000 : ℝ)
  | 1 => (-19753468437 / 500000000000 : ℝ)
  | 2 => (-39594703313 / 1000000000000 : ℝ)
  | 3 => (-39680526349 / 1000000000000 : ℝ)
  | 4 => (-19882192517 / 500000000000 : ℝ)
  | 5 => (-39846258367 / 1000000000000 : ℝ)
  | 6 => (-39926125297 / 1000000000000 : ℝ)
  | 7 => (-20001982361 / 500000000000 : ℝ)
  | 8 => (-40079755487 / 1000000000000 : ℝ)
  | 9 => (-40153476391 / 1000000000000 : ℝ)
  | 10 => (-20112553091 / 500000000000 : ℝ)
  | 11 => (-1007365589 / 25000000000 : ℝ)
  | 12 => (-40362007177 / 1000000000000 : ℝ)
  | 13 => (-40427235639 / 1000000000000 : ℝ)
  | 14 => (-40490287503 / 1000000000000 : ℝ)
  | 15 => (-10137785321 / 250000000000 : ℝ)
  | 16 => (-5076221931 / 125000000000 : ℝ)
  | 17 => (-40666168419 / 1000000000000 : ℝ)
  | 18 => (-40720298577 / 1000000000000 : ℝ)
  | 19 => (-40772144259 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch033Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1228926791 / 31250000000 : ℝ)
  | 1 => (-1576689917 / 40000000000 : ℝ)
  | 2 => (-39506936873 / 1000000000000 : ℝ)
  | 3 => (-2474668957 / 62500000000 : ℝ)
  | 4 => (-9920131587 / 250000000000 : ℝ)
  | 5 => (-39764385033 / 1000000000000 : ℝ)
  | 6 => (-19923129183 / 500000000000 : ℝ)
  | 7 => (-2495382831 / 62500000000 : ℝ)
  | 8 => (-40003964721 / 1000000000000 : ℝ)
  | 9 => (-20039877743 / 500000000000 : ℝ)
  | 10 => (-4015347639 / 100000000000 : ℝ)
  | 11 => (-40225106181 / 1000000000000 : ℝ)
  | 12 => (-40294623559 / 1000000000000 : ℝ)
  | 13 => (-5045250897 / 125000000000 : ℝ)
  | 14 => (-20213617819 / 500000000000 : ℝ)
  | 15 => (-20245143751 / 500000000000 : ℝ)
  | 16 => (-40551141283 / 1000000000000 : ℝ)
  | 17 => (-40609775447 / 1000000000000 : ℝ)
  | 18 => (-20333084209 / 500000000000 : ℝ)
  | 19 => (-2545018661 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch033Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((660 : ℝ) + (j.val : ℝ)) / 1600)
      (((660 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch033Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch033Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((660 : ℝ) + (j.val : ℝ)) / 1600)
    (((660 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch033Neg40WeightLower j.val) (hpThetaShiftOneBatch033Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch033Neg40WeightLower, hpThetaShiftOneBatch033Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch033Neg40_integral_bounds :
    (-146954370759 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-144526784317 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (660 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch033Lower hpThetaJensenCellsBatch033Upper
    hpThetaShiftOneBatch033Neg40WeightLower hpThetaShiftOneBatch033Neg40WeightUpper hpThetaJensenCellsBatch033_bounds hpThetaShiftOneBatch033Neg40_weight_bounds
  have hl : (-146954370759 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch033Lower j * hpThetaShiftOneBatch033Neg40WeightLower j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftOneBatch033Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftOneBatch033Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch033Lower j * hpThetaShiftOneBatch033Neg40WeightUpper j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftOneBatch033Neg40WeightUpper j) / 1600) ≤ (-144526784317 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftOneBatch033Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (660 : ℝ) / 1600 = 33 / 80 by norm_num,
    show ((660 : ℝ) + 20) / 1600 = (33 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch033Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-7317146057 / 500000000000 : ℝ)
  | 1 => (-14855436597 / 1000000000000 : ℝ)
  | 2 => (-753864551 / 50000000000 : ℝ)
  | 3 => (-3824962867 / 250000000000 : ℝ)
  | 4 => (-1552311399 / 100000000000 : ℝ)
  | 5 => (-15747074593 / 1000000000000 : ℝ)
  | 6 => (-15971729243 / 1000000000000 : ℝ)
  | 7 => (-16197073867 / 1000000000000 : ℝ)
  | 8 => (-16423104351 / 1000000000000 : ℝ)
  | 9 => (-8324908271 / 500000000000 : ℝ)
  | 10 => (-3375441249 / 200000000000 : ℝ)
  | 11 => (-684210769 / 40000000000 : ℝ)
  | 12 => (-2166750151 / 125000000000 : ℝ)
  | 13 => (-4390849469 / 250000000000 : ℝ)
  | 14 => (-8896727437 / 500000000000 : ℝ)
  | 15 => (-4506041951 / 250000000000 : ℝ)
  | 16 => (-4563883057 / 250000000000 : ℝ)
  | 17 => (-18487543667 / 1000000000000 : ℝ)
  | 18 => (-18720197601 / 1000000000000 : ℝ)
  | 19 => (-4738372367 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch033Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-14413861441 / 1000000000000 : ℝ)
  | 1 => (-14634292113 / 1000000000000 : ℝ)
  | 2 => (-3713859149 / 250000000000 : ℝ)
  | 3 => (-15077291019 / 1000000000000 : ℝ)
  | 4 => (-15299851467 / 1000000000000 : ℝ)
  | 5 => (-15523113989 / 1000000000000 : ℝ)
  | 6 => (-492096081 / 31250000000 : ℝ)
  | 7 => (-7985864621 / 500000000000 : ℝ)
  | 8 => (-8098536933 / 500000000000 : ℝ)
  | 9 => (-328462087 / 20000000000 : ℝ)
  | 10 => (-16649816541 / 1000000000000 : ℝ)
  | 11 => (-4219301561 / 250000000000 : ℝ)
  | 12 => (-2138158653 / 125000000000 : ℝ)
  | 13 => (-17334001207 / 1000000000000 : ℝ)
  | 14 => (-140507183 / 8000000000 : ℝ)
  | 15 => (-17793454873 / 1000000000000 : ℝ)
  | 16 => (-18024167803 / 1000000000000 : ℝ)
  | 17 => (-18255532227 / 1000000000000 : ℝ)
  | 18 => (-9243771833 / 500000000000 : ℝ)
  | 19 => (-23400247 / 1250000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch033Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((660 : ℝ) + (j.val : ℝ)) / 1600)
      (((660 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch033Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch033Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((660 : ℝ) + (j.val : ℝ)) / 1600)
    (((660 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch033Neg20WeightLower j.val) (hpThetaShiftOneBatch033Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch033Neg20WeightLower, hpThetaShiftOneBatch033Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch033Neg20_integral_bounds :
    (-61247928929 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-14881748863 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (660 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch033Lower hpThetaJensenCellsBatch033Upper
    hpThetaShiftOneBatch033Neg20WeightLower hpThetaShiftOneBatch033Neg20WeightUpper hpThetaJensenCellsBatch033_bounds hpThetaShiftOneBatch033Neg20_weight_bounds
  have hl : (-61247928929 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch033Lower j * hpThetaShiftOneBatch033Neg20WeightLower j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftOneBatch033Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftOneBatch033Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch033Lower j * hpThetaShiftOneBatch033Neg20WeightUpper j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftOneBatch033Neg20WeightUpper j) / 1600) ≤ (-14881748863 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftOneBatch033Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (660 : ℝ) / 1600 = 33 / 80 by norm_num,
    show ((660 : ℝ) + 20) / 1600 = (33 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch033Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch033Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch033Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch033Neg20_integral_bounds
end HodgeProofHP
