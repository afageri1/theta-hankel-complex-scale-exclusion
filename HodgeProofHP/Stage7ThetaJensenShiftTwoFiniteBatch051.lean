/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch051

/-! Exact signed weight and batch integral certificates, batch 51 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch051Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-34243018053 / 1000000000000 : ℝ)
  | 1 => (-3496520489 / 100000000000 : ℝ)
  | 2 => (-17848897291 / 500000000000 : ℝ)
  | 3 => (-9110225709 / 250000000000 : ℝ)
  | 4 => (-37194646391 / 1000000000000 : ℝ)
  | 5 => (-37959143021 / 1000000000000 : ℝ)
  | 6 => (-38734511541 / 1000000000000 : ℝ)
  | 7 => (-1976043591 / 50000000000 : ℝ)
  | 8 => (-20159172391 / 500000000000 : ℝ)
  | 9 => (-8225410483 / 200000000000 : ℝ)
  | 10 => (-8389423557 / 200000000000 : ℝ)
  | 11 => (-42778665033 / 1000000000000 : ℝ)
  | 12 => (-43621819391 / 1000000000000 : ℝ)
  | 13 => (-22238353593 / 500000000000 : ℝ)
  | 14 => (-5667931981 / 125000000000 : ℝ)
  | 15 => (-46222193919 / 1000000000000 : ℝ)
  | 16 => (-2355652553 / 50000000000 : ℝ)
  | 17 => (-24008079029 / 500000000000 : ℝ)
  | 18 => (-12232911709 / 250000000000 : ℝ)
  | 19 => (-6232456307 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch051Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-33531119379 / 1000000000000 : ℝ)
  | 1 => (-8560754513 / 250000000000 : ℝ)
  | 2 => (-34965204889 / 1000000000000 : ℝ)
  | 3 => (-35697794581 / 1000000000000 : ℝ)
  | 4 => (-7288180567 / 200000000000 : ℝ)
  | 5 => (-3719464639 / 100000000000 : ℝ)
  | 6 => (-1897957151 / 50000000000 : ℝ)
  | 7 => (-1936725577 / 50000000000 : ℝ)
  | 8 => (-39520871819 / 1000000000000 : ℝ)
  | 9 => (-40318344781 / 1000000000000 : ℝ)
  | 10 => (-20563526207 / 500000000000 : ℝ)
  | 11 => (-5243389723 / 125000000000 : ℝ)
  | 12 => (-5347333129 / 125000000000 : ℝ)
  | 13 => (-4362181939 / 100000000000 : ℝ)
  | 14 => (-8895341437 / 200000000000 : ℝ)
  | 15 => (-45343455847 / 1000000000000 : ℝ)
  | 16 => (-23111096959 / 500000000000 : ℝ)
  | 17 => (-47113051059 / 1000000000000 : ℝ)
  | 18 => (-48016158057 / 1000000000000 : ℝ)
  | 19 => (-9786329367 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch051Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1020 : ℝ) + (j.val : ℝ)) / 1600)
      (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch051Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch051Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1020 : ℝ) + (j.val : ℝ)) / 1600)
    (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch051Neg100WeightLower j.val) (hpThetaShiftTwoBatch051Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch051Neg100WeightLower, hpThetaShiftTwoBatch051Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch051Neg100_integral_bounds :
    (-463099121 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-56970877 / 8000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1020 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch051Lower hpThetaJensenCellsBatch051Upper
    hpThetaShiftTwoBatch051Neg100WeightLower hpThetaShiftTwoBatch051Neg100WeightUpper hpThetaJensenCellsBatch051_bounds hpThetaShiftTwoBatch051Neg100_weight_bounds
  have hl : (-463099121 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch051Lower j * hpThetaShiftTwoBatch051Neg100WeightLower j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftTwoBatch051Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftTwoBatch051Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch051Lower j * hpThetaShiftTwoBatch051Neg100WeightUpper j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftTwoBatch051Neg100WeightUpper j) / 1600) ≤ (-56970877 / 8000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftTwoBatch051Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1020 : ℝ) / 1600 = 51 / 80 by norm_num,
    show ((1020 : ℝ) + 20) / 1600 = (51 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch051Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1227384733 / 125000000000 : ℝ)
  | 1 => (4929130253 / 500000000000 : ℝ)
  | 2 => (77318827 / 7812500000 : ℝ)
  | 3 => (155229851 / 15625000000 : ℝ)
  | 4 => (9971946693 / 1000000000000 : ℝ)
  | 5 => (10008502717 / 1000000000000 : ℝ)
  | 6 => (2511090629 / 250000000000 : ℝ)
  | 7 => (10079509879 / 1000000000000 : ℝ)
  | 8 => (10113928397 / 1000000000000 : ℝ)
  | 9 => (10147601467 / 1000000000000 : ℝ)
  | 10 => (10180512287 / 1000000000000 : ℝ)
  | 11 => (2042528771 / 200000000000 : ℝ)
  | 12 => (10243978967 / 1000000000000 : ℝ)
  | 13 => (10274500217 / 1000000000000 : ℝ)
  | 14 => (1288023749 / 125000000000 : ℝ)
  | 15 => (5166515237 / 500000000000 : ℝ)
  | 16 => (2072200727 / 200000000000 : ℝ)
  | 17 => (259702281 / 25000000000 : ℝ)
  | 18 => (5207137419 / 500000000000 : ℝ)
  | 19 => (1304941971 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch051Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (9858260507 / 1000000000000 : ℝ)
  | 1 => (9896809857 / 1000000000000 : ℝ)
  | 2 => (1986942093 / 200000000000 : ℝ)
  | 3 => (4985973347 / 500000000000 : ℝ)
  | 4 => (5004251359 / 500000000000 : ℝ)
  | 5 => (10044362517 / 1000000000000 : ℝ)
  | 6 => (251987747 / 25000000000 : ℝ)
  | 7 => (5056964199 / 500000000000 : ℝ)
  | 8 => (2536900367 / 250000000000 : ℝ)
  | 9 => (318141009 / 31250000000 : ℝ)
  | 10 => (638290241 / 62500000000 : ℝ)
  | 11 => (1280497371 / 125000000000 : ℝ)
  | 12 => (5137250109 / 500000000000 : ℝ)
  | 13 => (10304189993 / 1000000000000 : ℝ)
  | 14 => (413321219 / 40000000000 : ℝ)
  | 15 => (2590250909 / 250000000000 : ℝ)
  | 16 => (10388091241 / 1000000000000 : ℝ)
  | 17 => (10414274839 / 1000000000000 : ℝ)
  | 18 => (10439535769 / 1000000000000 : ℝ)
  | 19 => (653990947 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch051Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1020 : ℝ) + (j.val : ℝ)) / 1600)
      (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch051Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch051Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1020 : ℝ) + (j.val : ℝ)) / 1600)
    (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch051Neg65WeightLower j.val) (hpThetaShiftTwoBatch051Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch051Neg65WeightLower, hpThetaShiftTwoBatch051Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch051Neg65_integral_bounds :
    (222264021 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (181960241 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1020 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch051Lower hpThetaJensenCellsBatch051Upper
    hpThetaShiftTwoBatch051Neg65WeightLower hpThetaShiftTwoBatch051Neg65WeightUpper hpThetaJensenCellsBatch051_bounds hpThetaShiftTwoBatch051Neg65_weight_bounds
  have hl : (222264021 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch051Lower j * hpThetaShiftTwoBatch051Neg65WeightLower j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftTwoBatch051Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftTwoBatch051Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch051Lower j * hpThetaShiftTwoBatch051Neg65WeightUpper j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftTwoBatch051Neg65WeightUpper j) / 1600) ≤ (181960241 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftTwoBatch051Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1020 : ℝ) / 1600 = 51 / 80 by norm_num,
    show ((1020 : ℝ) + 20) / 1600 = (51 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch051Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1742995451 / 500000000000 : ℝ)
  | 1 => (1771059249 / 500000000000 : ℝ)
  | 2 => (112457729 / 31250000000 : ℝ)
  | 3 => (3655577689 / 1000000000000 : ℝ)
  | 4 => (3712909851 / 1000000000000 : ℝ)
  | 5 => (3770644053 / 1000000000000 : ℝ)
  | 6 => (3828780509 / 1000000000000 : ℝ)
  | 7 => (3887319401 / 1000000000000 : ℝ)
  | 8 => (3946260883 / 1000000000000 : ℝ)
  | 9 => (4005605079 / 1000000000000 : ℝ)
  | 10 => (2032676041 / 500000000000 : ℝ)
  | 11 => (2062750977 / 500000000000 : ℝ)
  | 12 => (523256841 / 125000000000 : ℝ)
  | 13 => (1061752601 / 250000000000 : ℝ)
  | 14 => (86167379 / 20000000000 : ℝ)
  | 15 => (4370130303 / 1000000000000 : ℝ)
  | 16 => (886458873 / 200000000000 : ℝ)
  | 17 => (4494861009 / 1000000000000 : ℝ)
  | 18 => (4557830069 / 1000000000000 : ℝ)
  | 19 => (4621201351 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch051Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3542118499 / 1000000000000 : ℝ)
  | 1 => (3598647329 / 1000000000000 : ℝ)
  | 2 => (365557769 / 100000000000 : ℝ)
  | 3 => (928227463 / 250000000000 : ℝ)
  | 4 => (1885322027 / 500000000000 : ℝ)
  | 5 => (382878051 / 100000000000 : ℝ)
  | 6 => (1943659701 / 500000000000 : ℝ)
  | 7 => (986565221 / 250000000000 : ℝ)
  | 8 => (100140127 / 25000000000 : ℝ)
  | 9 => (4065352083 / 1000000000000 : ℝ)
  | 10 => (825100391 / 200000000000 : ℝ)
  | 11 => (4186054729 / 1000000000000 : ℝ)
  | 12 => (849402081 / 200000000000 : ℝ)
  | 13 => (4308368951 / 1000000000000 : ℝ)
  | 14 => (34141643 / 7812500000 : ℝ)
  | 15 => (2216147183 / 500000000000 : ℝ)
  | 16 => (449486101 / 100000000000 : ℝ)
  | 17 => (455783007 / 100000000000 : ℝ)
  | 18 => (577650169 / 125000000000 : ℝ)
  | 19 => (146405457 / 31250000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch051Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1020 : ℝ) + (j.val : ℝ)) / 1600)
      (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch051Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch051Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1020 : ℝ) + (j.val : ℝ)) / 1600)
    (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch051Neg45WeightLower j.val) (hpThetaShiftTwoBatch051Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch051Neg45WeightLower, hpThetaShiftTwoBatch051Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch051Neg45_integral_bounds :
    (704966377 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (14596223 / 20000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1020 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch051Lower hpThetaJensenCellsBatch051Upper
    hpThetaShiftTwoBatch051Neg45WeightLower hpThetaShiftTwoBatch051Neg45WeightUpper hpThetaJensenCellsBatch051_bounds hpThetaShiftTwoBatch051Neg45_weight_bounds
  have hl : (704966377 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch051Lower j * hpThetaShiftTwoBatch051Neg45WeightLower j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftTwoBatch051Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftTwoBatch051Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch051Lower j * hpThetaShiftTwoBatch051Neg45WeightUpper j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftTwoBatch051Neg45WeightUpper j) / 1600) ≤ (14596223 / 20000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftTwoBatch051Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1020 : ℝ) / 1600 = 51 / 80 by norm_num,
    show ((1020 : ℝ) + 20) / 1600 = (51 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch051Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-10879283 / 3125000000 : ℝ)
  | 1 => (-3491403771 / 1000000000000 : ℝ)
  | 2 => (-3501342049 / 1000000000000 : ℝ)
  | 3 => (-702236811 / 200000000000 : ℝ)
  | 4 => (-880232111 / 250000000000 : ℝ)
  | 5 => (-1765286933 / 500000000000 : ℝ)
  | 6 => (-44251487 / 12500000000 : ℝ)
  | 7 => (-3549562361 / 1000000000000 : ℝ)
  | 8 => (-3558902697 / 1000000000000 : ℝ)
  | 9 => (-892034647 / 250000000000 : ℝ)
  | 10 => (-447158581 / 125000000000 : ℝ)
  | 11 => (-3586291483 / 1000000000000 : ℝ)
  | 12 => (-3595205693 / 1000000000000 : ℝ)
  | 13 => (-360400987 / 100000000000 : ℝ)
  | 14 => (-1806351301 / 500000000000 : ℝ)
  | 15 => (-724256493 / 200000000000 : ℝ)
  | 16 => (-3629748033 / 1000000000000 : ℝ)
  | 17 => (-3638097871 / 1000000000000 : ℝ)
  | 18 => (-455791317 / 125000000000 : ℝ)
  | 19 => (-3654444579 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch051Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-694248749 / 200000000000 : ℝ)
  | 1 => (-3481370559 / 1000000000000 : ℝ)
  | 2 => (-349140377 / 100000000000 : ℝ)
  | 3 => (-109416939 / 31250000000 : ℝ)
  | 4 => (-1755592027 / 500000000000 : ℝ)
  | 5 => (-3520928443 / 1000000000000 : ℝ)
  | 6 => (-706114773 / 200000000000 : ℝ)
  | 7 => (-3540118959 / 1000000000000 : ℝ)
  | 8 => (-88739059 / 25000000000 : ℝ)
  | 9 => (-444862837 / 125000000000 : ℝ)
  | 10 => (-3568138587 / 1000000000000 : ℝ)
  | 11 => (-3577268647 / 1000000000000 : ℝ)
  | 12 => (-1793145741 / 500000000000 : ℝ)
  | 13 => (-898801423 / 250000000000 : ℝ)
  | 14 => (-3604009869 / 1000000000000 : ℝ)
  | 15 => (-3612702601 / 1000000000000 : ℝ)
  | 16 => (-113165077 / 31250000000 : ℝ)
  | 17 => (-56714813 / 15625000000 : ℝ)
  | 18 => (-363809787 / 100000000000 : ℝ)
  | 19 => (-729266107 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch051Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1020 : ℝ) + (j.val : ℝ)) / 1600)
      (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch051Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch051Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1020 : ℝ) + (j.val : ℝ)) / 1600)
    (((1020 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch051Neg25WeightLower j.val) (hpThetaShiftTwoBatch051Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch051Neg25WeightLower, hpThetaShiftTwoBatch051Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch051Neg25_integral_bounds :
    (-638197857 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (51 / 80 : ℝ) ((51 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-624033553 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1020 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch051Lower hpThetaJensenCellsBatch051Upper
    hpThetaShiftTwoBatch051Neg25WeightLower hpThetaShiftTwoBatch051Neg25WeightUpper hpThetaJensenCellsBatch051_bounds hpThetaShiftTwoBatch051Neg25_weight_bounds
  have hl : (-638197857 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch051Lower j * hpThetaShiftTwoBatch051Neg25WeightLower j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftTwoBatch051Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftTwoBatch051Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch051Lower j * hpThetaShiftTwoBatch051Neg25WeightUpper j)
        (hpThetaJensenCellsBatch051Upper j * hpThetaShiftTwoBatch051Neg25WeightUpper j) / 1600) ≤ (-624033553 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch051Lower, hpThetaJensenCellsBatch051Upper,
      hpThetaShiftTwoBatch051Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1020 : ℝ) / 1600 = 51 / 80 by norm_num,
    show ((1020 : ℝ) + 20) / 1600 = (51 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch051Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch051Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch051Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch051Neg25_integral_bounds
end HodgeProofHP
