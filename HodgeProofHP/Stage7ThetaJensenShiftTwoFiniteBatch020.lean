/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch020

/-! Exact signed weight and batch integral certificates, batch 20 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch020Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5641789 / 125000000000 : ℝ)
  | 1 => (-9278353 / 200000000000 : ℝ)
  | 2 => (-23830751 / 500000000000 : ℝ)
  | 3 => (-48943463 / 1000000000000 : ℝ)
  | 4 => (-50237581 / 1000000000000 : ℝ)
  | 5 => (-12885947 / 250000000000 : ℝ)
  | 6 => (-5286201 / 100000000000 : ℝ)
  | 7 => (-13548043 / 250000000000 : ℝ)
  | 8 => (-3470887 / 62500000000 : ℝ)
  | 9 => (-14221997 / 250000000000 : ℝ)
  | 10 => (-1820421 / 31250000000 : ℝ)
  | 11 => (-59630553 / 1000000000000 : ℝ)
  | 12 => (-12203827 / 200000000000 : ℝ)
  | 13 => (-31209559 / 500000000000 : ℝ)
  | 14 => (-63830401 / 1000000000000 : ℝ)
  | 15 => (-522023 / 8000000000 : ℝ)
  | 16 => (-6668643 / 100000000000 : ℝ)
  | 17 => (-1362619 / 20000000000 : ℝ)
  | 18 => (-69586317 / 1000000000000 : ℝ)
  | 19 => (-14210481 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch020Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-21944601 / 500000000000 : ℝ)
  | 1 => (-45134311 / 1000000000000 : ℝ)
  | 2 => (-11597941 / 250000000000 : ℝ)
  | 3 => (-47661501 / 1000000000000 : ℝ)
  | 4 => (-24471731 / 500000000000 : ℝ)
  | 5 => (-2511879 / 50000000000 : ℝ)
  | 6 => (-51543787 / 1000000000000 : ℝ)
  | 7 => (-52862009 / 1000000000000 : ℝ)
  | 8 => (-54192171 / 1000000000000 : ℝ)
  | 9 => (-55534191 / 1000000000000 : ℝ)
  | 10 => (-56887987 / 1000000000000 : ℝ)
  | 11 => (-58253471 / 1000000000000 : ℝ)
  | 12 => (-7453819 / 125000000000 : ℝ)
  | 13 => (-30509567 / 500000000000 : ℝ)
  | 14 => (-62419117 / 1000000000000 : ℝ)
  | 15 => (-19947 / 312500000 : ℝ)
  | 16 => (-32626437 / 500000000000 : ℝ)
  | 17 => (-66686429 / 1000000000000 : ℝ)
  | 18 => (-68130949 / 1000000000000 : ℝ)
  | 19 => (-17396579 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch020Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((400 : ℝ) + (j.val : ℝ)) / 1600)
      (((400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch020Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch020Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((400 : ℝ) + (j.val : ℝ)) / 1600)
    (((400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch020Neg100WeightLower j.val) (hpThetaShiftTwoBatch020Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch020Neg100WeightLower, hpThetaShiftTwoBatch020Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch020Neg100_integral_bounds :
    (-683688711 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-659289673 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch020Lower hpThetaJensenCellsBatch020Upper
    hpThetaShiftTwoBatch020Neg100WeightLower hpThetaShiftTwoBatch020Neg100WeightUpper hpThetaJensenCellsBatch020_bounds hpThetaShiftTwoBatch020Neg100_weight_bounds
  have hl : (-683688711 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch020Lower j * hpThetaShiftTwoBatch020Neg100WeightLower j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftTwoBatch020Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftTwoBatch020Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch020Lower j * hpThetaShiftTwoBatch020Neg100WeightUpper j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftTwoBatch020Neg100WeightUpper j) / 1600) ≤ (-659289673 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftTwoBatch020Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (400 : ℝ) / 1600 = 20 / 80 by norm_num,
    show ((400 : ℝ) + 20) / 1600 = (20 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch020Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (8659133 / 250000000000 : ℝ)
  | 1 => (17002387 / 500000000000 : ℝ)
  | 2 => (8339559 / 250000000000 : ℝ)
  | 3 => (8174201 / 250000000000 : ℝ)
  | 4 => (32020367 / 1000000000000 : ℝ)
  | 5 => (7832203 / 250000000000 : ℝ)
  | 6 => (30622027 / 1000000000000 : ℝ)
  | 7 => (14949951 / 500000000000 : ℝ)
  | 8 => (3645291 / 125000000000 : ℝ)
  | 9 => (5681839 / 200000000000 : ℝ)
  | 10 => (13820197 / 500000000000 : ℝ)
  | 11 => (26855819 / 1000000000000 : ℝ)
  | 12 => (13027681 / 500000000000 : ℝ)
  | 13 => (12619459 / 500000000000 : ℝ)
  | 14 => (12203191 / 500000000000 : ℝ)
  | 15 => (23557649 / 1000000000000 : ℝ)
  | 16 => (2836577 / 125000000000 : ℝ)
  | 17 => (10905591 / 500000000000 : ℝ)
  | 18 => (4182649 / 200000000000 : ℝ)
  | 19 => (1249919 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch020Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (282029 / 8000000000 : ℝ)
  | 1 => (34636533 / 1000000000000 : ℝ)
  | 2 => (1360191 / 40000000000 : ℝ)
  | 3 => (33358237 / 1000000000000 : ℝ)
  | 4 => (6539361 / 200000000000 : ℝ)
  | 5 => (2001273 / 62500000000 : ℝ)
  | 6 => (31328813 / 1000000000000 : ℝ)
  | 7 => (7655507 / 250000000000 : ℝ)
  | 8 => (29899903 / 1000000000000 : ℝ)
  | 9 => (29162329 / 1000000000000 : ℝ)
  | 10 => (7102299 / 250000000000 : ℝ)
  | 11 => (5528079 / 200000000000 : ℝ)
  | 12 => (1342791 / 50000000000 : ℝ)
  | 13 => (26055363 / 1000000000000 : ℝ)
  | 14 => (25238919 / 1000000000000 : ℝ)
  | 15 => (24406383 / 1000000000000 : ℝ)
  | 16 => (471153 / 20000000000 : ℝ)
  | 17 => (22692617 / 1000000000000 : ℝ)
  | 18 => (21811183 / 1000000000000 : ℝ)
  | 19 => (10456623 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch020Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((400 : ℝ) + (j.val : ℝ)) / 1600)
      (((400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch020Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch020Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((400 : ℝ) + (j.val : ℝ)) / 1600)
    (((400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch020Neg65WeightLower j.val) (hpThetaShiftTwoBatch020Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch020Neg65WeightLower, hpThetaShiftTwoBatch020Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch020Neg65_integral_bounds :
    (163178077 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (169745191 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch020Lower hpThetaJensenCellsBatch020Upper
    hpThetaShiftTwoBatch020Neg65WeightLower hpThetaShiftTwoBatch020Neg65WeightUpper hpThetaJensenCellsBatch020_bounds hpThetaShiftTwoBatch020Neg65_weight_bounds
  have hl : (163178077 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch020Lower j * hpThetaShiftTwoBatch020Neg65WeightLower j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftTwoBatch020Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftTwoBatch020Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch020Lower j * hpThetaShiftTwoBatch020Neg65WeightUpper j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftTwoBatch020Neg65WeightUpper j) / 1600) ≤ (169745191 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftTwoBatch020Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (400 : ℝ) / 1600 = 20 / 80 by norm_num,
    show ((400 : ℝ) + 20) / 1600 = (20 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch020Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (20633141 / 200000000000 : ℝ)
  | 1 => (6458001 / 62500000000 : ℝ)
  | 2 => (51740401 / 500000000000 : ℝ)
  | 3 => (103623927 / 1000000000000 : ℝ)
  | 4 => (51878627 / 500000000000 : ℝ)
  | 5 => (51940323 / 500000000000 : ℝ)
  | 6 => (25998491 / 250000000000 : ℝ)
  | 7 => (6506067 / 62500000000 : ℝ)
  | 8 => (10418983 / 100000000000 : ℝ)
  | 9 => (104272099 / 1000000000000 : ℝ)
  | 10 => (5217187 / 50000000000 : ℝ)
  | 11 => (26101153 / 250000000000 : ℝ)
  | 12 => (6528411 / 62500000000 : ℝ)
  | 13 => (10449349 / 100000000000 : ℝ)
  | 14 => (52260607 / 500000000000 : ℝ)
  | 15 => (52268803 / 500000000000 : ℝ)
  | 16 => (4181433 / 40000000000 : ℝ)
  | 17 => (13064671 / 125000000000 : ℝ)
  | 18 => (104487009 / 1000000000000 : ℝ)
  | 19 => (20888921 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch020Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (103328017 / 1000000000000 : ℝ)
  | 1 => (103480803 / 1000000000000 : ℝ)
  | 2 => (12952991 / 125000000000 : ℝ)
  | 3 => (20751451 / 200000000000 : ℝ)
  | 4 => (103880647 / 1000000000000 : ℝ)
  | 5 => (20798793 / 200000000000 : ℝ)
  | 6 => (104097073 / 1000000000000 : ℝ)
  | 7 => (104189831 / 1000000000000 : ℝ)
  | 8 => (1042721 / 10000000000 : ℝ)
  | 9 => (104343741 / 1000000000000 : ℝ)
  | 10 => (104404613 / 1000000000000 : ℝ)
  | 11 => (104454577 / 1000000000000 : ℝ)
  | 12 => (104493491 / 1000000000000 : ℝ)
  | 13 => (20904243 / 200000000000 : ℝ)
  | 14 => (104537607 / 1000000000000 : ℝ)
  | 15 => (104542611 / 1000000000000 : ℝ)
  | 16 => (4181701 / 40000000000 : ℝ)
  | 17 => (52267913 / 500000000000 : ℝ)
  | 18 => (104517369 / 1000000000000 : ℝ)
  | 19 => (10448701 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch020Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((400 : ℝ) + (j.val : ℝ)) / 1600)
      (((400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch020Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch020Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((400 : ℝ) + (j.val : ℝ)) / 1600)
    (((400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch020Neg45WeightLower j.val) (hpThetaShiftTwoBatch020Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch020Neg45WeightLower, hpThetaShiftTwoBatch020Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch020Neg45_integral_bounds :
    (1220167237 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (154550269 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch020Lower hpThetaJensenCellsBatch020Upper
    hpThetaShiftTwoBatch020Neg45WeightLower hpThetaShiftTwoBatch020Neg45WeightUpper hpThetaJensenCellsBatch020_bounds hpThetaShiftTwoBatch020Neg45_weight_bounds
  have hl : (1220167237 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch020Lower j * hpThetaShiftTwoBatch020Neg45WeightLower j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftTwoBatch020Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftTwoBatch020Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch020Lower j * hpThetaShiftTwoBatch020Neg45WeightUpper j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftTwoBatch020Neg45WeightUpper j) / 1600) ≤ (154550269 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftTwoBatch020Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (400 : ℝ) / 1600 = 20 / 80 by norm_num,
    show ((400 : ℝ) + 20) / 1600 = (20 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch020Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (189470077 / 1000000000000 : ℝ)
  | 1 => (47691369 / 250000000000 : ℝ)
  | 2 => (96031141 / 500000000000 : ℝ)
  | 3 => (193360413 / 1000000000000 : ℝ)
  | 4 => (97329893 / 500000000000 : ℝ)
  | 5 => (195960319 / 1000000000000 : ℝ)
  | 6 => (24657741 / 125000000000 : ℝ)
  | 7 => (198564529 / 1000000000000 : ℝ)
  | 8 => (39973607 / 200000000000 : ℝ)
  | 9 => (5029309 / 25000000000 : ℝ)
  | 10 => (101238709 / 500000000000 : ℝ)
  | 11 => (2547289 / 12500000000 : ℝ)
  | 12 => (205089377 / 1000000000000 : ℝ)
  | 13 => (2063961 / 10000000000 : ℝ)
  | 14 => (207703199 / 1000000000000 : ℝ)
  | 15 => (209010581 / 1000000000000 : ℝ)
  | 16 => (42063631 / 200000000000 : ℝ)
  | 17 => (52906457 / 250000000000 : ℝ)
  | 18 => (42586701 / 200000000000 : ℝ)
  | 19 => (107120547 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch020Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (190765477 / 1000000000000 : ℝ)
  | 1 => (192062283 / 1000000000000 : ℝ)
  | 2 => (96680207 / 500000000000 : ℝ)
  | 3 => (194659787 / 1000000000000 : ℝ)
  | 4 => (76547 / 390625000 : ℝ)
  | 5 => (197261929 / 1000000000000 : ℝ)
  | 6 => (19856453 / 100000000000 : ℝ)
  | 7 => (49967009 / 250000000000 : ℝ)
  | 8 => (201172361 / 1000000000000 : ℝ)
  | 9 => (202477419 / 1000000000000 : ℝ)
  | 10 => (203783121 / 1000000000000 : ℝ)
  | 11 => (102544689 / 500000000000 : ℝ)
  | 12 => (206396101 / 1000000000000 : ℝ)
  | 13 => (259629 / 1250000000 : ℝ)
  | 14 => (104505291 / 500000000000 : ℝ)
  | 15 => (52579539 / 250000000000 : ℝ)
  | 16 => (211625829 / 1000000000000 : ℝ)
  | 17 => (106466753 / 500000000000 : ℝ)
  | 18 => (42848219 / 200000000000 : ℝ)
  | 19 => (107774249 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch020Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((400 : ℝ) + (j.val : ℝ)) / 1600)
      (((400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch020Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch020Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((400 : ℝ) + (j.val : ℝ)) / 1600)
    (((400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch020Neg25WeightLower j.val) (hpThetaShiftTwoBatch020Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch020Neg25WeightLower, hpThetaShiftTwoBatch020Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch020Neg25_integral_bounds :
    (590915453 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (481774273 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch020Lower hpThetaJensenCellsBatch020Upper
    hpThetaShiftTwoBatch020Neg25WeightLower hpThetaShiftTwoBatch020Neg25WeightUpper hpThetaJensenCellsBatch020_bounds hpThetaShiftTwoBatch020Neg25_weight_bounds
  have hl : (590915453 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch020Lower j * hpThetaShiftTwoBatch020Neg25WeightLower j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftTwoBatch020Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftTwoBatch020Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch020Lower j * hpThetaShiftTwoBatch020Neg25WeightUpper j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftTwoBatch020Neg25WeightUpper j) / 1600) ≤ (481774273 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftTwoBatch020Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (400 : ℝ) / 1600 = 20 / 80 by norm_num,
    show ((400 : ℝ) + 20) / 1600 = (20 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch020Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch020Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch020Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch020Neg25_integral_bounds
end HodgeProofHP
