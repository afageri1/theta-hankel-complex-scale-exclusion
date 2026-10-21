/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch025

/-! Exact signed weight and batch integral certificates, batch 25 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch025Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-20465193 / 100000000000 : ℝ)
  | 1 => (-103048249 / 500000000000 : ℝ)
  | 2 => (-207523057 / 1000000000000 : ℝ)
  | 3 => (-208930999 / 1000000000000 : ℝ)
  | 4 => (-210319707 / 1000000000000 : ℝ)
  | 5 => (-211688561 / 1000000000000 : ℝ)
  | 6 => (-213036929 / 1000000000000 : ℝ)
  | 7 => (-107182089 / 500000000000 : ℝ)
  | 8 => (-215669663 / 1000000000000 : ℝ)
  | 9 => (-43390547 / 200000000000 : ℝ)
  | 10 => (-1704787 / 7812500000 : ℝ)
  | 11 => (-54862251 / 250000000000 : ℝ)
  | 12 => (-220660867 / 1000000000000 : ℝ)
  | 13 => (-6932739 / 31250000000 : ℝ)
  | 14 => (-111504331 / 500000000000 : ℝ)
  | 15 => (-112071609 / 500000000000 : ℝ)
  | 16 => (-225250617 / 1000000000000 : ℝ)
  | 17 => (-45266031 / 200000000000 : ℝ)
  | 18 => (-227381117 / 1000000000000 : ℝ)
  | 19 => (-228402787 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch025Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3174843 / 15625000000 : ℝ)
  | 1 => (-204651929 / 1000000000000 : ℝ)
  | 2 => (-206096497 / 1000000000000 : ℝ)
  | 3 => (-12970191 / 62500000000 : ℝ)
  | 4 => (-104465499 / 500000000000 : ℝ)
  | 5 => (-105159853 / 500000000000 : ℝ)
  | 6 => (-2646107 / 12500000000 : ℝ)
  | 7 => (-1664351 / 7812500000 : ℝ)
  | 8 => (-214364177 / 1000000000000 : ℝ)
  | 9 => (-107834831 / 500000000000 : ℝ)
  | 10 => (-108476367 / 500000000000 : ℝ)
  | 11 => (-43642547 / 200000000000 : ℝ)
  | 12 => (-219449003 / 1000000000000 : ℝ)
  | 13 => (-110330433 / 500000000000 : ℝ)
  | 14 => (-221847647 / 1000000000000 : ℝ)
  | 15 => (-223008661 / 1000000000000 : ℝ)
  | 16 => (-224143217 / 1000000000000 : ℝ)
  | 17 => (-28156327 / 125000000000 : ℝ)
  | 18 => (-113165077 / 500000000000 : ℝ)
  | 19 => (-56845279 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch025Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((500 : ℝ) + (j.val : ℝ)) / 1600)
      (((500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch025Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch025Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((500 : ℝ) + (j.val : ℝ)) / 1600)
    (((500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch025Neg100WeightLower j.val) (hpThetaShiftTwoBatch025Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch025Neg100WeightLower, hpThetaShiftTwoBatch025Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch025Neg100_integral_bounds :
    (-1777771553 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-872036471 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch025Lower hpThetaJensenCellsBatch025Upper
    hpThetaShiftTwoBatch025Neg100WeightLower hpThetaShiftTwoBatch025Neg100WeightUpper hpThetaJensenCellsBatch025_bounds hpThetaShiftTwoBatch025Neg100_weight_bounds
  have hl : (-1777771553 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch025Lower j * hpThetaShiftTwoBatch025Neg100WeightLower j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftTwoBatch025Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftTwoBatch025Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch025Lower j * hpThetaShiftTwoBatch025Neg100WeightUpper j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftTwoBatch025Neg100WeightUpper j) / 1600) ≤ (-872036471 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftTwoBatch025Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (500 : ℝ) / 1600 = 25 / 80 by norm_num,
    show ((500 : ℝ) + 20) / 1600 = (25 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch025Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-23119203 / 200000000000 : ℝ)
  | 1 => (-118061373 / 1000000000000 : ℝ)
  | 2 => (-60272679 / 500000000000 : ℝ)
  | 3 => (-123047883 / 1000000000000 : ℝ)
  | 4 => (-62784427 / 500000000000 : ℝ)
  | 5 => (-5124327 / 40000000000 : ℝ)
  | 6 => (-130665749 / 1000000000000 : ℝ)
  | 7 => (-13324147 / 100000000000 : ℝ)
  | 8 => (-135835233 / 1000000000000 : ℝ)
  | 9 => (-69223463 / 500000000000 : ℝ)
  | 10 => (-70538217 / 500000000000 : ℝ)
  | 11 => (-3593091 / 25000000000 : ℝ)
  | 12 => (-146388421 / 1000000000000 : ℝ)
  | 13 => (-149070649 / 1000000000000 : ℝ)
  | 14 => (-37942549 / 250000000000 : ℝ)
  | 15 => (-77243463 / 500000000000 : ℝ)
  | 16 => (-157220701 / 1000000000000 : ℝ)
  | 17 => (-79985689 / 500000000000 : ℝ)
  | 18 => (-40684703 / 250000000000 : ℝ)
  | 19 => (-3310457 / 20000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch025Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-14143671 / 125000000000 : ℝ)
  | 1 => (-57798007 / 500000000000 : ℝ)
  | 2 => (-29515343 / 250000000000 : ℝ)
  | 3 => (-120545357 / 1000000000000 : ℝ)
  | 4 => (-61523941 / 500000000000 : ℝ)
  | 5 => (-125568853 / 1000000000000 : ℝ)
  | 6 => (-64054087 / 500000000000 : ℝ)
  | 7 => (-32666437 / 250000000000 : ℝ)
  | 8 => (-133241469 / 1000000000000 : ℝ)
  | 9 => (-4244851 / 31250000000 : ℝ)
  | 10 => (-5537877 / 40000000000 : ℝ)
  | 11 => (-141076433 / 1000000000000 : ℝ)
  | 12 => (-143723639 / 1000000000000 : ℝ)
  | 13 => (-7319421 / 50000000000 : ℝ)
  | 14 => (-18633831 / 125000000000 : ℝ)
  | 15 => (-30354039 / 200000000000 : ℝ)
  | 16 => (-6179477 / 40000000000 : ℝ)
  | 17 => (-1572207 / 10000000000 : ℝ)
  | 18 => (-159971377 / 1000000000000 : ℝ)
  | 19 => (-162738811 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch025Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((500 : ℝ) + (j.val : ℝ)) / 1600)
      (((500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch025Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch025Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((500 : ℝ) + (j.val : ℝ)) / 1600)
    (((500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch025Neg65WeightLower j.val) (hpThetaShiftTwoBatch025Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch025Neg65WeightLower, hpThetaShiftTwoBatch025Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch025Neg65_integral_bounds :
    (-28607067 / 25000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-554007981 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch025Lower hpThetaJensenCellsBatch025Upper
    hpThetaShiftTwoBatch025Neg65WeightLower hpThetaShiftTwoBatch025Neg65WeightUpper hpThetaJensenCellsBatch025_bounds hpThetaShiftTwoBatch025Neg65_weight_bounds
  have hl : (-28607067 / 25000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch025Lower j * hpThetaShiftTwoBatch025Neg65WeightLower j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftTwoBatch025Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftTwoBatch025Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch025Lower j * hpThetaShiftTwoBatch025Neg65WeightUpper j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftTwoBatch025Neg65WeightUpper j) / 1600) ≤ (-554007981 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftTwoBatch025Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (500 : ℝ) / 1600 = 25 / 80 by norm_num,
    show ((500 : ℝ) + 20) / 1600 = (25 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch025Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (23803073 / 500000000000 : ℝ)
  | 1 => (9216489 / 200000000000 : ℝ)
  | 2 => (5566869 / 125000000000 : ℝ)
  | 3 => (21481773 / 500000000000 : ℝ)
  | 4 => (41368107 / 1000000000000 : ℝ)
  | 5 => (9937129 / 250000000000 : ℝ)
  | 6 => (19052327 / 500000000000 : ℝ)
  | 7 => (18218203 / 500000000000 : ℝ)
  | 8 => (4342957 / 125000000000 : ℝ)
  | 9 => (33026289 / 1000000000000 : ℝ)
  | 10 => (31284191 / 1000000000000 : ℝ)
  | 11 => (7379313 / 250000000000 : ℝ)
  | 12 => (27725359 / 1000000000000 : ℝ)
  | 13 => (12954201 / 500000000000 : ℝ)
  | 14 => (12033137 / 500000000000 : ℝ)
  | 15 => (22198867 / 1000000000000 : ℝ)
  | 16 => (10153037 / 500000000000 : ℝ)
  | 17 => (1149237 / 62500000000 : ℝ)
  | 18 => (4110979 / 250000000000 : ℝ)
  | 19 => (1809293 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch025Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (49106177 / 1000000000000 : ℝ)
  | 1 => (47606147 / 1000000000000 : ℝ)
  | 2 => (23041223 / 500000000000 : ℝ)
  | 3 => (44534953 / 1000000000000 : ℝ)
  | 4 => (42963547 / 1000000000000 : ℝ)
  | 5 => (10342027 / 250000000000 : ℝ)
  | 6 => (39748517 / 1000000000000 : ℝ)
  | 7 => (7620931 / 200000000000 : ℝ)
  | 8 => (36436407 / 1000000000000 : ℝ)
  | 9 => (34743657 / 1000000000000 : ℝ)
  | 10 => (3302629 / 100000000000 : ℝ)
  | 11 => (977631 / 31250000000 : ℝ)
  | 12 => (29517253 / 1000000000000 : ℝ)
  | 13 => (346567 / 12500000000 : ℝ)
  | 14 => (25908403 / 1000000000000 : ℝ)
  | 15 => (962651 / 40000000000 : ℝ)
  | 16 => (5549717 / 250000000000 : ℝ)
  | 17 => (812243 / 40000000000 : ℝ)
  | 18 => (18387793 / 1000000000000 : ℝ)
  | 19 => (16443917 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch025Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((500 : ℝ) + (j.val : ℝ)) / 1600)
      (((500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch025Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch025Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((500 : ℝ) + (j.val : ℝ)) / 1600)
    (((500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch025Neg45WeightLower j.val) (hpThetaShiftTwoBatch025Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch025Neg45WeightLower, hpThetaShiftTwoBatch025Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch025Neg45_integral_bounds :
    (32323509 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (276201373 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch025Lower hpThetaJensenCellsBatch025Upper
    hpThetaShiftTwoBatch025Neg45WeightLower hpThetaShiftTwoBatch025Neg45WeightUpper hpThetaJensenCellsBatch025_bounds hpThetaShiftTwoBatch025Neg45_weight_bounds
  have hl : (32323509 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch025Lower j * hpThetaShiftTwoBatch025Neg45WeightLower j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftTwoBatch025Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftTwoBatch025Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch025Lower j * hpThetaShiftTwoBatch025Neg45WeightUpper j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftTwoBatch025Neg45WeightUpper j) / 1600) ≤ (276201373 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftTwoBatch025Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (500 : ℝ) / 1600 = 25 / 80 by norm_num,
    show ((500 : ℝ) + 20) / 1600 = (25 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch025Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (309568877 / 1000000000000 : ℝ)
  | 1 => (62093753 / 200000000000 : ℝ)
  | 2 => (2490863 / 8000000000 : ℝ)
  | 3 => (19514753 / 62500000000 : ℝ)
  | 4 => (313103121 / 1000000000000 : ℝ)
  | 5 => (78489733 / 250000000000 : ℝ)
  | 6 => (314803319 / 1000000000000 : ℝ)
  | 7 => (157818059 / 500000000000 : ℝ)
  | 8 => (63291433 / 200000000000 : ℝ)
  | 9 => (158633147 / 500000000000 : ℝ)
  | 10 => (318063341 / 1000000000000 : ℝ)
  | 11 => (318848139 / 1000000000000 : ℝ)
  | 12 => (159810261 / 500000000000 : ℝ)
  | 13 => (160190161 / 500000000000 : ℝ)
  | 14 => (321127371 / 1000000000000 : ℝ)
  | 15 => (643723 / 2000000000 : ℝ)
  | 16 => (16129127 / 50000000000 : ℝ)
  | 17 => (323290321 / 1000000000000 : ℝ)
  | 18 => (323984673 / 1000000000000 : ℝ)
  | 19 => (20291589 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch025Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (155234383 / 500000000000 : ℝ)
  | 1 => (77839469 / 250000000000 : ℝ)
  | 2 => (312236049 / 1000000000000 : ℝ)
  | 3 => (156551561 / 500000000000 : ℝ)
  | 4 => (313958933 / 1000000000000 : ℝ)
  | 5 => (7870083 / 25000000000 : ℝ)
  | 6 => (315636119 / 1000000000000 : ℝ)
  | 7 => (158228583 / 500000000000 : ℝ)
  | 8 => (63453259 / 200000000000 : ℝ)
  | 9 => (159031671 / 500000000000 : ℝ)
  | 10 => (15942407 / 50000000000 : ℝ)
  | 11 => (319620523 / 1000000000000 : ℝ)
  | 12 => (320380323 / 1000000000000 : ℝ)
  | 13 => (80281843 / 250000000000 : ℝ)
  | 14 => (321861501 / 1000000000000 : ℝ)
  | 15 => (322582541 / 1000000000000 : ℝ)
  | 16 => (161645161 / 500000000000 : ℝ)
  | 17 => (161992337 / 500000000000 : ℝ)
  | 18 => (12986617 / 40000000000 : ℝ)
  | 19 => (325332403 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch025Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((500 : ℝ) + (j.val : ℝ)) / 1600)
      (((500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch025Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch025Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((500 : ℝ) + (j.val : ℝ)) / 1600)
    (((500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch025Neg25WeightLower j.val) (hpThetaShiftTwoBatch025Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch025Neg25WeightLower, hpThetaShiftTwoBatch025Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch025Neg25_integral_bounds :
    (641330603 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (2606128691 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch025Lower hpThetaJensenCellsBatch025Upper
    hpThetaShiftTwoBatch025Neg25WeightLower hpThetaShiftTwoBatch025Neg25WeightUpper hpThetaJensenCellsBatch025_bounds hpThetaShiftTwoBatch025Neg25_weight_bounds
  have hl : (641330603 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch025Lower j * hpThetaShiftTwoBatch025Neg25WeightLower j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftTwoBatch025Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftTwoBatch025Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch025Lower j * hpThetaShiftTwoBatch025Neg25WeightUpper j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftTwoBatch025Neg25WeightUpper j) / 1600) ≤ (2606128691 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftTwoBatch025Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (500 : ℝ) / 1600 = 25 / 80 by norm_num,
    show ((500 : ℝ) + 20) / 1600 = (25 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch025Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch025Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch025Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch025Neg25_integral_bounds
end HodgeProofHP
