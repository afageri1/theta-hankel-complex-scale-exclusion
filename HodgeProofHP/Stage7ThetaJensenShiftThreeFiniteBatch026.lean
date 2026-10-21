/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch026

/-! Exact signed weight and batch integral certificates, batch 26 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch026Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1477299 / 1000000000000 : ℝ)
  | 1 => (-375893 / 250000000000 : ℝ)
  | 2 => (-153003 / 100000000000 : ℝ)
  | 3 => (-24323 / 15625000000 : ℝ)
  | 4 => (-197937 / 125000000000 : ℝ)
  | 5 => (-6291 / 3906250000 : ℝ)
  | 6 => (-204709 / 125000000000 : ℝ)
  | 7 => (-83251 / 50000000000 : ℝ)
  | 8 => (-211567 / 125000000000 : ℝ)
  | 9 => (-860109 / 500000000000 : ℝ)
  | 10 => (-1748061 / 1000000000000 : ℝ)
  | 11 => (-888031 / 500000000000 : ℝ)
  | 12 => (-902109 / 500000000000 : ℝ)
  | 13 => (-73301 / 40000000000 : ℝ)
  | 14 => (-930489 / 500000000000 : ℝ)
  | 15 => (-944787 / 500000000000 : ℝ)
  | 16 => (-1918309 / 1000000000000 : ℝ)
  | 17 => (-973589 / 500000000000 : ℝ)
  | 18 => (-988089 / 500000000000 : ℝ)
  | 19 => (-1002651 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch026Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-290243 / 200000000000 : ℝ)
  | 1 => (-738649 / 500000000000 : ℝ)
  | 2 => (-1503571 / 1000000000000 : ℝ)
  | 3 => (-1530029 / 1000000000000 : ℝ)
  | 4 => (-1556671 / 1000000000000 : ℝ)
  | 5 => (-316699 / 200000000000 : ℝ)
  | 6 => (-322099 / 200000000000 : ℝ)
  | 7 => (-1637671 / 1000000000000 : ℝ)
  | 8 => (-1665019 / 1000000000000 : ℝ)
  | 9 => (-338507 / 200000000000 : ℝ)
  | 10 => (-1720217 / 1000000000000 : ℝ)
  | 11 => (-87403 / 50000000000 : ℝ)
  | 12 => (-1776061 / 1000000000000 : ℝ)
  | 13 => (-1804217 / 1000000000000 : ℝ)
  | 14 => (-458131 / 250000000000 : ℝ)
  | 15 => (-1860977 / 1000000000000 : ℝ)
  | 16 => (-1889573 / 1000000000000 : ℝ)
  | 17 => (-479577 / 250000000000 : ℝ)
  | 18 => (-1947177 / 1000000000000 : ℝ)
  | 19 => (-1976177 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch026Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((520 : ℝ) + (j.val : ℝ)) / 1600)
      (((520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch026Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch026Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((520 : ℝ) + (j.val : ℝ)) / 1600)
    (((520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch026Neg100WeightLower j.val) (hpThetaShiftThreeBatch026Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch026Neg100WeightLower, hpThetaShiftThreeBatch026Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch026Neg100_integral_bounds :
    (-6513473 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-12647263 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch026Lower hpThetaJensenCellsBatch026Upper
    hpThetaShiftThreeBatch026Neg100WeightLower hpThetaShiftThreeBatch026Neg100WeightUpper hpThetaJensenCellsBatch026_bounds hpThetaShiftThreeBatch026Neg100_weight_bounds
  have hl : (-6513473 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch026Lower j * hpThetaShiftThreeBatch026Neg100WeightLower j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftThreeBatch026Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftThreeBatch026Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch026Lower j * hpThetaShiftThreeBatch026Neg100WeightUpper j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftThreeBatch026Neg100WeightUpper j) / 1600) ≤ (-12647263 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftThreeBatch026Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (520 : ℝ) / 1600 = 26 / 80 by norm_num,
    show ((520 : ℝ) + 20) / 1600 = (26 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch026Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-83471 / 1000000000000 : ℝ)
  | 1 => (-51841 / 500000000000 : ℝ)
  | 2 => (-62127 / 500000000000 : ℝ)
  | 3 => (-145189 / 1000000000000 : ℝ)
  | 4 => (-16649 / 100000000000 : ℝ)
  | 5 => (-147 / 781250000 : ℝ)
  | 6 => (-105101 / 500000000000 : ℝ)
  | 7 => (-232617 / 1000000000000 : ℝ)
  | 8 => (-25541 / 100000000000 : ℝ)
  | 9 => (-139291 / 500000000000 : ℝ)
  | 10 => (-37767 / 125000000000 : ℝ)
  | 11 => (-13043 / 40000000000 : ℝ)
  | 12 => (-350401 / 1000000000000 : ℝ)
  | 13 => (-375117 / 1000000000000 : ℝ)
  | 14 => (-16009 / 40000000000 : ℝ)
  | 15 => (-1663 / 3906250000 : ℝ)
  | 16 => (-451629 / 1000000000000 : ℝ)
  | 17 => (-477929 / 1000000000000 : ℝ)
  | 18 => (-504631 / 1000000000000 : ℝ)
  | 19 => (-265869 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch026Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-63617 / 1000000000000 : ℝ)
  | 1 => (-8347 / 100000000000 : ℝ)
  | 2 => (-103681 / 1000000000000 : ℝ)
  | 3 => (-124253 / 1000000000000 : ℝ)
  | 4 => (-36297 / 250000000000 : ℝ)
  | 5 => (-166489 / 1000000000000 : ℝ)
  | 6 => (-188159 / 1000000000000 : ℝ)
  | 7 => (-210201 / 1000000000000 : ℝ)
  | 8 => (-29077 / 125000000000 : ℝ)
  | 9 => (-255409 / 1000000000000 : ℝ)
  | 10 => (-278581 / 1000000000000 : ℝ)
  | 11 => (-60427 / 200000000000 : ℝ)
  | 12 => (-163037 / 500000000000 : ℝ)
  | 13 => (-219 / 625000000 : ℝ)
  | 14 => (-93779 / 250000000000 : ℝ)
  | 15 => (-12507 / 31250000000 : ℝ)
  | 16 => (-425727 / 1000000000000 : ℝ)
  | 17 => (-112907 / 250000000000 : ℝ)
  | 18 => (-59741 / 125000000000 : ℝ)
  | 19 => (-50463 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch026Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((520 : ℝ) + (j.val : ℝ)) / 1600)
      (((520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch026Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch026Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((520 : ℝ) + (j.val : ℝ)) / 1600)
    (((520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch026Neg70WeightLower j.val) (hpThetaShiftThreeBatch026Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch026Neg70WeightLower, hpThetaShiftThreeBatch026Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch026Neg70_integral_bounds :
    (-2204663 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-125119 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch026Lower hpThetaJensenCellsBatch026Upper
    hpThetaShiftThreeBatch026Neg70WeightLower hpThetaShiftThreeBatch026Neg70WeightUpper hpThetaJensenCellsBatch026_bounds hpThetaShiftThreeBatch026Neg70_weight_bounds
  have hl : (-2204663 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch026Lower j * hpThetaShiftThreeBatch026Neg70WeightLower j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftThreeBatch026Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftThreeBatch026Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch026Lower j * hpThetaShiftThreeBatch026Neg70WeightUpper j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftThreeBatch026Neg70WeightUpper j) / 1600) ≤ (-125119 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftThreeBatch026Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (520 : ℝ) / 1600 = 26 / 80 by norm_num,
    show ((520 : ℝ) + 20) / 1600 = (26 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch026Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1134517 / 500000000000 : ℝ)
  | 1 => (2274769 / 1000000000000 : ℝ)
  | 2 => (456061 / 200000000000 : ℝ)
  | 3 => (2285637 / 1000000000000 : ℝ)
  | 4 => (1145381 / 500000000000 : ℝ)
  | 5 => (573919 / 250000000000 : ℝ)
  | 6 => (18403 / 8000000000 : ℝ)
  | 7 => (460971 / 200000000000 : ℝ)
  | 8 => (2309113 / 1000000000000 : ℝ)
  | 9 => (2313143 / 1000000000000 : ℝ)
  | 10 => (1158471 / 500000000000 : ℝ)
  | 11 => (2320507 / 1000000000000 : ℝ)
  | 12 => (290479 / 125000000000 : ℝ)
  | 13 => (1163457 / 500000000000 : ℝ)
  | 14 => (2329749 / 1000000000000 : ℝ)
  | 15 => (583083 / 250000000000 : ℝ)
  | 16 => (2334659 / 1000000000000 : ℝ)
  | 17 => (1168363 / 500000000000 : ℝ)
  | 18 => (2338529 / 1000000000000 : ℝ)
  | 19 => (73127 / 31250000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch026Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (227477 / 100000000000 : ℝ)
  | 1 => (1140153 / 500000000000 : ℝ)
  | 2 => (1142819 / 500000000000 : ℝ)
  | 3 => (2290763 / 1000000000000 : ℝ)
  | 4 => (2295677 / 1000000000000 : ℝ)
  | 5 => (287547 / 125000000000 : ℝ)
  | 6 => (288107 / 125000000000 : ℝ)
  | 7 => (1154557 / 500000000000 : ℝ)
  | 8 => (289143 / 125000000000 : ℝ)
  | 9 => (2316943 / 1000000000000 : ℝ)
  | 10 => (580127 / 250000000000 : ℝ)
  | 11 => (2323833 / 1000000000000 : ℝ)
  | 12 => (465383 / 200000000000 : ℝ)
  | 13 => (9319 / 4000000000 : ℝ)
  | 14 => (2332333 / 1000000000000 : ℝ)
  | 15 => (116733 / 50000000000 : ℝ)
  | 16 => (2336727 / 1000000000000 : ℝ)
  | 17 => (233853 / 100000000000 : ℝ)
  | 18 => (468013 / 200000000000 : ℝ)
  | 19 => (1170663 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch026Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((520 : ℝ) + (j.val : ℝ)) / 1600)
      (((520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch026Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch026Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((520 : ℝ) + (j.val : ℝ)) / 1600)
    (((520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch026Neg45WeightLower j.val) (hpThetaShiftThreeBatch026Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch026Neg45WeightLower, hpThetaShiftThreeBatch026Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch026Neg45_integral_bounds :
    (8569793 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (543733 / 31250000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch026Lower hpThetaJensenCellsBatch026Upper
    hpThetaShiftThreeBatch026Neg45WeightLower hpThetaShiftThreeBatch026Neg45WeightUpper hpThetaJensenCellsBatch026_bounds hpThetaShiftThreeBatch026Neg45_weight_bounds
  have hl : (8569793 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch026Lower j * hpThetaShiftThreeBatch026Neg45WeightLower j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftThreeBatch026Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftThreeBatch026Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch026Lower j * hpThetaShiftThreeBatch026Neg45WeightUpper j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftThreeBatch026Neg45WeightUpper j) / 1600) ≤ (543733 / 31250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftThreeBatch026Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (520 : ℝ) / 1600 = 26 / 80 by norm_num,
    show ((520 : ℝ) + 20) / 1600 = (26 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch026Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (5046007 / 1000000000000 : ℝ)
  | 1 => (101777 / 20000000000 : ℝ)
  | 2 => (1026377 / 200000000000 : ℝ)
  | 3 => (646889 / 125000000000 : ℝ)
  | 4 => (5218531 / 1000000000000 : ℝ)
  | 5 => (5262139 / 1000000000000 : ℝ)
  | 6 => (1061187 / 200000000000 : ℝ)
  | 7 => (33437 / 6250000000 : ℝ)
  | 8 => (539409 / 100000000000 : ℝ)
  | 9 => (1087689 / 200000000000 : ℝ)
  | 10 => (685373 / 125000000000 : ℝ)
  | 11 => (1105541 / 200000000000 : ℝ)
  | 12 => (5572607 / 1000000000000 : ℝ)
  | 13 => (5617689 / 1000000000000 : ℝ)
  | 14 => (113259 / 20000000000 : ℝ)
  | 15 => (5708387 / 1000000000000 : ℝ)
  | 16 => (5753999 / 1000000000000 : ℝ)
  | 17 => (1159957 / 200000000000 : ℝ)
  | 18 => (5845743 / 1000000000000 : ℝ)
  | 19 => (5891873 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch026Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5088851 / 1000000000000 : ℝ)
  | 1 => (2565943 / 500000000000 : ℝ)
  | 2 => (5175113 / 1000000000000 : ℝ)
  | 3 => (1304633 / 250000000000 : ℝ)
  | 4 => (263107 / 50000000000 : ℝ)
  | 5 => (331621 / 62500000000 : ℝ)
  | 6 => (5349921 / 1000000000000 : ℝ)
  | 7 => (5394091 / 1000000000000 : ℝ)
  | 8 => (2719223 / 500000000000 : ℝ)
  | 9 => (1096597 / 200000000000 : ℝ)
  | 10 => (2763853 / 500000000000 : ℝ)
  | 11 => (2721 / 488281250 : ℝ)
  | 12 => (561769 / 100000000000 : ℝ)
  | 13 => (5662951 / 1000000000000 : ℝ)
  | 14 => (1427097 / 250000000000 : ℝ)
  | 15 => (2877 / 500000000 : ℝ)
  | 16 => (2899893 / 500000000000 : ℝ)
  | 17 => (365359 / 62500000000 : ℝ)
  | 18 => (2945937 / 500000000000 : ℝ)
  | 19 => (1484543 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch026Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((520 : ℝ) + (j.val : ℝ)) / 1600)
      (((520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch026Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch026Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((520 : ℝ) + (j.val : ℝ)) / 1600)
    (((520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch026Neg25WeightLower j.val) (hpThetaShiftThreeBatch026Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch026Neg25WeightLower, hpThetaShiftThreeBatch026Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch026Neg25_integral_bounds :
    (40479797 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (20682001 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch026Lower hpThetaJensenCellsBatch026Upper
    hpThetaShiftThreeBatch026Neg25WeightLower hpThetaShiftThreeBatch026Neg25WeightUpper hpThetaJensenCellsBatch026_bounds hpThetaShiftThreeBatch026Neg25_weight_bounds
  have hl : (40479797 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch026Lower j * hpThetaShiftThreeBatch026Neg25WeightLower j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftThreeBatch026Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftThreeBatch026Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch026Lower j * hpThetaShiftThreeBatch026Neg25WeightUpper j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftThreeBatch026Neg25WeightUpper j) / 1600) ≤ (20682001 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftThreeBatch026Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (520 : ℝ) / 1600 = 26 / 80 by norm_num,
    show ((520 : ℝ) + 20) / 1600 = (26 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch026Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch026Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch026Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch026Neg25_integral_bounds
end HodgeProofHP
