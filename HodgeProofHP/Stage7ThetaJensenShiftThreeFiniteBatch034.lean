/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch034

/-! Exact signed weight and batch integral certificates, batch 34 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch034Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-75971 / 31250000000 : ℝ)
  | 1 => (-1174489 / 500000000000 : ℝ)
  | 2 => (-2264461 / 1000000000000 : ℝ)
  | 3 => (-136093 / 62500000000 : ℝ)
  | 4 => (-261003 / 125000000000 : ℝ)
  | 5 => (-1996037 / 1000000000000 : ℝ)
  | 6 => (-475373 / 250000000000 : ℝ)
  | 7 => (-360871 / 200000000000 : ℝ)
  | 8 => (-1704591 / 1000000000000 : ℝ)
  | 9 => (-801083 / 500000000000 : ℝ)
  | 10 => (-748523 / 500000000000 : ℝ)
  | 11 => (-694597 / 500000000000 : ℝ)
  | 12 => (-1278577 / 1000000000000 : ℝ)
  | 13 => (-1165159 / 1000000000000 : ℝ)
  | 14 => (-209781 / 200000000000 : ℝ)
  | 15 => (-46489 / 50000000000 : ℝ)
  | 16 => (-807747 / 1000000000000 : ℝ)
  | 17 => (-170693 / 250000000000 : ℝ)
  | 18 => (-277409 / 500000000000 : ℝ)
  | 19 => (-8477 / 20000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch034Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2348977 / 1000000000000 : ℝ)
  | 1 => (-113223 / 50000000000 : ℝ)
  | 2 => (-2177487 / 1000000000000 : ℝ)
  | 3 => (-2088023 / 1000000000000 : ℝ)
  | 4 => (-499009 / 250000000000 : ℝ)
  | 5 => (-1901491 / 1000000000000 : ℝ)
  | 6 => (-902177 / 500000000000 : ℝ)
  | 7 => (-170459 / 100000000000 : ℝ)
  | 8 => (-320433 / 200000000000 : ℝ)
  | 9 => (-299409 / 200000000000 : ℝ)
  | 10 => (-1389193 / 1000000000000 : ℝ)
  | 11 => (-79911 / 62500000000 : ℝ)
  | 12 => (-582579 / 500000000000 : ℝ)
  | 13 => (-131113 / 125000000000 : ℝ)
  | 14 => (-929779 / 1000000000000 : ℝ)
  | 15 => (-403873 / 500000000000 : ℝ)
  | 16 => (-682771 / 1000000000000 : ℝ)
  | 17 => (-554817 / 1000000000000 : ℝ)
  | 18 => (-423849 / 1000000000000 : ℝ)
  | 19 => (-28983 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch034Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((680 : ℝ) + (j.val : ℝ)) / 1600)
      (((680 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch034Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch034Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((680 : ℝ) + (j.val : ℝ)) / 1600)
    (((680 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch034Neg100WeightLower j.val) (hpThetaShiftThreeBatch034Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch034Neg100WeightLower, hpThetaShiftThreeBatch034Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch034Neg100_integral_bounds :
    (-1237919 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-1134363 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (680 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch034Lower hpThetaJensenCellsBatch034Upper
    hpThetaShiftThreeBatch034Neg100WeightLower hpThetaShiftThreeBatch034Neg100WeightUpper hpThetaJensenCellsBatch034_bounds hpThetaShiftThreeBatch034Neg100_weight_bounds
  have hl : (-1237919 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch034Lower j * hpThetaShiftThreeBatch034Neg100WeightLower j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftThreeBatch034Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftThreeBatch034Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch034Lower j * hpThetaShiftThreeBatch034Neg100WeightUpper j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftThreeBatch034Neg100WeightUpper j) / 1600) ≤ (-1134363 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftThreeBatch034Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (680 : ℝ) / 1600 = 34 / 80 by norm_num,
    show ((680 : ℝ) + 20) / 1600 = (34 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch034Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1692393 / 200000000000 : ℝ)
  | 1 => (-8535279 / 1000000000000 : ℝ)
  | 2 => (-860841 / 100000000000 : ℝ)
  | 3 => (-4340671 / 500000000000 : ℝ)
  | 4 => (-4377029 / 500000000000 : ℝ)
  | 5 => (-8826541 / 1000000000000 : ℝ)
  | 6 => (-1112347 / 125000000000 : ℝ)
  | 7 => (-1121343 / 125000000000 : ℝ)
  | 8 => (-9042429 / 1000000000000 : ℝ)
  | 9 => (-9113813 / 1000000000000 : ℝ)
  | 10 => (-4592439 / 500000000000 : ℝ)
  | 11 => (-4627803 / 500000000000 : ℝ)
  | 12 => (-9325979 / 1000000000000 : ℝ)
  | 13 => (-4697989 / 500000000000 : ℝ)
  | 14 => (-591599 / 62500000000 : ℝ)
  | 15 => (-9534779 / 1000000000000 : ℝ)
  | 16 => (-4801771 / 500000000000 : ℝ)
  | 17 => (-4835927 / 500000000000 : ℝ)
  | 18 => (-1947939 / 200000000000 : ℝ)
  | 19 => (-1961409 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch034Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4194241 / 500000000000 : ℝ)
  | 1 => (-2115491 / 250000000000 : ℝ)
  | 2 => (-4267639 / 500000000000 : ℝ)
  | 3 => (-8608409 / 1000000000000 : ℝ)
  | 4 => (-8681341 / 1000000000000 : ℝ)
  | 5 => (-8754057 / 1000000000000 : ℝ)
  | 6 => (-441327 / 50000000000 : ℝ)
  | 7 => (-355951 / 40000000000 : ℝ)
  | 8 => (-8970743 / 1000000000000 : ℝ)
  | 9 => (-2260607 / 250000000000 : ℝ)
  | 10 => (-2278453 / 250000000000 : ℝ)
  | 11 => (-9184877 / 1000000000000 : ℝ)
  | 12 => (-1851121 / 200000000000 : ℝ)
  | 13 => (-4662989 / 500000000000 : ℝ)
  | 14 => (-9395977 / 1000000000000 : ℝ)
  | 15 => (-9465583 / 1000000000000 : ℝ)
  | 16 => (-4767389 / 500000000000 : ℝ)
  | 17 => (-9603541 / 1000000000000 : ℝ)
  | 18 => (-9671853 / 1000000000000 : ℝ)
  | 19 => (-4869847 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch034Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((680 : ℝ) + (j.val : ℝ)) / 1600)
      (((680 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch034Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch034Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((680 : ℝ) + (j.val : ℝ)) / 1600)
    (((680 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch034Neg70WeightLower j.val) (hpThetaShiftThreeBatch034Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch034Neg70WeightLower, hpThetaShiftThreeBatch034Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch034Neg70_integral_bounds :
    (-3701897 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-5789099 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (680 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch034Lower hpThetaJensenCellsBatch034Upper
    hpThetaShiftThreeBatch034Neg70WeightLower hpThetaShiftThreeBatch034Neg70WeightUpper hpThetaJensenCellsBatch034_bounds hpThetaShiftThreeBatch034Neg70_weight_bounds
  have hl : (-3701897 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch034Lower j * hpThetaShiftThreeBatch034Neg70WeightLower j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftThreeBatch034Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftThreeBatch034Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch034Lower j * hpThetaShiftThreeBatch034Neg70WeightUpper j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftThreeBatch034Neg70WeightUpper j) / 1600) ≤ (-5789099 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftThreeBatch034Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (680 : ℝ) / 1600 = 34 / 80 by norm_num,
    show ((680 : ℝ) + 20) / 1600 = (34 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch034Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2647797 / 1000000000000 : ℝ)
  | 1 => (-684559 / 250000000000 : ℝ)
  | 2 => (-2829697 / 1000000000000 : ℝ)
  | 3 => (-1461091 / 500000000000 : ℝ)
  | 4 => (-3015697 / 1000000000000 : ℝ)
  | 5 => (-622049 / 200000000000 : ℝ)
  | 6 => (-320583 / 100000000000 : ℝ)
  | 7 => (-660491 / 200000000000 : ℝ)
  | 8 => (-27201 / 8000000000 : ℝ)
  | 9 => (-874711 / 250000000000 : ℝ)
  | 10 => (-1799307 / 500000000000 : ℝ)
  | 11 => (-3699439 / 1000000000000 : ℝ)
  | 12 => (-3801323 / 1000000000000 : ℝ)
  | 13 => (-3904269 / 1000000000000 : ℝ)
  | 14 => (-100207 / 25000000000 : ℝ)
  | 15 => (-51417 / 12500000000 : ℝ)
  | 16 => (-527439 / 125000000000 : ℝ)
  | 17 => (-2163369 / 500000000000 : ℝ)
  | 18 => (-4435043 / 1000000000000 : ℝ)
  | 19 => (-1136107 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch034Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1279187 / 500000000000 : ℝ)
  | 1 => (-661949 / 250000000000 : ℝ)
  | 2 => (-547647 / 200000000000 : ℝ)
  | 3 => (-22107 / 7812500000 : ℝ)
  | 4 => (-2922181 / 1000000000000 : ℝ)
  | 5 => (-188481 / 62500000000 : ℝ)
  | 6 => (-777561 / 250000000000 : ℝ)
  | 7 => (-3205829 / 1000000000000 : ℝ)
  | 8 => (-1651227 / 500000000000 : ℝ)
  | 9 => (-850031 / 250000000000 : ℝ)
  | 10 => (-3498843 / 1000000000000 : ℝ)
  | 11 => (-3598613 / 1000000000000 : ℝ)
  | 12 => (-1849719 / 500000000000 : ℝ)
  | 13 => (-1900661 / 500000000000 : ℝ)
  | 14 => (-976067 / 250000000000 : ℝ)
  | 15 => (-4008279 / 1000000000000 : ℝ)
  | 16 => (-4113359 / 1000000000000 : ℝ)
  | 17 => (-4219511 / 1000000000000 : ℝ)
  | 18 => (-4326737 / 1000000000000 : ℝ)
  | 19 => (-2217521 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch034Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((680 : ℝ) + (j.val : ℝ)) / 1600)
      (((680 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch034Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch034Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((680 : ℝ) + (j.val : ℝ)) / 1600)
    (((680 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch034Neg45WeightLower j.val) (hpThetaShiftThreeBatch034Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch034Neg45WeightLower, hpThetaShiftThreeBatch034Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch034Neg45_integral_bounds :
    (-11501871 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-5506587 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (680 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch034Lower hpThetaJensenCellsBatch034Upper
    hpThetaShiftThreeBatch034Neg45WeightLower hpThetaShiftThreeBatch034Neg45WeightUpper hpThetaJensenCellsBatch034_bounds hpThetaShiftThreeBatch034Neg45_weight_bounds
  have hl : (-11501871 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch034Lower j * hpThetaShiftThreeBatch034Neg45WeightLower j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftThreeBatch034Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftThreeBatch034Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch034Lower j * hpThetaShiftThreeBatch034Neg45WeightUpper j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftThreeBatch034Neg45WeightUpper j) / 1600) ≤ (-5506587 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftThreeBatch034Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (680 : ℝ) / 1600 = 34 / 80 by norm_num,
    show ((680 : ℝ) + 20) / 1600 = (34 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch034Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2538943 / 200000000000 : ℝ)
  | 1 => (12729651 / 1000000000000 : ℝ)
  | 2 => (6382049 / 500000000000 : ℝ)
  | 3 => (6399023 / 500000000000 : ℝ)
  | 4 => (12831489 / 1000000000000 : ℝ)
  | 5 => (12864417 / 1000000000000 : ℝ)
  | 6 => (6448411 / 500000000000 : ℝ)
  | 7 => (1616087 / 125000000000 : ℝ)
  | 8 => (1296003 / 100000000000 : ℝ)
  | 9 => (405963 / 31250000000 : ℝ)
  | 10 => (3255261 / 250000000000 : ℝ)
  | 11 => (13050707 / 1000000000000 : ℝ)
  | 12 => (2615959 / 200000000000 : ℝ)
  | 13 => (131083 / 10000000000 : ℝ)
  | 14 => (13136213 / 1000000000000 : ℝ)
  | 15 => (526541 / 40000000000 : ℝ)
  | 16 => (13190227 / 1000000000000 : ℝ)
  | 17 => (1321631 / 100000000000 : ℝ)
  | 18 => (3310441 / 250000000000 : ℝ)
  | 19 => (6633291 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch034Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3182413 / 250000000000 : ℝ)
  | 1 => (12764099 / 1000000000000 : ℝ)
  | 2 => (12798047 / 1000000000000 : ℝ)
  | 3 => (1283149 / 100000000000 : ℝ)
  | 4 => (6432209 / 500000000000 : ℝ)
  | 5 => (12896823 / 1000000000000 : ℝ)
  | 6 => (12928697 / 1000000000000 : ℝ)
  | 7 => (12960031 / 1000000000000 : ℝ)
  | 8 => (12990817 / 1000000000000 : ℝ)
  | 9 => (2604209 / 200000000000 : ℝ)
  | 10 => (3262677 / 250000000000 : ℝ)
  | 11 => (3269949 / 250000000000 : ℝ)
  | 12 => (13108301 / 1000000000000 : ℝ)
  | 13 => (6568107 / 500000000000 : ℝ)
  | 14 => (6581763 / 500000000000 : ℝ)
  | 15 => (3297557 / 250000000000 : ℝ)
  | 16 => (13216311 / 1000000000000 : ℝ)
  | 17 => (2648353 / 200000000000 : ℝ)
  | 18 => (13266583 / 1000000000000 : ℝ)
  | 19 => (6645377 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch034Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((680 : ℝ) + (j.val : ℝ)) / 1600)
      (((680 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch034Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch034Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((680 : ℝ) + (j.val : ℝ)) / 1600)
    (((680 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch034Neg25WeightLower j.val) (hpThetaShiftThreeBatch034Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch034Neg25WeightLower, hpThetaShiftThreeBatch034Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch034Neg25_integral_bounds :
    (41510349 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (42237423 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (680 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch034Lower hpThetaJensenCellsBatch034Upper
    hpThetaShiftThreeBatch034Neg25WeightLower hpThetaShiftThreeBatch034Neg25WeightUpper hpThetaJensenCellsBatch034_bounds hpThetaShiftThreeBatch034Neg25_weight_bounds
  have hl : (41510349 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch034Lower j * hpThetaShiftThreeBatch034Neg25WeightLower j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftThreeBatch034Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftThreeBatch034Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch034Lower j * hpThetaShiftThreeBatch034Neg25WeightUpper j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftThreeBatch034Neg25WeightUpper j) / 1600) ≤ (42237423 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftThreeBatch034Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (680 : ℝ) / 1600 = 34 / 80 by norm_num,
    show ((680 : ℝ) + 20) / 1600 = (34 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch034Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch034Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch034Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch034Neg25_integral_bounds
end HodgeProofHP
