/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch025

/-! Exact signed weight and batch integral certificates, batch 25 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch025Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-198863 / 200000000000 : ℝ)
  | 1 => (-254109 / 250000000000 : ℝ)
  | 2 => (-1038779 / 1000000000000 : ℝ)
  | 3 => (-530671 / 500000000000 : ℝ)
  | 4 => (-1084123 / 1000000000000 : ℝ)
  | 5 => (-276781 / 250000000000 : ℝ)
  | 6 => (-1130341 / 1000000000000 : ℝ)
  | 7 => (-1153773 / 1000000000000 : ℝ)
  | 8 => (-58871 / 50000000000 : ℝ)
  | 9 => (-1877 / 1562500000 : ℝ)
  | 10 => (-153169 / 125000000000 : ℝ)
  | 11 => (-1249633 / 1000000000000 : ℝ)
  | 12 => (-637061 / 500000000000 : ℝ)
  | 13 => (-649409 / 500000000000 : ℝ)
  | 14 => (-661859 / 500000000000 : ℝ)
  | 15 => (-1348821 / 1000000000000 : ℝ)
  | 16 => (-10993 / 8000000000 : ℝ)
  | 17 => (-699813 / 500000000000 : ℝ)
  | 18 => (-356331 / 250000000000 : ℝ)
  | 19 => (-90701 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch025Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-194483 / 200000000000 : ℝ)
  | 1 => (-497157 / 500000000000 : ℝ)
  | 2 => (-203287 / 200000000000 : ℝ)
  | 3 => (-519389 / 500000000000 : ℝ)
  | 4 => (-1061341 / 1000000000000 : ℝ)
  | 5 => (-542061 / 500000000000 : ℝ)
  | 6 => (-1107123 / 1000000000000 : ℝ)
  | 7 => (-56517 / 50000000000 : ℝ)
  | 8 => (-288443 / 250000000000 : ℝ)
  | 9 => (-1177419 / 1000000000000 : ℝ)
  | 10 => (-1201279 / 1000000000000 : ℝ)
  | 11 => (-1225351 / 1000000000000 : ℝ)
  | 12 => (-39051 / 31250000000 : ℝ)
  | 13 => (-1274121 / 1000000000000 : ℝ)
  | 14 => (-1298817 / 1000000000000 : ℝ)
  | 15 => (-1323717 / 1000000000000 : ℝ)
  | 16 => (-67441 / 50000000000 : ℝ)
  | 17 => (-343531 / 250000000000 : ℝ)
  | 18 => (-11197 / 8000000000 : ℝ)
  | 19 => (-1425323 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch025Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((500 : ℝ) + (j.val : ℝ)) / 1600)
      (((500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch025Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch025Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((500 : ℝ) + (j.val : ℝ)) / 1600)
    (((500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch025Neg100WeightLower j.val) (hpThetaShiftThreeBatch025Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch025Neg100WeightLower, hpThetaShiftThreeBatch025Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch025Neg100_integral_bounds :
    (-1242509 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-9615447 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch025Lower hpThetaJensenCellsBatch025Upper
    hpThetaShiftThreeBatch025Neg100WeightLower hpThetaShiftThreeBatch025Neg100WeightUpper hpThetaJensenCellsBatch025_bounds hpThetaShiftThreeBatch025Neg100_weight_bounds
  have hl : (-1242509 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch025Lower j * hpThetaShiftThreeBatch025Neg100WeightLower j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftThreeBatch025Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftThreeBatch025Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch025Lower j * hpThetaShiftThreeBatch025Neg100WeightUpper j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftThreeBatch025Neg100WeightUpper j) / 1600) ≤ (-9615447 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftThreeBatch025Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (500 : ℝ) / 1600 = 25 / 80 by norm_num,
    show ((500 : ℝ) + 20) / 1600 = (25 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch025Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (124693 / 500000000000 : ℝ)
  | 1 => (58947 / 250000000000 : ℝ)
  | 2 => (3467 / 15625000000 : ℝ)
  | 3 => (207681 / 1000000000000 : ℝ)
  | 4 => (96583 / 500000000000 : ℝ)
  | 5 => (178339 / 1000000000000 : ℝ)
  | 6 => (163197 / 1000000000000 : ℝ)
  | 7 => (147737 / 1000000000000 : ℝ)
  | 8 => (131957 / 1000000000000 : ℝ)
  | 9 => (115853 / 1000000000000 : ℝ)
  | 10 => (49711 / 500000000000 : ℝ)
  | 11 => (82663 / 1000000000000 : ℝ)
  | 12 => (65571 / 1000000000000 : ℝ)
  | 13 => (3009 / 62500000000 : ℝ)
  | 14 => (15189 / 500000000000 : ℝ)
  | 15 => (767 / 62500000000 : ℝ)
  | 16 => (-3089 / 500000000000 : ℝ)
  | 17 => (-12487 / 500000000000 : ℝ)
  | 18 => (-1103 / 25000000000 : ℝ)
  | 19 => (-31809 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch025Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (65671 / 250000000000 : ℝ)
  | 1 => (249387 / 1000000000000 : ℝ)
  | 2 => (235789 / 1000000000000 : ℝ)
  | 3 => (221889 / 1000000000000 : ℝ)
  | 4 => (103841 / 500000000000 : ℝ)
  | 5 => (193167 / 1000000000000 : ℝ)
  | 6 => (8917 / 50000000000 : ℝ)
  | 7 => (81599 / 500000000000 : ℝ)
  | 8 => (73869 / 500000000000 : ℝ)
  | 9 => (65979 / 500000000000 : ℝ)
  | 10 => (57927 / 500000000000 : ℝ)
  | 11 => (99423 / 1000000000000 : ℝ)
  | 12 => (10333 / 125000000000 : ℝ)
  | 13 => (16393 / 250000000000 : ℝ)
  | 14 => (9629 / 200000000000 : ℝ)
  | 15 => (30379 / 1000000000000 : ℝ)
  | 16 => (12273 / 1000000000000 : ℝ)
  | 17 => (-6177 / 1000000000000 : ℝ)
  | 18 => (-24973 / 1000000000000 : ℝ)
  | 19 => (-44119 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch025Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((500 : ℝ) + (j.val : ℝ)) / 1600)
      (((500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch025Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch025Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((500 : ℝ) + (j.val : ℝ)) / 1600)
    (((500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch025Neg70WeightLower j.val) (hpThetaShiftThreeBatch025Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch025Neg70WeightLower, hpThetaShiftThreeBatch025Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch025Neg70_integral_bounds :
    (844193 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (98987 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch025Lower hpThetaJensenCellsBatch025Upper
    hpThetaShiftThreeBatch025Neg70WeightLower hpThetaShiftThreeBatch025Neg70WeightUpper hpThetaJensenCellsBatch025_bounds hpThetaShiftThreeBatch025Neg70_weight_bounds
  have hl : (844193 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch025Lower j * hpThetaShiftThreeBatch025Neg70WeightLower j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftThreeBatch025Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftThreeBatch025Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch025Lower j * hpThetaShiftThreeBatch025Neg70WeightUpper j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftThreeBatch025Neg70WeightUpper j) / 1600) ≤ (98987 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftThreeBatch025Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (500 : ℝ) / 1600 = 25 / 80 by norm_num,
    show ((500 : ℝ) + 20) / 1600 = (25 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch025Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (132379 / 62500000000 : ℝ)
  | 1 => (265879 / 125000000000 : ℝ)
  | 2 => (2135871 / 1000000000000 : ℝ)
  | 3 => (2144577 / 1000000000000 : ℝ)
  | 4 => (2153147 / 1000000000000 : ℝ)
  | 5 => (1080789 / 500000000000 : ℝ)
  | 6 => (2169867 / 1000000000000 : ℝ)
  | 7 => (217801 / 100000000000 : ℝ)
  | 8 => (546501 / 250000000000 : ℝ)
  | 9 => (1096923 / 500000000000 : ℝ)
  | 10 => (2201531 / 1000000000000 : ℝ)
  | 11 => (1104529 / 500000000000 : ℝ)
  | 12 => (2216421 / 1000000000000 : ℝ)
  | 13 => (1111809 / 500000000000 : ℝ)
  | 14 => (446129 / 200000000000 : ℝ)
  | 15 => (1118749 / 500000000000 : ℝ)
  | 16 => (1122087 / 500000000000 : ℝ)
  | 17 => (225067 / 100000000000 : ℝ)
  | 18 => (112849 / 50000000000 : ℝ)
  | 19 => (2263103 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch025Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2127033 / 1000000000000 : ℝ)
  | 1 => (33373 / 15625000000 : ℝ)
  | 2 => (1072289 / 500000000000 : ℝ)
  | 3 => (538287 / 250000000000 : ℝ)
  | 4 => (2161579 / 1000000000000 : ℝ)
  | 5 => (542467 / 250000000000 : ℝ)
  | 6 => (2178011 / 1000000000000 : ℝ)
  | 7 => (437201 / 200000000000 : ℝ)
  | 8 => (2193847 / 1000000000000 : ℝ)
  | 9 => (550383 / 250000000000 : ℝ)
  | 10 => (2209059 / 1000000000000 : ℝ)
  | 11 => (1108211 / 500000000000 : ℝ)
  | 12 => (2223619 / 1000000000000 : ℝ)
  | 13 => (1115323 / 500000000000 : ℝ)
  | 14 => (2237499 / 1000000000000 : ℝ)
  | 15 => (89767 / 40000000000 : ℝ)
  | 16 => (2250671 / 1000000000000 : ℝ)
  | 17 => (2256981 / 1000000000000 : ℝ)
  | 18 => (35361 / 15625000000 : ℝ)
  | 19 => (453807 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch025Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((500 : ℝ) + (j.val : ℝ)) / 1600)
      (((500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch025Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch025Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((500 : ℝ) + (j.val : ℝ)) / 1600)
    (((500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch025Neg45WeightLower j.val) (hpThetaShiftThreeBatch025Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch025Neg45WeightLower, hpThetaShiftThreeBatch025Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch025Neg45_integral_bounds :
    (554229 / 31250000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (901737 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch025Lower hpThetaJensenCellsBatch025Upper
    hpThetaShiftThreeBatch025Neg45WeightLower hpThetaShiftThreeBatch025Neg45WeightUpper hpThetaJensenCellsBatch025_bounds hpThetaShiftThreeBatch025Neg45_weight_bounds
  have hl : (554229 / 31250000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch025Lower j * hpThetaShiftThreeBatch025Neg45WeightLower j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftThreeBatch025Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftThreeBatch025Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch025Lower j * hpThetaShiftThreeBatch025Neg45WeightUpper j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftThreeBatch025Neg45WeightUpper j) / 1600) ≤ (901737 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftThreeBatch025Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (500 : ℝ) / 1600 = 25 / 80 by norm_num,
    show ((500 : ℝ) + 20) / 1600 = (25 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch025Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4231111 / 1000000000000 : ℝ)
  | 1 => (426991 / 100000000000 : ℝ)
  | 2 => (4308917 / 1000000000000 : ℝ)
  | 3 => (1087033 / 250000000000 : ℝ)
  | 4 => (877511 / 200000000000 : ℝ)
  | 5 => (885437 / 200000000000 : ℝ)
  | 6 => (4467021 / 1000000000000 : ℝ)
  | 7 => (4507063 / 1000000000000 : ℝ)
  | 8 => (4547311 / 1000000000000 : ℝ)
  | 9 => (4587763 / 1000000000000 : ℝ)
  | 10 => (4628419 / 1000000000000 : ℝ)
  | 11 => (2334639 / 500000000000 : ℝ)
  | 12 => (4710339 / 1000000000000 : ℝ)
  | 13 => (4751601 / 1000000000000 : ℝ)
  | 14 => (599133 / 125000000000 : ℝ)
  | 15 => (4834727 / 1000000000000 : ℝ)
  | 16 => (4876589 / 1000000000000 : ℝ)
  | 17 => (4918649 / 1000000000000 : ℝ)
  | 18 => (2480453 / 500000000000 : ℝ)
  | 19 => (5003359 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch025Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (4269911 / 1000000000000 : ℝ)
  | 1 => (2154459 / 500000000000 : ℝ)
  | 2 => (4348133 / 1000000000000 : ℝ)
  | 3 => (1096889 / 250000000000 : ℝ)
  | 4 => (2213593 / 500000000000 : ℝ)
  | 5 => (2233511 / 500000000000 : ℝ)
  | 6 => (563383 / 125000000000 : ℝ)
  | 7 => (284207 / 62500000000 : ℝ)
  | 8 => (1146941 / 250000000000 : ℝ)
  | 9 => (231421 / 50000000000 : ℝ)
  | 10 => (4669279 / 1000000000000 : ℝ)
  | 11 => (235517 / 50000000000 : ℝ)
  | 12 => (2375801 / 500000000000 : ℝ)
  | 13 => (958613 / 200000000000 : ℝ)
  | 14 => (604341 / 125000000000 : ℝ)
  | 15 => (487659 / 100000000000 : ℝ)
  | 16 => (98373 / 20000000000 : ℝ)
  | 17 => (4960907 / 1000000000000 : ℝ)
  | 18 => (31271 / 6250000000 : ℝ)
  | 19 => (630751 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch025Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((500 : ℝ) + (j.val : ℝ)) / 1600)
      (((500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch025Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch025Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((500 : ℝ) + (j.val : ℝ)) / 1600)
    (((500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch025Neg25WeightLower j.val) (hpThetaShiftThreeBatch025Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch025Neg25WeightLower, hpThetaShiftThreeBatch025Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch025Neg25_integral_bounds :
    (37230749 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (38062681 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch025Lower hpThetaJensenCellsBatch025Upper
    hpThetaShiftThreeBatch025Neg25WeightLower hpThetaShiftThreeBatch025Neg25WeightUpper hpThetaJensenCellsBatch025_bounds hpThetaShiftThreeBatch025Neg25_weight_bounds
  have hl : (37230749 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch025Lower j * hpThetaShiftThreeBatch025Neg25WeightLower j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftThreeBatch025Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftThreeBatch025Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch025Lower j * hpThetaShiftThreeBatch025Neg25WeightUpper j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftThreeBatch025Neg25WeightUpper j) / 1600) ≤ (38062681 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftThreeBatch025Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (500 : ℝ) / 1600 = 25 / 80 by norm_num,
    show ((500 : ℝ) + 20) / 1600 = (25 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch025Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch025Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch025Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch025Neg25_integral_bounds
end HodgeProofHP
