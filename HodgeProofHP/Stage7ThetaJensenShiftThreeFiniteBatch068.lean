/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch068

/-! Exact signed weight and batch integral certificates, batch 68 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch068Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-32368968499 / 500000000000 : ℝ)
  | 1 => (-2618862343 / 40000000000 : ℝ)
  | 2 => (-4138280233 / 62500000000 : ℝ)
  | 3 => (-33480388153 / 500000000000 : ℝ)
  | 4 => (-16929125161 / 250000000000 : ℝ)
  | 5 => (-6847972157 / 100000000000 : ℝ)
  | 6 => (-13850100881 / 200000000000 : ℝ)
  | 7 => (-8753614371 / 125000000000 : ℝ)
  | 8 => (-70815019579 / 1000000000000 : ℝ)
  | 9 => (-8951110633 / 125000000000 : ℝ)
  | 10 => (-72410578753 / 1000000000000 : ℝ)
  | 11 => (-73220168489 / 1000000000000 : ℝ)
  | 12 => (-74037722631 / 1000000000000 : ℝ)
  | 13 => (-74863310051 / 1000000000000 : ℝ)
  | 14 => (-75697000147 / 1000000000000 : ℝ)
  | 15 => (-76538862837 / 1000000000000 : ℝ)
  | 16 => (-77388968571 / 1000000000000 : ℝ)
  | 17 => (-9780923541 / 125000000000 : ℝ)
  | 18 => (-39557096811 / 500000000000 : ℝ)
  | 19 => (-15997891301 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch068Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4000722227 / 62500000000 : ℝ)
  | 1 => (-64737936997 / 1000000000000 : ℝ)
  | 2 => (-32735779287 / 500000000000 : ℝ)
  | 3 => (-66212483727 / 1000000000000 : ℝ)
  | 4 => (-13392155261 / 200000000000 : ℝ)
  | 5 => (-67716500643 / 1000000000000 : ℝ)
  | 6 => (-68479721569 / 1000000000000 : ℝ)
  | 7 => (-17312626101 / 250000000000 : ℝ)
  | 8 => (-70028914967 / 1000000000000 : ℝ)
  | 9 => (-35407509789 / 500000000000 : ℝ)
  | 10 => (-71608885063 / 1000000000000 : ℝ)
  | 11 => (-1131415293 / 15625000000 : ℝ)
  | 12 => (-9152521061 / 125000000000 : ℝ)
  | 13 => (-7403772263 / 100000000000 : ℝ)
  | 14 => (-1497266201 / 20000000000 : ℝ)
  | 15 => (-37848500073 / 500000000000 : ℝ)
  | 16 => (-19134715709 / 250000000000 : ℝ)
  | 17 => (-7738896857 / 100000000000 : ℝ)
  | 18 => (-78247388327 / 1000000000000 : ℝ)
  | 19 => (-79114193621 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch068Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1360 : ℝ) + (j.val : ℝ)) / 1600)
      (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch068Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch068Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1360 : ℝ) + (j.val : ℝ)) / 1600)
    (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch068Neg100WeightLower j.val) (hpThetaShiftThreeBatch068Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch068Neg100WeightLower, hpThetaShiftThreeBatch068Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch068Neg100_integral_bounds :
    (-42568277 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-81923299 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch068Lower hpThetaJensenCellsBatch068Upper
    hpThetaShiftThreeBatch068Neg100WeightLower hpThetaShiftThreeBatch068Neg100WeightUpper hpThetaJensenCellsBatch068_bounds hpThetaShiftThreeBatch068Neg100_weight_bounds
  have hl : (-42568277 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch068Lower j * hpThetaShiftThreeBatch068Neg100WeightLower j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftThreeBatch068Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftThreeBatch068Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch068Lower j * hpThetaShiftThreeBatch068Neg100WeightUpper j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftThreeBatch068Neg100WeightUpper j) / 1600) ≤ (-81923299 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftThreeBatch068Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1360 : ℝ) / 1600 = 68 / 80 by norm_num,
    show ((1360 : ℝ) + 20) / 1600 = (68 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch068Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8682150761 / 1000000000000 : ℝ)
  | 1 => (-550898999 / 62500000000 : ℝ)
  | 2 => (-111852571 / 12500000000 : ℝ)
  | 3 => (-4541815833 / 500000000000 : ℝ)
  | 4 => (-4610338947 / 500000000000 : ℝ)
  | 5 => (-146240007 / 15625000000 : ℝ)
  | 6 => (-9499695549 / 1000000000000 : ℝ)
  | 7 => (-301303111 / 31250000000 : ℝ)
  | 8 => (-195707779 / 20000000000 : ℝ)
  | 9 => (-9930780371 / 1000000000000 : ℝ)
  | 10 => (-5038945293 / 500000000000 : ℝ)
  | 11 => (-10226736501 / 1000000000000 : ℝ)
  | 12 => (-5188667583 / 500000000000 : ℝ)
  | 13 => (-1052970377 / 100000000000 : ℝ)
  | 14 => (-10683859647 / 1000000000000 : ℝ)
  | 15 => (-10839820273 / 1000000000000 : ℝ)
  | 16 => (-10997603269 / 1000000000000 : ℝ)
  | 17 => (-5578613201 / 500000000000 : ℝ)
  | 18 => (-88427403 / 7812500000 : ℝ)
  | 19 => (-11482064877 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch068Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4275745161 / 500000000000 : ℝ)
  | 1 => (-217053769 / 25000000000 : ℝ)
  | 2 => (-8814383983 / 1000000000000 : ℝ)
  | 3 => (-8948205679 / 1000000000000 : ℝ)
  | 4 => (-1816726333 / 200000000000 : ℝ)
  | 5 => (-9220677893 / 1000000000000 : ℝ)
  | 6 => (-9359360447 / 1000000000000 : ℝ)
  | 7 => (-2374923887 / 250000000000 : ℝ)
  | 8 => (-9641699551 / 1000000000000 : ℝ)
  | 9 => (-9785388949 / 1000000000000 : ℝ)
  | 10 => (-993078037 / 100000000000 : ℝ)
  | 11 => (-2015578117 / 200000000000 : ℝ)
  | 12 => (-20453473 / 2000000000 : ℝ)
  | 13 => (-2075467033 / 200000000000 : ℝ)
  | 14 => (-10529703769 / 1000000000000 : ℝ)
  | 15 => (-5341929823 / 500000000000 : ℝ)
  | 16 => (-677488767 / 62500000000 : ℝ)
  | 17 => (-2749400817 / 250000000000 : ℝ)
  | 18 => (-11157226401 / 1000000000000 : ℝ)
  | 19 => (-11318707583 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch068Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1360 : ℝ) + (j.val : ℝ)) / 1600)
      (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch068Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch068Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1360 : ℝ) + (j.val : ℝ)) / 1600)
    (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch068Neg70WeightLower j.val) (hpThetaShiftThreeBatch068Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch068Neg70WeightLower, hpThetaShiftThreeBatch068Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch068Neg70_integral_bounds :
    (-5907001 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-2265457 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch068Lower hpThetaJensenCellsBatch068Upper
    hpThetaShiftThreeBatch068Neg70WeightLower hpThetaShiftThreeBatch068Neg70WeightUpper hpThetaJensenCellsBatch068_bounds hpThetaShiftThreeBatch068Neg70_weight_bounds
  have hl : (-5907001 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch068Lower j * hpThetaShiftThreeBatch068Neg70WeightLower j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftThreeBatch068Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftThreeBatch068Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch068Lower j * hpThetaShiftThreeBatch068Neg70WeightUpper j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftThreeBatch068Neg70WeightUpper j) / 1600) ≤ (-2265457 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftThreeBatch068Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1360 : ℝ) / 1600 = 68 / 80 by norm_num,
    show ((1360 : ℝ) + 20) / 1600 = (68 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch068Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (20528421 / 15625000000 : ℝ)
  | 1 => (164718167 / 125000000000 : ℝ)
  | 2 => (1321592107 / 1000000000000 : ℝ)
  | 3 => (331339387 / 250000000000 : ℝ)
  | 4 => (332259983 / 250000000000 : ℝ)
  | 5 => (1332637509 / 1000000000000 : ℝ)
  | 6 => (1336148511 / 1000000000000 : ℝ)
  | 7 => (334892787 / 250000000000 : ℝ)
  | 8 => (167862951 / 125000000000 : ℝ)
  | 9 => (67307203 / 50000000000 : ℝ)
  | 10 => (337322663 / 250000000000 : ℝ)
  | 11 => (1352341509 / 1000000000000 : ℝ)
  | 12 => (677647367 / 500000000000 : ℝ)
  | 13 => (135814841 / 100000000000 : ℝ)
  | 14 => (680450299 / 500000000000 : ℝ)
  | 15 => (170443667 / 125000000000 : ℝ)
  | 16 => (1366092639 / 1000000000000 : ℝ)
  | 17 => (2737057 / 2000000000 : ℝ)
  | 18 => (1370854891 / 1000000000000 : ℝ)
  | 19 => (686534879 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch068Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1317745337 / 1000000000000 : ℝ)
  | 1 => (330398027 / 250000000000 : ℝ)
  | 2 => (1325357549 / 1000000000000 : ℝ)
  | 3 => (1329039933 / 1000000000000 : ℝ)
  | 4 => (133263751 / 100000000000 : ℝ)
  | 5 => (41754641 / 31250000000 : ℝ)
  | 6 => (1339571149 / 1000000000000 : ℝ)
  | 7 => (1342903609 / 1000000000000 : ℝ)
  | 8 => (1346144061 / 1000000000000 : ℝ)
  | 9 => (1349290653 / 1000000000000 : ℝ)
  | 10 => (135234151 / 100000000000 : ℝ)
  | 11 => (271058947 / 200000000000 : ℝ)
  | 12 => (1358148411 / 1000000000000 : ℝ)
  | 13 => (1360900599 / 1000000000000 : ℝ)
  | 14 => (1363549337 / 1000000000000 : ℝ)
  | 15 => (8538079 / 6250000000 : ℝ)
  | 16 => (1368528501 / 1000000000000 : ℝ)
  | 17 => (342713723 / 250000000000 : ℝ)
  | 18 => (1373069759 / 1000000000000 : ℝ)
  | 19 => (343792757 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch068Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1360 : ℝ) + (j.val : ℝ)) / 1600)
      (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch068Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch068Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1360 : ℝ) + (j.val : ℝ)) / 1600)
    (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch068Neg45WeightLower j.val) (hpThetaShiftThreeBatch068Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch068Neg45WeightLower, hpThetaShiftThreeBatch068Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch068Neg45_integral_bounds :
    (310879 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (400291 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch068Lower hpThetaJensenCellsBatch068Upper
    hpThetaShiftThreeBatch068Neg45WeightLower hpThetaShiftThreeBatch068Neg45WeightUpper hpThetaJensenCellsBatch068_bounds hpThetaShiftThreeBatch068Neg45_weight_bounds
  have hl : (310879 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch068Lower j * hpThetaShiftThreeBatch068Neg45WeightLower j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftThreeBatch068Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftThreeBatch068Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch068Lower j * hpThetaShiftThreeBatch068Neg45WeightUpper j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftThreeBatch068Neg45WeightUpper j) / 1600) ≤ (400291 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftThreeBatch068Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1360 : ℝ) / 1600 = 68 / 80 by norm_num,
    show ((1360 : ℝ) + 20) / 1600 = (68 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch068Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-77794279 / 500000000000 : ℝ)
  | 1 => (-76490399 / 500000000000 : ℝ)
  | 2 => (-150334541 / 1000000000000 : ℝ)
  | 3 => (-73824759 / 500000000000 : ℝ)
  | 4 => (-144925463 / 1000000000000 : ℝ)
  | 5 => (-142162107 / 1000000000000 : ℝ)
  | 6 => (-6967959 / 50000000000 : ℝ)
  | 7 => (-136516413 / 1000000000000 : ℝ)
  | 8 => (-26726707 / 200000000000 : ℝ)
  | 9 => (-65355137 / 500000000000 : ℝ)
  | 10 => (-127746359 / 1000000000000 : ℝ)
  | 11 => (-31185379 / 250000000000 : ℝ)
  | 12 => (-121695473 / 1000000000000 : ℝ)
  | 13 => (-23721591 / 200000000000 : ℝ)
  | 14 => (-3608709 / 31250000000 : ℝ)
  | 15 => (-28076849 / 250000000000 : ℝ)
  | 16 => (-27273451 / 250000000000 : ℝ)
  | 17 => (-52918817 / 500000000000 : ℝ)
  | 18 => (-102538609 / 1000000000000 : ℝ)
  | 19 => (-24799113 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch068Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-152980797 / 1000000000000 : ℝ)
  | 1 => (-7516727 / 50000000000 : ℝ)
  | 2 => (-147649517 / 1000000000000 : ℝ)
  | 3 => (-72462731 / 500000000000 : ℝ)
  | 4 => (-71081053 / 500000000000 : ℝ)
  | 5 => (-139359179 / 1000000000000 : ℝ)
  | 6 => (-34129103 / 250000000000 : ℝ)
  | 7 => (-66816767 / 500000000000 : ℝ)
  | 8 => (-130710273 / 1000000000000 : ℝ)
  | 9 => (-63873179 / 500000000000 : ℝ)
  | 10 => (-24948303 / 200000000000 : ℝ)
  | 11 => (-7605967 / 62500000000 : ℝ)
  | 12 => (-59303977 / 500000000000 : ℝ)
  | 13 => (-115478687 / 1000000000000 : ℝ)
  | 14 => (-22461479 / 200000000000 : ℝ)
  | 15 => (-109093803 / 1000000000000 : ℝ)
  | 16 => (-105837633 / 1000000000000 : ℝ)
  | 17 => (-6408663 / 62500000000 : ℝ)
  | 18 => (-99196451 / 1000000000000 : ℝ)
  | 19 => (-47905441 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch068Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1360 : ℝ) + (j.val : ℝ)) / 1600)
      (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch068Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch068Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1360 : ℝ) + (j.val : ℝ)) / 1600)
    (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch068Neg25WeightLower j.val) (hpThetaShiftThreeBatch068Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch068Neg25WeightLower, hpThetaShiftThreeBatch068Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch068Neg25_integral_bounds :
    (-154973 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-147373 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch068Lower hpThetaJensenCellsBatch068Upper
    hpThetaShiftThreeBatch068Neg25WeightLower hpThetaShiftThreeBatch068Neg25WeightUpper hpThetaJensenCellsBatch068_bounds hpThetaShiftThreeBatch068Neg25_weight_bounds
  have hl : (-154973 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch068Lower j * hpThetaShiftThreeBatch068Neg25WeightLower j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftThreeBatch068Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftThreeBatch068Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch068Lower j * hpThetaShiftThreeBatch068Neg25WeightUpper j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftThreeBatch068Neg25WeightUpper j) / 1600) ≤ (-147373 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftThreeBatch068Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1360 : ℝ) / 1600 = 68 / 80 by norm_num,
    show ((1360 : ℝ) + 20) / 1600 = (68 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch068Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch068Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch068Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch068Neg25_integral_bounds
end HodgeProofHP
