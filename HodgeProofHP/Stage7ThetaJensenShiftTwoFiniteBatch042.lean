/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch042

/-! Exact signed weight and batch integral certificates, batch 42 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch042Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4439299823 / 1000000000000 : ℝ)
  | 1 => (4450497023 / 1000000000000 : ℝ)
  | 2 => (4461029997 / 1000000000000 : ℝ)
  | 3 => (139715081 / 31250000000 : ℝ)
  | 4 => (560004803 / 125000000000 : ℝ)
  | 5 => (4488480881 / 1000000000000 : ℝ)
  | 6 => (2248096561 / 500000000000 : ℝ)
  | 7 => (450315807 / 100000000000 : ℝ)
  | 8 => (1127339603 / 250000000000 : ℝ)
  | 9 => (2257388299 / 500000000000 : ℝ)
  | 10 => (903878967 / 200000000000 : ℝ)
  | 11 => (452319509 / 100000000000 : ℝ)
  | 12 => (4526159081 / 1000000000000 : ℝ)
  | 13 => (2264134141 / 500000000000 : ℝ)
  | 14 => (566187989 / 125000000000 : ℝ)
  | 15 => (4529278081 / 1000000000000 : ℝ)
  | 16 => (4527777789 / 1000000000000 : ℝ)
  | 17 => (4525326259 / 1000000000000 : ℝ)
  | 18 => (70654741 / 15625000000 : ℝ)
  | 19 => (90349779 / 20000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch042Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (8692377 / 1953125000 : ℝ)
  | 1 => (2230514999 / 500000000000 : ℝ)
  | 2 => (4470882593 / 1000000000000 : ℝ)
  | 3 => (179201537 / 40000000000 : ℝ)
  | 4 => (2244240441 / 500000000000 : ℝ)
  | 5 => (4496193123 / 1000000000000 : ℝ)
  | 6 => (4503158071 / 1000000000000 : ℝ)
  | 7 => (4509358413 / 1000000000000 : ℝ)
  | 8 => (4514776599 / 1000000000000 : ℝ)
  | 9 => (1129848709 / 250000000000 : ℝ)
  | 10 => (4523195091 / 1000000000000 : ℝ)
  | 11 => (2263079541 / 500000000000 : ℝ)
  | 12 => (4528268283 / 1000000000000 : ℝ)
  | 13 => (4529503913 / 1000000000000 : ℝ)
  | 14 => (905971749 / 200000000000 : ℝ)
  | 15 => (4529846941 / 1000000000000 : ℝ)
  | 16 => (2264639041 / 500000000000 : ℝ)
  | 17 => (452777779 / 100000000000 : ℝ)
  | 18 => (226266313 / 50000000000 : ℝ)
  | 19 => (180876137 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch042Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((840 : ℝ) + (j.val : ℝ)) / 1600)
      (((840 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch042Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch042Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((840 : ℝ) + (j.val : ℝ)) / 1600)
    (((840 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch042Neg100WeightLower j.val) (hpThetaShiftTwoBatch042Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch042Neg100WeightLower, hpThetaShiftTwoBatch042Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch042Neg100_integral_bounds :
    (4538581447 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (2311032819 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (840 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch042Lower hpThetaJensenCellsBatch042Upper
    hpThetaShiftTwoBatch042Neg100WeightLower hpThetaShiftTwoBatch042Neg100WeightUpper hpThetaJensenCellsBatch042_bounds hpThetaShiftTwoBatch042Neg100_weight_bounds
  have hl : (4538581447 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch042Lower j * hpThetaShiftTwoBatch042Neg100WeightLower j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftTwoBatch042Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftTwoBatch042Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch042Lower j * hpThetaShiftTwoBatch042Neg100WeightUpper j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftTwoBatch042Neg100WeightUpper j) / 1600) ≤ (2311032819 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftTwoBatch042Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (840 : ℝ) / 1600 = 42 / 80 by norm_num,
    show ((840 : ℝ) + 20) / 1600 = (42 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch042Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (280249557 / 200000000000 : ℝ)
  | 1 => (1431202097 / 1000000000000 : ℝ)
  | 2 => (1461431019 / 1000000000000 : ℝ)
  | 3 => (1491935019 / 1000000000000 : ℝ)
  | 4 => (1522714539 / 1000000000000 : ℝ)
  | 5 => (388442499 / 250000000000 : ℝ)
  | 6 => (1585101783 / 1000000000000 : ℝ)
  | 7 => (808355133 / 500000000000 : ℝ)
  | 8 => (329719157 / 200000000000 : ℝ)
  | 9 => (336151731 / 200000000000 : ℝ)
  | 10 => (856599581 / 500000000000 : ℝ)
  | 11 => (872958783 / 500000000000 : ℝ)
  | 12 => (1778914097 / 1000000000000 : ℝ)
  | 13 => (1812188961 / 1000000000000 : ℝ)
  | 14 => (1845742331 / 1000000000000 : ℝ)
  | 15 => (1879574353 / 1000000000000 : ℝ)
  | 16 => (1913685143 / 1000000000000 : ℝ)
  | 17 => (974037393 / 500000000000 : ℝ)
  | 18 => (991371669 / 500000000000 : ℝ)
  | 19 => (2017690823 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch042Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (715601049 / 500000000000 : ℝ)
  | 1 => (73071551 / 50000000000 : ℝ)
  | 2 => (74596751 / 50000000000 : ℝ)
  | 3 => (76135727 / 50000000000 : ℝ)
  | 4 => (1553769997 / 1000000000000 : ℝ)
  | 5 => (198137723 / 125000000000 : ℝ)
  | 6 => (1616710267 / 1000000000000 : ℝ)
  | 7 => (824297893 / 500000000000 : ℝ)
  | 8 => (13130927 / 7812500000 : ℝ)
  | 9 => (1713199163 / 1000000000000 : ℝ)
  | 10 => (1745917567 / 1000000000000 : ℝ)
  | 11 => (889457049 / 500000000000 : ℝ)
  | 12 => (906094481 / 500000000000 : ℝ)
  | 13 => (461435583 / 250000000000 : ℝ)
  | 14 => (939787177 / 500000000000 : ℝ)
  | 15 => (239210643 / 125000000000 : ℝ)
  | 16 => (1948074787 / 1000000000000 : ℝ)
  | 17 => (1982743339 / 1000000000000 : ℝ)
  | 18 => (252211353 / 125000000000 : ℝ)
  | 19 => (2052917233 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch042Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((840 : ℝ) + (j.val : ℝ)) / 1600)
      (((840 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch042Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch042Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((840 : ℝ) + (j.val : ℝ)) / 1600)
    (((840 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch042Neg65WeightLower j.val) (hpThetaShiftTwoBatch042Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch042Neg65WeightLower, hpThetaShiftTwoBatch042Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch042Neg65_integral_bounds :
    (106649551 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (442272943 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (840 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch042Lower hpThetaJensenCellsBatch042Upper
    hpThetaShiftTwoBatch042Neg65WeightLower hpThetaShiftTwoBatch042Neg65WeightUpper hpThetaJensenCellsBatch042_bounds hpThetaShiftTwoBatch042Neg65_weight_bounds
  have hl : (106649551 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch042Lower j * hpThetaShiftTwoBatch042Neg65WeightLower j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftTwoBatch042Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftTwoBatch042Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch042Lower j * hpThetaShiftTwoBatch042Neg65WeightUpper j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftTwoBatch042Neg65WeightUpper j) / 1600) ≤ (442272943 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftTwoBatch042Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (840 : ℝ) / 1600 = 42 / 80 by norm_num,
    show ((840 : ℝ) + 20) / 1600 = (42 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch042Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1149593063 / 1000000000000 : ℝ)
  | 1 => (-572969347 / 500000000000 : ℝ)
  | 2 => (-1142131811 / 1000000000000 : ℝ)
  | 3 => (-1138170911 / 1000000000000 : ℝ)
  | 4 => (-567027243 / 500000000000 : ℝ)
  | 5 => (-35305657 / 31250000000 : ℝ)
  | 6 => (-1125349007 / 1000000000000 : ℝ)
  | 7 => (-70047307 / 62500000000 : ℝ)
  | 8 => (-1116003213 / 1000000000000 : ℝ)
  | 9 => (-138885797 / 125000000000 : ℝ)
  | 10 => (-553002433 / 500000000000 : ℝ)
  | 11 => (-55037857 / 50000000000 : ℝ)
  | 12 => (-1095341653 / 1000000000000 : ℝ)
  | 13 => (-544878427 / 500000000000 : ℝ)
  | 14 => (-1084001187 / 1000000000000 : ℝ)
  | 15 => (-539036547 / 500000000000 : ℝ)
  | 16 => (-107197101 / 100000000000 : ℝ)
  | 17 => (-1065693367 / 1000000000000 : ℝ)
  | 18 => (-1059238593 / 1000000000000 : ℝ)
  | 19 => (-1052605111 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch042Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1145938693 / 1000000000000 : ℝ)
  | 1 => (-114213181 / 100000000000 : ℝ)
  | 2 => (-113817091 / 100000000000 : ℝ)
  | 3 => (-226810897 / 200000000000 : ℝ)
  | 4 => (-1129781023 / 1000000000000 : ℝ)
  | 5 => (-562674503 / 500000000000 : ℝ)
  | 6 => (-1120756911 / 1000000000000 : ℝ)
  | 7 => (-279000803 / 250000000000 : ℝ)
  | 8 => (-8888691 / 8000000000 : ℝ)
  | 9 => (-221200973 / 200000000000 : ℝ)
  | 10 => (-1100757139 / 1000000000000 : ℝ)
  | 11 => (-273835413 / 250000000000 : ℝ)
  | 12 => (-1089756853 / 1000000000000 : ℝ)
  | 13 => (-542000593 / 500000000000 : ℝ)
  | 14 => (-1078073093 / 1000000000000 : ℝ)
  | 15 => (-1071971009 / 1000000000000 : ℝ)
  | 16 => (-532846683 / 500000000000 : ℝ)
  | 17 => (-16550603 / 15625000000 : ℝ)
  | 18 => (-105260511 / 100000000000 : ℝ)
  | 19 => (-1045791339 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch042Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((840 : ℝ) + (j.val : ℝ)) / 1600)
      (((840 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch042Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch042Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((840 : ℝ) + (j.val : ℝ)) / 1600)
    (((840 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch042Neg45WeightLower j.val) (hpThetaShiftTwoBatch042Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch042Neg45WeightLower, hpThetaShiftTwoBatch042Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch042Neg45_integral_bounds :
    (-1135436737 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-1111054777 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (840 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch042Lower hpThetaJensenCellsBatch042Upper
    hpThetaShiftTwoBatch042Neg45WeightLower hpThetaShiftTwoBatch042Neg45WeightUpper hpThetaJensenCellsBatch042_bounds hpThetaShiftTwoBatch042Neg45_weight_bounds
  have hl : (-1135436737 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch042Lower j * hpThetaShiftTwoBatch042Neg45WeightLower j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftTwoBatch042Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftTwoBatch042Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch042Lower j * hpThetaShiftTwoBatch042Neg45WeightUpper j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftTwoBatch042Neg45WeightUpper j) / 1600) ≤ (-1111054777 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftTwoBatch042Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (840 : ℝ) / 1600 = 42 / 80 by norm_num,
    show ((840 : ℝ) + 20) / 1600 = (42 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch042Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1148630881 / 1000000000000 : ℝ)
  | 1 => (-232093081 / 200000000000 : ℝ)
  | 2 => (-58617089 / 50000000000 : ℝ)
  | 3 => (-148032467 / 125000000000 : ℝ)
  | 4 => (-598109499 / 500000000000 : ℝ)
  | 5 => (-1208219287 / 1000000000000 : ℝ)
  | 6 => (-7626627 / 6250000000 : ℝ)
  | 7 => (-77021363 / 62500000000 : ℝ)
  | 8 => (-1244463459 / 1000000000000 : ℝ)
  | 9 => (-78539061 / 62500000000 : ℝ)
  | 10 => (-1268826059 / 1000000000000 : ℝ)
  | 11 => (-1281066401 / 1000000000000 : ℝ)
  | 12 => (-1293345693 / 1000000000000 : ℝ)
  | 13 => (-65283181 / 50000000000 : ℝ)
  | 14 => (-659009931 / 500000000000 : ℝ)
  | 15 => (-83150881 / 62500000000 : ℝ)
  | 16 => (-671422997 / 500000000000 : ℝ)
  | 17 => (-677657611 / 500000000000 : ℝ)
  | 18 => (-1367821443 / 1000000000000 : ℝ)
  | 19 => (-276072863 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch042Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-568419237 / 500000000000 : ℝ)
  | 1 => (-7178943 / 6250000000 : ℝ)
  | 2 => (-290116351 / 250000000000 : ℝ)
  | 3 => (-1172341779 / 1000000000000 : ℝ)
  | 4 => (-236851947 / 200000000000 : ℝ)
  | 5 => (-1196218997 / 1000000000000 : ℝ)
  | 6 => (-604109643 / 500000000000 : ℝ)
  | 7 => (-1220260319 / 1000000000000 : ℝ)
  | 8 => (-1232341807 / 1000000000000 : ℝ)
  | 9 => (-622231729 / 500000000000 : ℝ)
  | 10 => (-50264999 / 40000000000 : ℝ)
  | 11 => (-634413029 / 500000000000 : ℝ)
  | 12 => (-1601333 / 1250000000 : ℝ)
  | 13 => (-323336423 / 250000000000 : ℝ)
  | 14 => (-1305663619 / 1000000000000 : ℝ)
  | 15 => (-1318019861 / 1000000000000 : ℝ)
  | 16 => (-266082819 / 200000000000 : ℝ)
  | 17 => (-1342845993 / 1000000000000 : ℝ)
  | 18 => (-1355315221 / 1000000000000 : ℝ)
  | 19 => (-683910721 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch042Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((840 : ℝ) + (j.val : ℝ)) / 1600)
      (((840 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch042Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch042Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((840 : ℝ) + (j.val : ℝ)) / 1600)
    (((840 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch042Neg25WeightLower j.val) (hpThetaShiftTwoBatch042Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch042Neg25WeightLower, hpThetaShiftTwoBatch042Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch042Neg25_integral_bounds :
    (-646062631 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-1258007599 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (840 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch042Lower hpThetaJensenCellsBatch042Upper
    hpThetaShiftTwoBatch042Neg25WeightLower hpThetaShiftTwoBatch042Neg25WeightUpper hpThetaJensenCellsBatch042_bounds hpThetaShiftTwoBatch042Neg25_weight_bounds
  have hl : (-646062631 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch042Lower j * hpThetaShiftTwoBatch042Neg25WeightLower j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftTwoBatch042Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftTwoBatch042Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch042Lower j * hpThetaShiftTwoBatch042Neg25WeightUpper j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftTwoBatch042Neg25WeightUpper j) / 1600) ≤ (-1258007599 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftTwoBatch042Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (840 : ℝ) / 1600 = 42 / 80 by norm_num,
    show ((840 : ℝ) + 20) / 1600 = (42 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch042Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch042Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch042Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch042Neg25_integral_bounds
end HodgeProofHP
