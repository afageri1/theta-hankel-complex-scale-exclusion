/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch054

/-! Exact signed weight and batch integral certificates, batch 54 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch054Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-25122610807 / 250000000000 : ℝ)
  | 1 => (-25520150741 / 250000000000 : ℝ)
  | 2 => (-20738040019 / 200000000000 : ℝ)
  | 3 => (-13164928313 / 125000000000 : ℝ)
  | 4 => (-53484237809 / 500000000000 : ℝ)
  | 5 => (-4345501697 / 40000000000 : ℝ)
  | 6 => (-2758170587 / 25000000000 : ℝ)
  | 7 => (-56018258457 / 500000000000 : ℝ)
  | 8 => (-113766822449 / 1000000000000 : ℝ)
  | 9 => (-23103588281 / 200000000000 : ℝ)
  | 10 => (-117290076711 / 1000000000000 : ℝ)
  | 11 => (-23816686583 / 200000000000 : ℝ)
  | 12 => (-120898216197 / 1000000000000 : ℝ)
  | 13 => (-39275083 / 320000000 : ℝ)
  | 14 => (-62296448461 / 500000000000 : ℝ)
  | 15 => (-126473214969 / 1000000000000 : ℝ)
  | 16 => (-64187900661 / 500000000000 : ℝ)
  | 17 => (-16287608809 / 125000000000 : ℝ)
  | 18 => (-132248638601 / 1000000000000 : ℝ)
  | 19 => (-134219323599 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch054Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-98919530543 / 1000000000000 : ℝ)
  | 1 => (-100490443227 / 1000000000000 : ℝ)
  | 2 => (-102080602963 / 1000000000000 : ℝ)
  | 3 => (-51845100047 / 500000000000 : ℝ)
  | 4 => (-105319426503 / 1000000000000 : ℝ)
  | 5 => (-106968475617 / 1000000000000 : ℝ)
  | 6 => (-13579692803 / 125000000000 : ℝ)
  | 7 => (-110326823479 / 1000000000000 : ℝ)
  | 8 => (-112036516913 / 1000000000000 : ℝ)
  | 9 => (-7110426403 / 62500000000 : ℝ)
  | 10 => (-28879485351 / 250000000000 : ℝ)
  | 11 => (-11729007671 / 100000000000 : ℝ)
  | 12 => (-59541716457 / 500000000000 : ℝ)
  | 13 => (-30224554049 / 250000000000 : ℝ)
  | 14 => (-61367317187 / 500000000000 : ℝ)
  | 15 => (-124592896921 / 1000000000000 : ℝ)
  | 16 => (-15809151871 / 125000000000 : ℝ)
  | 17 => (-128375801321 / 1000000000000 : ℝ)
  | 18 => (-130300870471 / 1000000000000 : ℝ)
  | 19 => (-661243193 / 5000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch054Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1080 : ℝ) + (j.val : ℝ)) / 1600)
      (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch054Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch054Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1080 : ℝ) + (j.val : ℝ)) / 1600)
    (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch054Neg100WeightLower j.val) (hpThetaShiftTwoBatch054Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch054Neg100WeightLower, hpThetaShiftTwoBatch054Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch054Neg100_integral_bounds :
    (-10245072311 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-1235084857 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1080 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch054Lower hpThetaJensenCellsBatch054Upper
    hpThetaShiftTwoBatch054Neg100WeightLower hpThetaShiftTwoBatch054Neg100WeightUpper hpThetaJensenCellsBatch054_bounds hpThetaShiftTwoBatch054Neg100_weight_bounds
  have hl : (-10245072311 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch054Lower j * hpThetaShiftTwoBatch054Neg100WeightLower j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftTwoBatch054Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftTwoBatch054Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch054Lower j * hpThetaShiftTwoBatch054Neg100WeightUpper j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftTwoBatch054Neg100WeightUpper j) / 1600) ≤ (-1235084857 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftTwoBatch054Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1080 : ℝ) / 1600 = 54 / 80 by norm_num,
    show ((1080 : ℝ) + 20) / 1600 = (54 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch054Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (10385821761 / 1000000000000 : ℝ)
  | 1 => (1293802543 / 125000000000 : ℝ)
  | 2 => (2062607031 / 200000000000 : ℝ)
  | 3 => (10273635931 / 1000000000000 : ℝ)
  | 4 => (5116096051 / 500000000000 : ℝ)
  | 5 => (2547168197 / 250000000000 : ℝ)
  | 6 => (25357617 / 2500000000 : ℝ)
  | 7 => (2019056527 / 200000000000 : ℝ)
  | 8 => (5022674237 / 500000000000 : ℝ)
  | 9 => (9993212181 / 1000000000000 : ℝ)
  | 10 => (99388413 / 10000000000 : ℝ)
  | 11 => (197644061 / 20000000000 : ℝ)
  | 12 => (9823264327 / 1000000000000 : ℝ)
  | 13 => (4880995849 / 500000000000 : ℝ)
  | 14 => (9698351403 / 1000000000000 : ℝ)
  | 15 => (4816154673 / 500000000000 : ℝ)
  | 16 => (4781915549 / 500000000000 : ℝ)
  | 17 => (9492881893 / 1000000000000 : ℝ)
  | 18 => (75355413 / 8000000000 : ℝ)
  | 19 => (2335857461 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch054Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1302408671 / 125000000000 : ℝ)
  | 1 => (5192910881 / 500000000000 : ℝ)
  | 2 => (2070084069 / 200000000000 : ℝ)
  | 3 => (2578258789 / 250000000000 : ℝ)
  | 4 => (2568408983 / 250000000000 : ℝ)
  | 5 => (10232192103 / 1000000000000 : ℝ)
  | 6 => (10188672789 / 1000000000000 : ℝ)
  | 7 => (10143046801 / 1000000000000 : ℝ)
  | 8 => (2523820659 / 250000000000 : ℝ)
  | 9 => (401813939 / 40000000000 : ℝ)
  | 10 => (4996606091 / 500000000000 : ℝ)
  | 11 => (9938841301 / 1000000000000 : ℝ)
  | 12 => (9882203051 / 1000000000000 : ℝ)
  | 13 => (1227908041 / 125000000000 : ℝ)
  | 14 => (9761991699 / 1000000000000 : ℝ)
  | 15 => (2424587851 / 250000000000 : ℝ)
  | 16 => (9632309347 / 1000000000000 : ℝ)
  | 17 => (9563831099 / 1000000000000 : ℝ)
  | 18 => (4746440947 / 500000000000 : ℝ)
  | 19 => (4709713313 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch054Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1080 : ℝ) + (j.val : ℝ)) / 1600)
      (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch054Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch054Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1080 : ℝ) + (j.val : ℝ)) / 1600)
    (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch054Neg65WeightLower j.val) (hpThetaShiftTwoBatch054Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch054Neg65WeightLower, hpThetaShiftTwoBatch054Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch054Neg65_integral_bounds :
    (430236809 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (441679401 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1080 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch054Lower hpThetaJensenCellsBatch054Upper
    hpThetaShiftTwoBatch054Neg65WeightLower hpThetaShiftTwoBatch054Neg65WeightUpper hpThetaJensenCellsBatch054_bounds hpThetaShiftTwoBatch054Neg65_weight_bounds
  have hl : (430236809 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch054Lower j * hpThetaShiftTwoBatch054Neg65WeightLower j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftTwoBatch054Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftTwoBatch054Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch054Lower j * hpThetaShiftTwoBatch054Neg65WeightUpper j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftTwoBatch054Neg65WeightUpper j) / 1600) ≤ (441679401 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftTwoBatch054Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1080 : ℝ) / 1600 = 54 / 80 by norm_num,
    show ((1080 : ℝ) + 20) / 1600 = (54 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch054Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (151163591 / 20000000000 : ℝ)
  | 1 => (1527550481 / 200000000000 : ℝ)
  | 2 => (1929420159 / 250000000000 : ℝ)
  | 3 => (7797962101 / 1000000000000 : ℝ)
  | 4 => (3939297301 / 500000000000 : ℝ)
  | 5 => (1591915177 / 200000000000 : ℝ)
  | 6 => (4020451819 / 500000000000 : ℝ)
  | 7 => (8122575493 / 1000000000000 : ℝ)
  | 8 => (8204589023 / 1000000000000 : ℝ)
  | 9 => (8286941743 / 1000000000000 : ℝ)
  | 10 => (8369631109 / 1000000000000 : ℝ)
  | 11 => (2113163629 / 250000000000 : ℝ)
  | 12 => (8536009299 / 1000000000000 : ℝ)
  | 13 => (4309846367 / 500000000000 : ℝ)
  | 14 => (8703702033 / 1000000000000 : ℝ)
  | 15 => (4394017173 / 500000000000 : ℝ)
  | 16 => (4436343381 / 500000000000 : ℝ)
  | 17 => (1791531261 / 200000000000 : ℝ)
  | 18 => (1808587987 / 200000000000 : ℝ)
  | 19 => (9128534549 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch054Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3818876203 / 500000000000 : ℝ)
  | 1 => (7717680637 / 1000000000000 : ℝ)
  | 2 => (3898981051 / 500000000000 : ℝ)
  | 3 => (7878594603 / 1000000000000 : ℝ)
  | 4 => (3979787943 / 500000000000 : ℝ)
  | 5 => (8040903639 / 1000000000000 : ℝ)
  | 6 => (4061287747 / 500000000000 : ℝ)
  | 7 => (256393407 / 31250000000 : ℝ)
  | 8 => (517933859 / 62500000000 : ℝ)
  | 9 => (836963111 / 100000000000 : ℝ)
  | 10 => (8452654517 / 1000000000000 : ℝ)
  | 11 => (85360093 / 10000000000 : ℝ)
  | 12 => (1723938547 / 200000000000 : ℝ)
  | 13 => (4351851017 / 500000000000 : ℝ)
  | 14 => (8788034347 / 1000000000000 : ℝ)
  | 15 => (8872686763 / 1000000000000 : ℝ)
  | 16 => (4478828153 / 500000000000 : ℝ)
  | 17 => (282591873 / 31250000000 : ℝ)
  | 18 => (182570691 / 20000000000 : ℝ)
  | 19 => (9214436977 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch054Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1080 : ℝ) + (j.val : ℝ)) / 1600)
      (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch054Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch054Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1080 : ℝ) + (j.val : ℝ)) / 1600)
    (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch054Neg45WeightLower j.val) (hpThetaShiftTwoBatch054Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch054Neg45WeightLower, hpThetaShiftTwoBatch054Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch054Neg45_integral_bounds :
    (717682651 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (370091699 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1080 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch054Lower hpThetaJensenCellsBatch054Upper
    hpThetaShiftTwoBatch054Neg45WeightLower hpThetaShiftTwoBatch054Neg45WeightUpper hpThetaJensenCellsBatch054_bounds hpThetaShiftTwoBatch054Neg45_weight_bounds
  have hl : (717682651 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch054Lower j * hpThetaShiftTwoBatch054Neg45WeightLower j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftTwoBatch054Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftTwoBatch054Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch054Lower j * hpThetaShiftTwoBatch054Neg45WeightUpper j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftTwoBatch054Neg45WeightUpper j) / 1600) ≤ (370091699 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftTwoBatch054Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1080 : ℝ) / 1600 = 54 / 80 by norm_num,
    show ((1080 : ℝ) + 20) / 1600 = (54 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch054Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3866177529 / 1000000000000 : ℝ)
  | 1 => (-3867910687 / 1000000000000 : ℝ)
  | 2 => (-967364123 / 250000000000 : ℝ)
  | 3 => (-1935406599 / 500000000000 : ℝ)
  | 4 => (-241998691 / 62500000000 : ℝ)
  | 5 => (-3872952307 / 1000000000000 : ℝ)
  | 6 => (-968432797 / 250000000000 : ℝ)
  | 7 => (-387431393 / 100000000000 : ℝ)
  | 8 => (-1937349377 / 500000000000 : ℝ)
  | 9 => (-96872097 / 25000000000 : ℝ)
  | 10 => (-387490431 / 100000000000 : ℝ)
  | 11 => (-1937433759 / 500000000000 : ℝ)
  | 12 => (-3874647873 / 1000000000000 : ℝ)
  | 13 => (-1937111571 / 500000000000 : ℝ)
  | 14 => (-24209947 / 6250000000 : ℝ)
  | 15 => (-387275119 / 100000000000 : ℝ)
  | 16 => (-1935850167 / 500000000000 : ℝ)
  | 17 => (-1935218563 / 500000000000 : ℝ)
  | 18 => (-3868959731 / 1000000000000 : ℝ)
  | 19 => (-3867266313 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch054Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-772851751 / 200000000000 : ℝ)
  | 1 => (-483272191 / 125000000000 : ℝ)
  | 2 => (-1933955343 / 500000000000 : ℝ)
  | 3 => (-3869456491 / 1000000000000 : ℝ)
  | 4 => (-3870813197 / 1000000000000 : ℝ)
  | 5 => (-774395811 / 200000000000 : ℝ)
  | 6 => (-1936476153 / 500000000000 : ℝ)
  | 7 => (-3873731187 / 1000000000000 : ℝ)
  | 8 => (-3874313929 / 1000000000000 : ℝ)
  | 9 => (-3874698753 / 1000000000000 : ℝ)
  | 10 => (-3874867517 / 1000000000000 : ℝ)
  | 11 => (-60541373 / 15625000000 : ℝ)
  | 12 => (-3874223141 / 1000000000000 : ℝ)
  | 13 => (-3873591519 / 1000000000000 : ℝ)
  | 14 => (-3872751189 / 1000000000000 : ℝ)
  | 15 => (-3871700333 / 1000000000000 : ℝ)
  | 16 => (-30963497 / 8000000000 : ℝ)
  | 17 => (-386895973 / 100000000000 : ℝ)
  | 18 => (-483408289 / 125000000000 : ℝ)
  | 19 => (-1932677513 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch054Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1080 : ℝ) + (j.val : ℝ)) / 1600)
      (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch054Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch054Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1080 : ℝ) + (j.val : ℝ)) / 1600)
    (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch054Neg25WeightLower j.val) (hpThetaShiftTwoBatch054Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch054Neg25WeightLower, hpThetaShiftTwoBatch054Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch054Neg25_integral_bounds :
    (-85473787 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-334718577 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1080 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch054Lower hpThetaJensenCellsBatch054Upper
    hpThetaShiftTwoBatch054Neg25WeightLower hpThetaShiftTwoBatch054Neg25WeightUpper hpThetaJensenCellsBatch054_bounds hpThetaShiftTwoBatch054Neg25_weight_bounds
  have hl : (-85473787 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch054Lower j * hpThetaShiftTwoBatch054Neg25WeightLower j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftTwoBatch054Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftTwoBatch054Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch054Lower j * hpThetaShiftTwoBatch054Neg25WeightUpper j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftTwoBatch054Neg25WeightUpper j) / 1600) ≤ (-334718577 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftTwoBatch054Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1080 : ℝ) / 1600 = 54 / 80 by norm_num,
    show ((1080 : ℝ) + 20) / 1600 = (54 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch054Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch054Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch054Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch054Neg25_integral_bounds
end HodgeProofHP
