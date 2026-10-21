/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch040

/-! Exact signed weight and batch integral certificates, batch 40 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch040Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (142121837539 / 1000000000000 : ℝ)
  | 1 => (70296273041 / 500000000000 : ℝ)
  | 2 => (139012623171 / 1000000000000 : ℝ)
  | 3 => (34345342399 / 250000000000 : ℝ)
  | 4 => (27139615967 / 200000000000 : ℝ)
  | 5 => (133962042013 / 1000000000000 : ℝ)
  | 6 => (132172537863 / 1000000000000 : ℝ)
  | 7 => (32582210671 / 250000000000 : ℝ)
  | 8 => (64215112651 / 500000000000 : ℝ)
  | 9 => (126475948031 / 1000000000000 : ℝ)
  | 10 => (12446526663 / 100000000000 : ℝ)
  | 11 => (15299678783 / 125000000000 : ℝ)
  | 12 => (120271681463 / 1000000000000 : ℝ)
  | 13 => (118087256079 / 1000000000000 : ℝ)
  | 14 => (7240211453 / 62500000000 : ℝ)
  | 15 => (22707857069 / 200000000000 : ℝ)
  | 16 => (22234835589 / 200000000000 : ℝ)
  | 17 => (108747269781 / 1000000000000 : ℝ)
  | 18 => (106257762701 / 1000000000000 : ℝ)
  | 19 => (51852425813 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch040Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (143601190477 / 1000000000000 : ℝ)
  | 1 => (7106091877 / 50000000000 : ℝ)
  | 2 => (140592546083 / 1000000000000 : ℝ)
  | 3 => (34753155793 / 250000000000 : ℝ)
  | 4 => (137381369597 / 1000000000000 : ℝ)
  | 5 => (33924519959 / 250000000000 : ℝ)
  | 6 => (66981021007 / 500000000000 : ℝ)
  | 7 => (16521567233 / 125000000000 : ℝ)
  | 8 => (26065768537 / 200000000000 : ℝ)
  | 9 => (128430225303 / 1000000000000 : ℝ)
  | 10 => (30877917 / 244140625 : ℝ)
  | 11 => (124465266631 / 1000000000000 : ℝ)
  | 12 => (24479486053 / 200000000000 : ℝ)
  | 13 => (15033960183 / 125000000000 : ℝ)
  | 14 => (1476090701 / 12500000000 : ℝ)
  | 15 => (115843383249 / 1000000000000 : ℝ)
  | 16 => (56769642673 / 500000000000 : ℝ)
  | 17 => (55587088973 / 500000000000 : ℝ)
  | 18 => (54373634891 / 500000000000 : ℝ)
  | 19 => (53128881351 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch040Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((800 : ℝ) + (j.val : ℝ)) / 1600)
      (((800 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch040Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch040Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((800 : ℝ) + (j.val : ℝ)) / 1600)
    (((800 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch040Neg100WeightLower j.val) (hpThetaShiftOneBatch040Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch040Neg100WeightLower, hpThetaShiftOneBatch040Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch040Neg100_integral_bounds :
    (173753084787 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (89721221999 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (800 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch040Lower hpThetaJensenCellsBatch040Upper
    hpThetaShiftOneBatch040Neg100WeightLower hpThetaShiftOneBatch040Neg100WeightUpper hpThetaJensenCellsBatch040_bounds hpThetaShiftOneBatch040Neg100_weight_bounds
  have hl : (173753084787 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch040Lower j * hpThetaShiftOneBatch040Neg100WeightLower j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftOneBatch040Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftOneBatch040Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch040Lower j * hpThetaShiftOneBatch040Neg100WeightUpper j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftOneBatch040Neg100WeightUpper j) / 1600) ≤ (89721221999 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftOneBatch040Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (800 : ℝ) / 1600 = 40 / 80 by norm_num,
    show ((800 : ℝ) + 20) / 1600 = (40 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch040Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3788176037 / 31250000000 : ℝ)
  | 1 => (61224951577 / 500000000000 : ℝ)
  | 2 => (123680929681 / 1000000000000 : ℝ)
  | 3 => (12491463107 / 100000000000 : ℝ)
  | 4 => (63075462189 / 500000000000 : ℝ)
  | 5 => (63694862703 / 500000000000 : ℝ)
  | 6 => (128630948689 / 1000000000000 : ℝ)
  | 7 => (25974901497 / 200000000000 : ℝ)
  | 8 => (16390039221 / 125000000000 : ℝ)
  | 9 => (26473655643 / 200000000000 : ℝ)
  | 10 => (133618310199 / 1000000000000 : ℝ)
  | 11 => (134870317777 / 1000000000000 : ℝ)
  | 12 => (136124207681 / 1000000000000 : ℝ)
  | 13 => (13737988531 / 100000000000 : ℝ)
  | 14 => (138637254717 / 1000000000000 : ℝ)
  | 15 => (69948109299 / 500000000000 : ℝ)
  | 16 => (141156678287 / 1000000000000 : ℝ)
  | 17 => (71209266871 / 500000000000 : ℝ)
  | 18 => (71840841767 / 500000000000 : ℝ)
  | 19 => (72473012421 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch040Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (24489980631 / 200000000000 : ℝ)
  | 1 => (61840464841 / 500000000000 : ℝ)
  | 2 => (124914631071 / 1000000000000 : ℝ)
  | 3 => (126150924379 / 1000000000000 : ℝ)
  | 4 => (127389725407 / 1000000000000 : ℝ)
  | 5 => (12863094869 / 100000000000 : ℝ)
  | 6 => (64937253743 / 500000000000 : ℝ)
  | 7 => (131120313769 / 1000000000000 : ℝ)
  | 8 => (16546034777 / 125000000000 : ℝ)
  | 9 => (668091551 / 5000000000 : ℝ)
  | 10 => (67435158889 / 500000000000 : ℝ)
  | 11 => (68062103841 / 500000000000 : ℝ)
  | 12 => (137379885311 / 1000000000000 : ℝ)
  | 13 => (69318627359 / 500000000000 : ℝ)
  | 14 => (139896218599 / 1000000000000 : ℝ)
  | 15 => (8822292393 / 62500000000 : ℝ)
  | 16 => (142418533743 / 1000000000000 : ℝ)
  | 17 => (28736336707 / 200000000000 : ℝ)
  | 18 => (144946024843 / 1000000000000 : ℝ)
  | 19 => (146211453437 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch040Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((800 : ℝ) + (j.val : ℝ)) / 1600)
      (((800 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch040Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch040Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((800 : ℝ) + (j.val : ℝ)) / 1600)
    (((800 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch040Neg65WeightLower j.val) (hpThetaShiftOneBatch040Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch040Neg65WeightLower, hpThetaShiftOneBatch040Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch040Neg65_integral_bounds :
    (36877441347 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (94611284357 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (800 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch040Lower hpThetaJensenCellsBatch040Upper
    hpThetaShiftOneBatch040Neg65WeightLower hpThetaShiftOneBatch040Neg65WeightUpper hpThetaJensenCellsBatch040_bounds hpThetaShiftOneBatch040Neg65_weight_bounds
  have hl : (36877441347 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch040Lower j * hpThetaShiftOneBatch040Neg65WeightLower j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftOneBatch040Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftOneBatch040Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch040Lower j * hpThetaShiftOneBatch040Neg65WeightUpper j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftOneBatch040Neg65WeightUpper j) / 1600) ≤ (94611284357 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftOneBatch040Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (800 : ℝ) / 1600 = 40 / 80 by norm_num,
    show ((800 : ℝ) + 20) / 1600 = (40 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch040Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2380952381 / 100000000000 : ℝ)
  | 1 => (-23420141839 / 1000000000000 : ℝ)
  | 2 => (-23025792477 / 1000000000000 : ℝ)
  | 3 => (-11313228171 / 500000000000 : ℝ)
  | 4 => (-2777764269 / 125000000000 : ℝ)
  | 5 => (-2726593341 / 125000000000 : ℝ)
  | 6 => (-5349583749 / 250000000000 : ℝ)
  | 7 => (-5244714997 / 250000000000 : ℝ)
  | 8 => (-20554302843 / 1000000000000 : ℝ)
  | 9 => (-20124644811 / 1000000000000 : ℝ)
  | 10 => (-4922466813 / 250000000000 : ℝ)
  | 11 => (-481248791 / 25000000000 : ℝ)
  | 12 => (-18804879563 / 1000000000000 : ℝ)
  | 13 => (-2294329091 / 125000000000 : ℝ)
  | 14 => (-8949596479 / 500000000000 : ℝ)
  | 15 => (-8719271099 / 500000000000 : ℝ)
  | 16 => (-8486331257 / 500000000000 : ℝ)
  | 17 => (-16501536097 / 1000000000000 : ℝ)
  | 18 => (-8012572631 / 500000000000 : ℝ)
  | 19 => (-15543472453 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch040Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-11710070919 / 500000000000 : ℝ)
  | 1 => (-5756448119 / 250000000000 : ℝ)
  | 2 => (-22626456341 / 1000000000000 : ℝ)
  | 3 => (-22222114151 / 1000000000000 : ℝ)
  | 4 => (-21812746727 / 1000000000000 : ℝ)
  | 5 => (-4279666999 / 200000000000 : ℝ)
  | 6 => (-20978859987 / 1000000000000 : ℝ)
  | 7 => (-10277151421 / 500000000000 : ℝ)
  | 8 => (-2012464481 / 100000000000 : ℝ)
  | 9 => (-19689867251 / 1000000000000 : ℝ)
  | 10 => (-19249951639 / 1000000000000 : ℝ)
  | 11 => (-9402439781 / 500000000000 : ℝ)
  | 12 => (-18354632727 / 1000000000000 : ℝ)
  | 13 => (-17899192957 / 1000000000000 : ℝ)
  | 14 => (-17438542197 / 1000000000000 : ℝ)
  | 15 => (-16972662513 / 1000000000000 : ℝ)
  | 16 => (-515673003 / 31250000000 : ℝ)
  | 17 => (-16025145261 / 1000000000000 : ℝ)
  | 18 => (-3885868113 / 250000000000 : ℝ)
  | 19 => (-3764125061 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch040Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((800 : ℝ) + (j.val : ℝ)) / 1600)
      (((800 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch040Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch040Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((800 : ℝ) + (j.val : ℝ)) / 1600)
    (((800 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch040Neg40WeightLower j.val) (hpThetaShiftOneBatch040Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch040Neg40WeightLower, hpThetaShiftOneBatch040Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch040Neg40_integral_bounds :
    (-28158879783 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-13545840457 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (800 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch040Lower hpThetaJensenCellsBatch040Upper
    hpThetaShiftOneBatch040Neg40WeightLower hpThetaShiftOneBatch040Neg40WeightUpper hpThetaJensenCellsBatch040_bounds hpThetaShiftOneBatch040Neg40_weight_bounds
  have hl : (-28158879783 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch040Lower j * hpThetaShiftOneBatch040Neg40WeightLower j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftOneBatch040Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftOneBatch040Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch040Lower j * hpThetaShiftOneBatch040Neg40WeightUpper j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftOneBatch040Neg40WeightUpper j) / 1600) ≤ (-13545840457 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftOneBatch040Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (800 : ℝ) / 1600 = 40 / 80 by norm_num,
    show ((800 : ℝ) + 20) / 1600 = (40 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch040Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2505760591 / 50000000000 : ℝ)
  | 1 => (-12594748877 / 250000000000 : ℝ)
  | 2 => (-50642531711 / 1000000000000 : ℝ)
  | 3 => (-50905810557 / 1000000000000 : ℝ)
  | 4 => (-51168822131 / 1000000000000 : ℝ)
  | 5 => (-12857889119 / 250000000000 : ℝ)
  | 6 => (-51694003591 / 1000000000000 : ℝ)
  | 7 => (-25978076717 / 500000000000 : ℝ)
  | 8 => (-652724949 / 12500000000 : ℝ)
  | 9 => (-26239760461 / 500000000000 : ℝ)
  | 10 => (-52740718271 / 1000000000000 : ℝ)
  | 11 => (-53001577753 / 1000000000000 : ℝ)
  | 12 => (-13315522279 / 250000000000 : ℝ)
  | 13 => (-26761121031 / 500000000000 : ℝ)
  | 14 => (-26891013127 / 500000000000 : ℝ)
  | 15 => (-5404143131 / 100000000000 : ℝ)
  | 16 => (-6787555851 / 125000000000 : ℝ)
  | 17 => (-54559062283 / 1000000000000 : ℝ)
  | 18 => (-5481726723 / 100000000000 : ℝ)
  | 19 => (-27537525549 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch040Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-12462797619 / 250000000000 : ℝ)
  | 1 => (-50115211819 / 1000000000000 : ℝ)
  | 2 => (-50378995507 / 1000000000000 : ℝ)
  | 3 => (-5064253171 / 100000000000 : ℝ)
  | 4 => (-12726452639 / 250000000000 : ℝ)
  | 5 => (-5116882213 / 100000000000 : ℝ)
  | 6 => (-2057262259 / 40000000000 : ℝ)
  | 7 => (-5169400359 / 100000000000 : ℝ)
  | 8 => (-51956153433 / 1000000000000 : ℝ)
  | 9 => (-52217995919 / 1000000000000 : ℝ)
  | 10 => (-52479520921 / 1000000000000 : ℝ)
  | 11 => (-5274071827 / 100000000000 : ℝ)
  | 12 => (-6625197219 / 125000000000 : ℝ)
  | 13 => (-10652417823 / 200000000000 : ℝ)
  | 14 => (-53522242061 / 1000000000000 : ℝ)
  | 15 => (-53782026253 / 1000000000000 : ℝ)
  | 16 => (-54041431309 / 1000000000000 : ℝ)
  | 17 => (-54300446807 / 1000000000000 : ℝ)
  | 18 => (-27279531141 / 500000000000 : ℝ)
  | 19 => (-54817267229 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch040Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((800 : ℝ) + (j.val : ℝ)) / 1600)
      (((800 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch040Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch040Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((800 : ℝ) + (j.val : ℝ)) / 1600)
    (((800 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch040Neg20WeightLower j.val) (hpThetaShiftOneBatch040Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch040Neg20WeightLower, hpThetaShiftOneBatch040Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch040Neg20_integral_bounds :
    (-7421380949 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (40 / 80 : ℝ) ((40 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-907938757 / 12500000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (800 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch040Lower hpThetaJensenCellsBatch040Upper
    hpThetaShiftOneBatch040Neg20WeightLower hpThetaShiftOneBatch040Neg20WeightUpper hpThetaJensenCellsBatch040_bounds hpThetaShiftOneBatch040Neg20_weight_bounds
  have hl : (-7421380949 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch040Lower j * hpThetaShiftOneBatch040Neg20WeightLower j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftOneBatch040Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftOneBatch040Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch040Lower j * hpThetaShiftOneBatch040Neg20WeightUpper j)
        (hpThetaJensenCellsBatch040Upper j * hpThetaShiftOneBatch040Neg20WeightUpper j) / 1600) ≤ (-907938757 / 12500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch040Lower, hpThetaJensenCellsBatch040Upper,
      hpThetaShiftOneBatch040Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (800 : ℝ) / 1600 = 40 / 80 by norm_num,
    show ((800 : ℝ) + 20) / 1600 = (40 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch040Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch040Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch040Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch040Neg20_integral_bounds
end HodgeProofHP
