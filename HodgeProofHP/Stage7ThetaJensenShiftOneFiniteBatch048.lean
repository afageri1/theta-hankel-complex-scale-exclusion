/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch048

/-! Exact signed weight and batch integral certificates, batch 48 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch048Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-88586797533 / 62500000000 : ℝ)
  | 1 => (-720667578087 / 500000000000 : ℝ)
  | 2 => (-732777898931 / 500000000000 : ℝ)
  | 3 => (-372513256467 / 250000000000 : ℝ)
  | 4 => (-378707298903 / 250000000000 : ℝ)
  | 5 => (-1539886677723 / 1000000000000 : ℝ)
  | 6 => (-39130696453 / 25000000000 : ℝ)
  | 7 => (-795427569041 / 500000000000 : ℝ)
  | 8 => (-1616770934319 / 1000000000000 : ℝ)
  | 9 => (-410744419763 / 250000000000 : ℝ)
  | 10 => (-1669477820083 / 1000000000000 : ℝ)
  | 11 => (-169627382087 / 100000000000 : ℝ)
  | 12 => (-1723368160603 / 1000000000000 : ℝ)
  | 13 => (-1750763334279 / 1000000000000 : ℝ)
  | 14 => (-1778461852773 / 1000000000000 : ℝ)
  | 15 => (-903233121461 / 500000000000 : ℝ)
  | 16 => (-229347380949 / 125000000000 : ℝ)
  | 17 => (-931701412879 / 500000000000 : ℝ)
  | 18 => (-1892340152581 / 1000000000000 : ℝ)
  | 19 => (-480398404871 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch048Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-696857142857 / 500000000000 : ℝ)
  | 1 => (-1417388760527 / 1000000000000 : ℝ)
  | 2 => (-1441335156173 / 1000000000000 : ℝ)
  | 3 => (-1465555797861 / 1000000000000 : ℝ)
  | 4 => (-1490053025867 / 1000000000000 : ℝ)
  | 5 => (-1514829195611 / 1000000000000 : ℝ)
  | 6 => (-769943338861 / 500000000000 : ℝ)
  | 7 => (-1565227858119 / 1000000000000 : ℝ)
  | 8 => (-1590855138081 / 1000000000000 : ℝ)
  | 9 => (-808385467159 / 500000000000 : ℝ)
  | 10 => (-1642977679051 / 1000000000000 : ℝ)
  | 11 => (-834738910041 / 500000000000 : ℝ)
  | 12 => (-1696273820869 / 1000000000000 : ℝ)
  | 13 => (-861684080301 / 500000000000 : ℝ)
  | 14 => (-875381667139 / 500000000000 : ℝ)
  | 15 => (-444615463193 / 250000000000 : ℝ)
  | 16 => (-1806466242921 / 1000000000000 : ℝ)
  | 17 => (-1834779047591 / 1000000000000 : ℝ)
  | 18 => (-1863402825757 / 1000000000000 : ℝ)
  | 19 => (-94617007629 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch048Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((960 : ℝ) + (j.val : ℝ)) / 1600)
      (((960 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch048Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch048Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((960 : ℝ) + (j.val : ℝ)) / 1600)
    (((960 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch048Neg100WeightLower j.val) (hpThetaShiftOneBatch048Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch048Neg100WeightLower, hpThetaShiftOneBatch048Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch048Neg100_integral_bounds :
    (-112223009013 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-21674734957 / 40000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (960 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch048Lower hpThetaJensenCellsBatch048Upper
    hpThetaShiftOneBatch048Neg100WeightLower hpThetaShiftOneBatch048Neg100WeightUpper hpThetaJensenCellsBatch048_bounds hpThetaShiftOneBatch048Neg100_weight_bounds
  have hl : (-112223009013 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch048Lower j * hpThetaShiftOneBatch048Neg100WeightLower j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftOneBatch048Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftOneBatch048Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch048Lower j * hpThetaShiftOneBatch048Neg100WeightUpper j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftOneBatch048Neg100WeightUpper j) / 1600) ≤ (-21674734957 / 40000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftOneBatch048Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (960 : ℝ) / 1600 = 48 / 80 by norm_num,
    show ((960 : ℝ) + 20) / 1600 = (48 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch048Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (127960491269 / 500000000000 : ℝ)
  | 1 => (255390369397 / 1000000000000 : ℝ)
  | 2 => (254825438297 / 1000000000000 : ℝ)
  | 3 => (254225749239 / 1000000000000 : ℝ)
  | 4 => (63397714691 / 250000000000 : ℝ)
  | 5 => (12646015997 / 50000000000 : ℝ)
  | 6 => (12610684117 / 50000000000 : ℝ)
  | 7 => (10058819681 / 40000000000 : ℝ)
  | 8 => (10027611661 / 40000000000 : ℝ)
  | 9 => (249872619819 / 1000000000000 : ℝ)
  | 10 => (1556356327 / 6250000000 : ℝ)
  | 11 => (4962460017 / 20000000000 : ℝ)
  | 12 => (123595056813 / 500000000000 : ℝ)
  | 13 => (6155446881 / 25000000000 : ℝ)
  | 14 => (122602903319 / 500000000000 : ℝ)
  | 15 => (122076712551 / 500000000000 : ℝ)
  | 16 => (243060244231 / 1000000000000 : ℝ)
  | 17 => (120962886961 / 500000000000 : ℝ)
  | 18 => (240749520349 / 1000000000000 : ℝ)
  | 19 => (119765492973 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch048Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (128208857143 / 500000000000 : ℝ)
  | 1 => (255920982539 / 1000000000000 : ℝ)
  | 2 => (127695184699 / 500000000000 : ℝ)
  | 3 => (127412719149 / 500000000000 : ℝ)
  | 4 => (6355643731 / 25000000000 : ℝ)
  | 5 => (50718171753 / 200000000000 : ℝ)
  | 6 => (252920319941 / 1000000000000 : ℝ)
  | 7 => (252213682341 / 1000000000000 : ℝ)
  | 8 => (125735246013 / 500000000000 : ℝ)
  | 9 => (125345145763 / 500000000000 : ℝ)
  | 10 => (12493630991 / 50000000000 : ℝ)
  | 11 => (249017012321 / 1000000000000 : ℝ)
  | 12 => (248123000851 / 1000000000000 : ℝ)
  | 13 => (247190113627 / 1000000000000 : ℝ)
  | 14 => (246217875241 / 1000000000000 : ℝ)
  | 15 => (245205806639 / 1000000000000 : ℝ)
  | 16 => (244153425103 / 1000000000000 : ℝ)
  | 17 => (30382530529 / 125000000000 : ℝ)
  | 18 => (241925773923 / 1000000000000 : ℝ)
  | 19 => (4814990407 / 20000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch048Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((960 : ℝ) + (j.val : ℝ)) / 1600)
      (((960 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch048Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch048Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((960 : ℝ) + (j.val : ℝ)) / 1600)
    (((960 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch048Neg65WeightLower j.val) (hpThetaShiftOneBatch048Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch048Neg65WeightLower, hpThetaShiftOneBatch048Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch048Neg65_integral_bounds :
    (8302401169 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (42443074343 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (960 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch048Lower hpThetaJensenCellsBatch048Upper
    hpThetaShiftOneBatch048Neg65WeightLower hpThetaShiftOneBatch048Neg65WeightUpper hpThetaJensenCellsBatch048_bounds hpThetaShiftOneBatch048Neg65_weight_bounds
  have hl : (8302401169 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch048Lower j * hpThetaShiftOneBatch048Neg65WeightLower j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftOneBatch048Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftOneBatch048Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch048Lower j * hpThetaShiftOneBatch048Neg65WeightUpper j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftOneBatch048Neg65WeightUpper j) / 1600) ≤ (42443074343 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftOneBatch048Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (960 : ℝ) / 1600 = 48 / 80 by norm_num,
    show ((960 : ℝ) + 20) / 1600 = (48 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch048Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (55193142857 / 500000000000 : ℝ)
  | 1 => (111695860047 / 1000000000000 : ℝ)
  | 2 => (28252698669 / 250000000000 : ℝ)
  | 3 => (28582765949 / 250000000000 : ℝ)
  | 4 => (115656641087 / 1000000000000 : ℝ)
  | 5 => (23397499941 / 200000000000 : ℝ)
  | 6 => (59161806141 / 500000000000 : ℝ)
  | 7 => (119664950919 / 1000000000000 : ℝ)
  | 8 => (121011487183 / 1000000000000 : ℝ)
  | 9 => (24472638421 / 200000000000 : ℝ)
  | 10 => (123720036177 / 1000000000000 : ℝ)
  | 11 => (3908812167 / 31250000000 : ℝ)
  | 12 => (126449021003 / 1000000000000 : ℝ)
  | 13 => (1278211 / 10000000 : ℝ)
  | 14 => (1033585557 / 8000000000 : ℝ)
  | 15 => (4080633519 / 31250000000 : ℝ)
  | 16 => (131967301117 / 1000000000000 : ℝ)
  | 17 => (133359246749 / 1000000000000 : ℝ)
  | 18 => (67378037767 / 500000000000 : ℝ)
  | 19 => (5446310117 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch048Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (6980991253 / 62500000000 : ℝ)
  | 1 => (113010794677 / 1000000000000 : ℝ)
  | 2 => (114331063797 / 1000000000000 : ℝ)
  | 3 => (1807135017 / 15625000000 : ℝ)
  | 4 => (58493749853 / 500000000000 : ℝ)
  | 5 => (118323612283 / 1000000000000 : ℝ)
  | 6 => (2991623773 / 25000000000 : ℝ)
  | 7 => (7563217949 / 62500000000 : ℝ)
  | 8 => (61181596053 / 500000000000 : ℝ)
  | 9 => (61860018089 / 500000000000 : ℝ)
  | 10 => (25016397869 / 200000000000 : ℝ)
  | 11 => (31612255251 / 250000000000 : ℝ)
  | 12 => (127821100001 / 1000000000000 : ℝ)
  | 13 => (64599097313 / 500000000000 : ℝ)
  | 14 => (130580272609 / 1000000000000 : ℝ)
  | 15 => (65983650559 / 500000000000 : ℝ)
  | 16 => (533436987 / 4000000000 : ℝ)
  | 17 => (26951215107 / 200000000000 : ℝ)
  | 18 => (68078876463 / 500000000000 : ℝ)
  | 19 => (137564243797 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch048Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((960 : ℝ) + (j.val : ℝ)) / 1600)
      (((960 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch048Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch048Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((960 : ℝ) + (j.val : ℝ)) / 1600)
    (((960 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch048Neg40WeightLower j.val) (hpThetaShiftOneBatch048Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch048Neg40WeightLower, hpThetaShiftOneBatch048Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch048Neg40_integral_bounds :
    (40883542739 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (42122712143 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (960 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch048Lower hpThetaJensenCellsBatch048Upper
    hpThetaShiftOneBatch048Neg40WeightLower hpThetaShiftOneBatch048Neg40WeightUpper hpThetaJensenCellsBatch048_bounds hpThetaShiftOneBatch048Neg40_weight_bounds
  have hl : (40883542739 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch048Lower j * hpThetaShiftOneBatch048Neg40WeightLower j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftOneBatch048Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftOneBatch048Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch048Lower j * hpThetaShiftOneBatch048Neg40WeightUpper j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftOneBatch048Neg40WeightUpper j) / 1600) ≤ (42122712143 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftOneBatch048Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (960 : ℝ) / 1600 = 48 / 80 by norm_num,
    show ((960 : ℝ) + 20) / 1600 = (48 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch048Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-10187010713 / 125000000000 : ℝ)
  | 1 => (-20392040289 / 250000000000 : ℝ)
  | 2 => (-81637925283 / 1000000000000 : ℝ)
  | 3 => (-16341072541 / 200000000000 : ℝ)
  | 4 => (-4088522901 / 50000000000 : ℝ)
  | 5 => (-81833195807 / 1000000000000 : ℝ)
  | 6 => (-40946780313 / 500000000000 : ℝ)
  | 7 => (-16390307403 / 200000000000 : ℝ)
  | 8 => (-41003554747 / 500000000000 : ℝ)
  | 9 => (-20515065641 / 250000000000 : ℝ)
  | 10 => (-41055490353 / 500000000000 : ℝ)
  | 11 => (-82159248383 / 1000000000000 : ℝ)
  | 12 => (-82205050039 / 1000000000000 : ℝ)
  | 13 => (-822483701 / 10000000000 : ℝ)
  | 14 => (-5143074561 / 62500000000 : ℝ)
  | 15 => (-5145468941 / 62500000000 : ℝ)
  | 16 => (-41181642357 / 500000000000 : ℝ)
  | 17 => (-82396522307 / 1000000000000 : ℝ)
  | 18 => (-82427200173 / 1000000000000 : ℝ)
  | 19 => (-82455302637 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch048Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-16284342857 / 200000000000 : ℝ)
  | 1 => (-81496085703 / 1000000000000 : ℝ)
  | 2 => (-16313632231 / 200000000000 : ℝ)
  | 3 => (-40818962641 / 500000000000 : ℝ)
  | 4 => (-5106585169 / 62500000000 : ℝ)
  | 5 => (-81770458019 / 1000000000000 : ℝ)
  | 6 => (-40916597903 / 500000000000 : ℝ)
  | 7 => (-131029697 / 1600000000 : ℝ)
  | 8 => (-40975768507 / 500000000000 : ℝ)
  | 9 => (-82007109493 / 1000000000000 : ℝ)
  | 10 => (-82060262563 / 1000000000000 : ℝ)
  | 11 => (-16422196141 / 200000000000 : ℝ)
  | 12 => (-41079624191 / 500000000000 : ℝ)
  | 13 => (-41102525019 / 500000000000 : ℝ)
  | 14 => (-82248370099 / 1000000000000 : ℝ)
  | 15 => (-3291567719 / 40000000000 : ℝ)
  | 16 => (-16465500611 / 200000000000 : ℝ)
  | 17 => (-82363284713 / 1000000000000 : ℝ)
  | 18 => (-41198261153 / 500000000000 : ℝ)
  | 19 => (-20606800043 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch048Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((960 : ℝ) + (j.val : ℝ)) / 1600)
      (((960 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch048Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch048Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((960 : ℝ) + (j.val : ℝ)) / 1600)
    (((960 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch048Neg20WeightLower j.val) (hpThetaShiftOneBatch048Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch048Neg20WeightLower, hpThetaShiftOneBatch048Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch048Neg20_integral_bounds :
    (-2785932573 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-27321575053 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (960 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch048Lower hpThetaJensenCellsBatch048Upper
    hpThetaShiftOneBatch048Neg20WeightLower hpThetaShiftOneBatch048Neg20WeightUpper hpThetaJensenCellsBatch048_bounds hpThetaShiftOneBatch048Neg20_weight_bounds
  have hl : (-2785932573 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch048Lower j * hpThetaShiftOneBatch048Neg20WeightLower j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftOneBatch048Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftOneBatch048Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch048Lower j * hpThetaShiftOneBatch048Neg20WeightUpper j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftOneBatch048Neg20WeightUpper j) / 1600) ≤ (-27321575053 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftOneBatch048Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (960 : ℝ) / 1600 = 48 / 80 by norm_num,
    show ((960 : ℝ) + 20) / 1600 = (48 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch048Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch048Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch048Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch048Neg20_integral_bounds
end HodgeProofHP
