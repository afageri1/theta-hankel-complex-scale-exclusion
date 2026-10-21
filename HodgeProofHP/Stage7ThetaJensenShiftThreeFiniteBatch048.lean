/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch048

/-! Exact signed weight and batch integral certificates, batch 48 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch048Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (23026071 / 200000000000 : ℝ)
  | 1 => (28518029 / 250000000000 : ℝ)
  | 2 => (56479619 / 500000000000 : ℝ)
  | 3 => (55895297 / 500000000000 : ℝ)
  | 4 => (110565041 / 1000000000000 : ℝ)
  | 5 => (109281419 / 1000000000000 : ℝ)
  | 6 => (107938551 / 1000000000000 : ℝ)
  | 7 => (106535243 / 1000000000000 : ℝ)
  | 8 => (26267571 / 250000000000 : ℝ)
  | 9 => (20708489 / 200000000000 : ℝ)
  | 10 => (1274381 / 12500000000 : ℝ)
  | 11 => (160469 / 1600000000 : ℝ)
  | 12 => (49284549 / 500000000000 : ℝ)
  | 13 => (48388549 / 500000000000 : ℝ)
  | 14 => (94915807 / 1000000000000 : ℝ)
  | 15 => (46491943 / 500000000000 : ℝ)
  | 16 => (90979979 / 1000000000000 : ℝ)
  | 17 => (8890271 / 100000000000 : ℝ)
  | 18 => (43375343 / 500000000000 : ℝ)
  | 19 => (84522491 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch048Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (23227013 / 200000000000 : ℝ)
  | 1 => (28782589 / 250000000000 : ℝ)
  | 2 => (114072117 / 1000000000000 : ℝ)
  | 3 => (112959239 / 1000000000000 : ℝ)
  | 4 => (22358119 / 200000000000 : ℝ)
  | 5 => (55282521 / 500000000000 : ℝ)
  | 6 => (5464071 / 50000000000 : ℝ)
  | 7 => (13492319 / 125000000000 : ℝ)
  | 8 => (26633811 / 250000000000 : ℝ)
  | 9 => (21014057 / 200000000000 : ℝ)
  | 10 => (51771223 / 500000000000 : ℝ)
  | 11 => (101950481 / 1000000000000 : ℝ)
  | 12 => (50146563 / 500000000000 : ℝ)
  | 13 => (98569099 / 1000000000000 : ℝ)
  | 14 => (96777099 / 1000000000000 : ℝ)
  | 15 => (2966119 / 31250000000 : ℝ)
  | 16 => (92983887 / 1000000000000 : ℝ)
  | 17 => (4548999 / 50000000000 : ℝ)
  | 18 => (88902711 / 1000000000000 : ℝ)
  | 19 => (86750687 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch048Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((960 : ℝ) + (j.val : ℝ)) / 1600)
      (((960 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch048Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch048Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((960 : ℝ) + (j.val : ℝ)) / 1600)
    (((960 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch048Neg100WeightLower j.val) (hpThetaShiftThreeBatch048Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch048Neg100WeightLower, hpThetaShiftThreeBatch048Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch048Neg100_integral_bounds :
    (6813657 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (35245747 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (960 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch048Lower hpThetaJensenCellsBatch048Upper
    hpThetaShiftThreeBatch048Neg100WeightLower hpThetaShiftThreeBatch048Neg100WeightUpper hpThetaJensenCellsBatch048_bounds hpThetaShiftThreeBatch048Neg100_weight_bounds
  have hl : (6813657 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch048Lower j * hpThetaShiftThreeBatch048Neg100WeightLower j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftThreeBatch048Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftThreeBatch048Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch048Lower j * hpThetaShiftThreeBatch048Neg100WeightUpper j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftThreeBatch048Neg100WeightUpper j) / 1600) ≤ (35245747 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftThreeBatch048Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (960 : ℝ) / 1600 = 48 / 80 by norm_num,
    show ((960 : ℝ) + 20) / 1600 = (48 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch048Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (106319127 / 1000000000000 : ℝ)
  | 1 => (53924101 / 500000000000 : ℝ)
  | 2 => (27347157 / 250000000000 : ℝ)
  | 3 => (110940377 / 1000000000000 : ℝ)
  | 4 => (22500683 / 200000000000 : ℝ)
  | 5 => (114077707 / 1000000000000 : ℝ)
  | 6 => (23132643 / 200000000000 : ℝ)
  | 7 => (117259899 / 1000000000000 : ℝ)
  | 8 => (59433859 / 500000000000 : ℝ)
  | 9 => (60243313 / 500000000000 : ℝ)
  | 10 => (4884663 / 40000000000 : ℝ)
  | 11 => (30939379 / 250000000000 : ℝ)
  | 12 => (25081879 / 200000000000 : ℝ)
  | 13 => (63536079 / 500000000000 : ℝ)
  | 14 => (25749149 / 200000000000 : ℝ)
  | 15 => (8151881 / 62500000000 : ℝ)
  | 16 => (33031287 / 250000000000 : ℝ)
  | 17 => (133830833 / 1000000000000 : ℝ)
  | 18 => (135547081 / 1000000000000 : ℝ)
  | 19 => (137273821 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch048Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (107848203 / 1000000000000 : ℝ)
  | 1 => (109388629 / 1000000000000 : ℝ)
  | 2 => (55470189 / 500000000000 : ℝ)
  | 3 => (14062927 / 125000000000 : ℝ)
  | 4 => (28519427 / 250000000000 : ℝ)
  | 5 => (7228951 / 62500000000 : ℝ)
  | 6 => (1172599 / 10000000000 : ℝ)
  | 7 => (118867719 / 1000000000000 : ℝ)
  | 8 => (120486627 / 1000000000000 : ℝ)
  | 9 => (3816143 / 31250000000 : ℝ)
  | 10 => (123757517 / 1000000000000 : ℝ)
  | 11 => (31352349 / 250000000000 : ℝ)
  | 12 => (127072159 / 1000000000000 : ℝ)
  | 13 => (64372873 / 500000000000 : ℝ)
  | 14 => (130430097 / 1000000000000 : ℝ)
  | 15 => (132125149 / 1000000000000 : ℝ)
  | 16 => (66915417 / 500000000000 : ℝ)
  | 17 => (67773541 / 500000000000 : ℝ)
  | 18 => (68636911 / 500000000000 : ℝ)
  | 19 => (139010977 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch048Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((960 : ℝ) + (j.val : ℝ)) / 1600)
      (((960 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch048Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch048Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((960 : ℝ) + (j.val : ℝ)) / 1600)
    (((960 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch048Neg70WeightLower j.val) (hpThetaShiftThreeBatch048Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch048Neg70WeightLower, hpThetaShiftThreeBatch048Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch048Neg70_integral_bounds :
    (40305209 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (8325277 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (960 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch048Lower hpThetaJensenCellsBatch048Upper
    hpThetaShiftThreeBatch048Neg70WeightLower hpThetaShiftThreeBatch048Neg70WeightUpper hpThetaJensenCellsBatch048_bounds hpThetaShiftThreeBatch048Neg70_weight_bounds
  have hl : (40305209 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch048Lower j * hpThetaShiftThreeBatch048Neg70WeightLower j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftThreeBatch048Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftThreeBatch048Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch048Lower j * hpThetaShiftThreeBatch048Neg70WeightUpper j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftThreeBatch048Neg70WeightUpper j) / 1600) ≤ (8325277 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftThreeBatch048Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (960 : ℝ) / 1600 = 48 / 80 by norm_num,
    show ((960 : ℝ) + 20) / 1600 = (48 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch048Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-177313 / 4000000000 : ℝ)
  | 1 => (-22108007 / 500000000000 : ℝ)
  | 2 => (-4409713 / 100000000000 : ℝ)
  | 3 => (-21985757 / 500000000000 : ℝ)
  | 4 => (-1095977 / 25000000000 : ℝ)
  | 5 => (-21849871 / 500000000000 : ℝ)
  | 6 => (-21776707 / 500000000000 : ℝ)
  | 7 => (-43400009 / 1000000000000 : ℝ)
  | 8 => (-43239441 / 1000000000000 : ℝ)
  | 9 => (-43071621 / 1000000000000 : ℝ)
  | 10 => (-2144823 / 50000000000 : ℝ)
  | 11 => (-42713871 / 1000000000000 : ℝ)
  | 12 => (-42523763 / 1000000000000 : ℝ)
  | 13 => (-42326047 / 1000000000000 : ℝ)
  | 14 => (-5265079 / 125000000000 : ℝ)
  | 15 => (-41907427 / 1000000000000 : ℝ)
  | 16 => (-41686341 / 1000000000000 : ℝ)
  | 17 => (-20728641 / 500000000000 : ℝ)
  | 18 => (-10305039 / 250000000000 : ℝ)
  | 19 => (-5121859 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch048Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-44216013 / 1000000000000 : ℝ)
  | 1 => (-44097129 / 1000000000000 : ℝ)
  | 2 => (-43971513 / 1000000000000 : ℝ)
  | 3 => (-43839079 / 1000000000000 : ℝ)
  | 4 => (-43699741 / 1000000000000 : ℝ)
  | 5 => (-43553413 / 1000000000000 : ℝ)
  | 6 => (-5425001 / 125000000000 : ℝ)
  | 7 => (-540493 / 12500000000 : ℝ)
  | 8 => (-2153581 / 50000000000 : ℝ)
  | 9 => (-42896459 / 1000000000000 : ℝ)
  | 10 => (-4271387 / 100000000000 : ℝ)
  | 11 => (-21261881 / 500000000000 : ℝ)
  | 12 => (-21163023 / 500000000000 : ℝ)
  | 13 => (-42120631 / 1000000000000 : ℝ)
  | 14 => (-20953713 / 500000000000 : ℝ)
  | 15 => (-2084317 / 50000000000 : ℝ)
  | 16 => (-41457281 / 1000000000000 : ℝ)
  | 17 => (-8244031 / 200000000000 : ℝ)
  | 18 => (-40974871 / 1000000000000 : ℝ)
  | 19 => (-20360667 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch048Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((960 : ℝ) + (j.val : ℝ)) / 1600)
      (((960 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch048Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch048Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((960 : ℝ) + (j.val : ℝ)) / 1600)
    (((960 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch048Neg45WeightLower j.val) (hpThetaShiftThreeBatch048Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch048Neg45WeightLower, hpThetaShiftThreeBatch048Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch048Neg45_integral_bounds :
    (-2915497 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-14246027 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (960 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch048Lower hpThetaJensenCellsBatch048Upper
    hpThetaShiftThreeBatch048Neg45WeightLower hpThetaShiftThreeBatch048Neg45WeightUpper hpThetaJensenCellsBatch048_bounds hpThetaShiftThreeBatch048Neg45_weight_bounds
  have hl : (-2915497 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch048Lower j * hpThetaShiftThreeBatch048Neg45WeightLower j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftThreeBatch048Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftThreeBatch048Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch048Lower j * hpThetaShiftThreeBatch048Neg45WeightUpper j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftThreeBatch048Neg45WeightUpper j) / 1600) ≤ (-14246027 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftThreeBatch048Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (960 : ℝ) / 1600 = 48 / 80 by norm_num,
    show ((960 : ℝ) + 20) / 1600 = (48 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch048Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-37793043 / 1000000000000 : ℝ)
  | 1 => (-38350743 / 1000000000000 : ℝ)
  | 2 => (-19456033 / 500000000000 : ℝ)
  | 3 => (-39477013 / 1000000000000 : ℝ)
  | 4 => (-10011397 / 250000000000 : ℝ)
  | 5 => (-634653 / 15625000000 : ℝ)
  | 6 => (-10298407 / 250000000000 : ℝ)
  | 7 => (-20886549 / 500000000000 : ℝ)
  | 8 => (-42356203 / 1000000000000 : ℝ)
  | 9 => (-8588589 / 200000000000 : ℝ)
  | 10 => (-1741333 / 40000000000 : ℝ)
  | 11 => (-2757959 / 62500000000 : ℝ)
  | 12 => (-44725003 / 1000000000000 : ℝ)
  | 13 => (-45326303 / 1000000000000 : ℝ)
  | 14 => (-11482811 / 250000000000 : ℝ)
  | 15 => (-46539827 / 1000000000000 : ℝ)
  | 16 => (-47152051 / 1000000000000 : ℝ)
  | 17 => (-11941979 / 250000000000 : ℝ)
  | 18 => (-24193711 / 500000000000 : ℝ)
  | 19 => (-49010567 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch048Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-37238961 / 1000000000000 : ℝ)
  | 1 => (-18896521 / 500000000000 : ℝ)
  | 2 => (-19175371 / 500000000000 : ℝ)
  | 3 => (-7782413 / 200000000000 : ℝ)
  | 4 => (-9869253 / 250000000000 : ℝ)
  | 5 => (-40045587 / 1000000000000 : ℝ)
  | 6 => (-40617791 / 1000000000000 : ℝ)
  | 7 => (-41193627 / 1000000000000 : ℝ)
  | 8 => (-41773097 / 1000000000000 : ℝ)
  | 9 => (-21178101 / 500000000000 : ℝ)
  | 10 => (-1341967 / 31250000000 : ℝ)
  | 11 => (-10883331 / 250000000000 : ℝ)
  | 12 => (-44127343 / 1000000000000 : ℝ)
  | 13 => (-22362501 / 500000000000 : ℝ)
  | 14 => (-22663151 / 500000000000 : ℝ)
  | 15 => (-45931243 / 1000000000000 : ℝ)
  | 16 => (-23269913 / 500000000000 : ℝ)
  | 17 => (-943041 / 20000000000 : ℝ)
  | 18 => (-9553583 / 200000000000 : ℝ)
  | 19 => (-48387421 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch048Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((960 : ℝ) + (j.val : ℝ)) / 1600)
      (((960 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch048Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch048Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((960 : ℝ) + (j.val : ℝ)) / 1600)
    (((960 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch048Neg25WeightLower j.val) (hpThetaShiftThreeBatch048Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch048Neg25WeightLower, hpThetaShiftThreeBatch048Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch048Neg25_integral_bounds :
    (-14637653 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-7084223 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (960 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch048Lower hpThetaJensenCellsBatch048Upper
    hpThetaShiftThreeBatch048Neg25WeightLower hpThetaShiftThreeBatch048Neg25WeightUpper hpThetaJensenCellsBatch048_bounds hpThetaShiftThreeBatch048Neg25_weight_bounds
  have hl : (-14637653 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch048Lower j * hpThetaShiftThreeBatch048Neg25WeightLower j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftThreeBatch048Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftThreeBatch048Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch048Lower j * hpThetaShiftThreeBatch048Neg25WeightUpper j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftThreeBatch048Neg25WeightUpper j) / 1600) ≤ (-7084223 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftThreeBatch048Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (960 : ℝ) / 1600 = 48 / 80 by norm_num,
    show ((960 : ℝ) + 20) / 1600 = (48 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch048Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch048Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch048Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch048Neg25_integral_bounds
end HodgeProofHP
