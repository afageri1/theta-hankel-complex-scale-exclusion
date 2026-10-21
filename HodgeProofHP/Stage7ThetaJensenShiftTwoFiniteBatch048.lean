/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch048

/-! Exact signed weight and batch integral certificates, batch 48 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch048Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1533193871 / 250000000000 : ℝ)
  | 1 => (-320385829 / 50000000000 : ℝ)
  | 2 => (-3343872873 / 500000000000 : ℝ)
  | 3 => (-139458579 / 20000000000 : ℝ)
  | 4 => (-3631666407 / 500000000000 : ℝ)
  | 5 => (-1889756157 / 250000000000 : ℝ)
  | 6 => (-3930036173 / 500000000000 : ℝ)
  | 7 => (-8166544597 / 1000000000000 : ℝ)
  | 8 => (-8478510687 / 1000000000000 : ℝ)
  | 9 => (-274876269 / 31250000000 : ℝ)
  | 10 => (-113990063 / 12500000000 : ℝ)
  | 11 => (-9448075357 / 1000000000000 : ℝ)
  | 12 => (-9782723633 / 1000000000000 : ℝ)
  | 13 => (-10123222647 / 1000000000000 : ℝ)
  | 14 => (-1046964589 / 100000000000 : ℝ)
  | 15 => (-10822067569 / 1000000000000 : ℝ)
  | 16 => (-1118056261 / 100000000000 : ℝ)
  | 17 => (-1154520667 / 100000000000 : ℝ)
  | 18 => (-1489509517 / 125000000000 : ℝ)
  | 19 => (-2458649627 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch048Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2931428571 / 500000000000 : ℝ)
  | 1 => (-6132775483 / 1000000000000 : ℝ)
  | 2 => (-6407716579 / 1000000000000 : ℝ)
  | 3 => (-1337549149 / 200000000000 : ℝ)
  | 4 => (-6972928949 / 1000000000000 : ℝ)
  | 5 => (-7263332813 / 1000000000000 : ℝ)
  | 6 => (-7559024627 / 1000000000000 : ℝ)
  | 7 => (-1572014469 / 200000000000 : ℝ)
  | 8 => (-2041636149 / 250000000000 : ℝ)
  | 9 => (-4239255343 / 500000000000 : ℝ)
  | 10 => (-8796040607 / 1000000000000 : ℝ)
  | 11 => (-9119205039 / 1000000000000 : ℝ)
  | 12 => (-2362018839 / 250000000000 : ℝ)
  | 13 => (-611420227 / 62500000000 : ℝ)
  | 14 => (-5061611323 / 500000000000 : ℝ)
  | 15 => (-10469645889 / 1000000000000 : ℝ)
  | 16 => (-676379223 / 62500000000 : ℝ)
  | 17 => (-11180562609 / 1000000000000 : ℝ)
  | 18 => (-11545206669 / 1000000000000 : ℝ)
  | 19 => (-2383215227 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch048Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((960 : ℝ) + (j.val : ℝ)) / 1600)
      (((960 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch048Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch048Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((960 : ℝ) + (j.val : ℝ)) / 1600)
    (((960 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch048Neg100WeightLower j.val) (hpThetaShiftTwoBatch048Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch048Neg100WeightLower, hpThetaShiftTwoBatch048Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch048Neg100_integral_bounds :
    (-759234863 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-114945887 / 40000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (960 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch048Lower hpThetaJensenCellsBatch048Upper
    hpThetaShiftTwoBatch048Neg100WeightLower hpThetaShiftTwoBatch048Neg100WeightUpper hpThetaJensenCellsBatch048_bounds hpThetaShiftTwoBatch048Neg100_weight_bounds
  have hl : (-759234863 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch048Lower j * hpThetaShiftTwoBatch048Neg100WeightLower j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftTwoBatch048Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftTwoBatch048Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch048Lower j * hpThetaShiftTwoBatch048Neg100WeightUpper j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftTwoBatch048Neg100WeightUpper j) / 1600) ≤ (-114945887 / 40000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftTwoBatch048Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (960 : ℝ) / 1600 = 48 / 80 by norm_num,
    show ((960 : ℝ) + 20) / 1600 = (48 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch048Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (6792582857 / 1000000000000 : ℝ)
  | 1 => (855967597 / 125000000000 : ℝ)
  | 2 => (431431391 / 62500000000 : ℝ)
  | 3 => (347903029 / 50000000000 : ℝ)
  | 4 => (3506604463 / 500000000000 : ℝ)
  | 5 => (176708509 / 25000000000 : ℝ)
  | 6 => (1780861959 / 250000000000 : ℝ)
  | 7 => (7178524197 / 1000000000000 : ℝ)
  | 8 => (723356217 / 100000000000 : ℝ)
  | 9 => (1822138593 / 250000000000 : ℝ)
  | 10 => (7343493299 / 1000000000000 : ℝ)
  | 11 => (7398371333 / 1000000000000 : ℝ)
  | 12 => (7453180739 / 1000000000000 : ℝ)
  | 13 => (7507913659 / 1000000000000 : ℝ)
  | 14 => (189064053 / 25000000000 : ℝ)
  | 15 => (3808559011 / 500000000000 : ℝ)
  | 16 => (7671573147 / 1000000000000 : ℝ)
  | 17 => (154518383 / 20000000000 : ℝ)
  | 18 => (1945036891 / 250000000000 : ℝ)
  | 19 => (122410153 / 15625000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch048Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (6847740777 / 1000000000000 : ℝ)
  | 1 => (6902902257 / 1000000000000 : ℝ)
  | 2 => (6958060581 / 1000000000000 : ℝ)
  | 3 => (7013208927 / 1000000000000 : ℝ)
  | 4 => (7068340361 / 1000000000000 : ℝ)
  | 5 => (7123447837 / 1000000000000 : ℝ)
  | 6 => (3589262099 / 500000000000 : ℝ)
  | 7 => (7233562171 / 1000000000000 : ℝ)
  | 8 => (7288554373 / 1000000000000 : ℝ)
  | 9 => (73434933 / 10000000000 : ℝ)
  | 10 => (3699185667 / 500000000000 : ℝ)
  | 11 => (372659037 / 50000000000 : ℝ)
  | 12 => (375395683 / 50000000000 : ℝ)
  | 13 => (7562562121 / 1000000000000 : ℝ)
  | 14 => (7617118023 / 1000000000000 : ℝ)
  | 15 => (1917893287 / 250000000000 : ℝ)
  | 16 => (7725919151 / 1000000000000 : ℝ)
  | 17 => (1556029513 / 200000000000 : ℝ)
  | 18 => (7834249793 / 1000000000000 : ℝ)
  | 19 => (1577643423 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch048Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((960 : ℝ) + (j.val : ℝ)) / 1600)
      (((960 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch048Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch048Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((960 : ℝ) + (j.val : ℝ)) / 1600)
    (((960 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch048Neg65WeightLower j.val) (hpThetaShiftTwoBatch048Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch048Neg65WeightLower, hpThetaShiftTwoBatch048Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch048Neg65_integral_bounds :
    (1215920989 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (124837041 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (960 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch048Lower hpThetaJensenCellsBatch048Upper
    hpThetaShiftTwoBatch048Neg65WeightLower hpThetaShiftTwoBatch048Neg65WeightUpper hpThetaJensenCellsBatch048_bounds hpThetaShiftTwoBatch048Neg65_weight_bounds
  have hl : (1215920989 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch048Lower j * hpThetaShiftTwoBatch048Neg65WeightLower j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftTwoBatch048Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftTwoBatch048Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch048Lower j * hpThetaShiftTwoBatch048Neg65WeightUpper j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftTwoBatch048Neg65WeightUpper j) / 1600) ≤ (124837041 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftTwoBatch048Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (960 : ℝ) / 1600 = 48 / 80 by norm_num,
    show ((960 : ℝ) + 20) / 1600 = (48 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch048Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (10341 / 12500000 : ℝ)
  | 1 => (860735771 / 1000000000000 : ℝ)
  | 2 => (894536163 / 1000000000000 : ℝ)
  | 3 => (928682573 / 1000000000000 : ℝ)
  | 4 => (963176387 / 1000000000000 : ℝ)
  | 5 => (998018981 / 1000000000000 : ℝ)
  | 6 => (516605859 / 500000000000 : ℝ)
  | 7 => (534377977 / 500000000000 : ℝ)
  | 8 => (110465303 / 100000000000 : ℝ)
  | 9 => (285226069 / 250000000000 : ℝ)
  | 10 => (1177511013 / 1000000000000 : ℝ)
  | 11 => (1214474547 / 1000000000000 : ℝ)
  | 12 => (312949043 / 250000000000 : ℝ)
  | 13 => (322369293 / 250000000000 : ℝ)
  | 14 => (41484963 / 31250000000 : ℝ)
  | 15 => (34148059 / 25000000000 : ℝ)
  | 16 => (1404689047 / 1000000000000 : ℝ)
  | 17 => (1443820109 / 1000000000000 : ℝ)
  | 18 => (37082919 / 25000000000 : ℝ)
  | 19 => (1523180203 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch048Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (215183943 / 250000000000 : ℝ)
  | 1 => (223634041 / 250000000000 : ℝ)
  | 2 => (464341287 / 500000000000 : ℝ)
  | 3 => (240794097 / 250000000000 : ℝ)
  | 4 => (499009491 / 500000000000 : ℝ)
  | 5 => (1033211719 / 1000000000000 : ℝ)
  | 6 => (213751191 / 200000000000 : ℝ)
  | 7 => (1104653031 / 1000000000000 : ℝ)
  | 8 => (1140904277 / 1000000000000 : ℝ)
  | 9 => (588755507 / 500000000000 : ℝ)
  | 10 => (303618637 / 250000000000 : ℝ)
  | 11 => (1251796173 / 1000000000000 : ℝ)
  | 12 => (1289477173 / 1000000000000 : ℝ)
  | 13 => (1327518817 / 1000000000000 : ℝ)
  | 14 => (1365922361 / 1000000000000 : ℝ)
  | 15 => (175586131 / 125000000000 : ℝ)
  | 16 => (144382011 / 100000000000 : ℝ)
  | 17 => (1483316761 / 1000000000000 : ℝ)
  | 18 => (380795051 / 250000000000 : ℝ)
  | 19 => (1563411627 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch048Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((960 : ℝ) + (j.val : ℝ)) / 1600)
      (((960 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch048Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch048Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((960 : ℝ) + (j.val : ℝ)) / 1600)
    (((960 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch048Neg45WeightLower j.val) (hpThetaShiftTwoBatch048Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch048Neg45WeightLower, hpThetaShiftTwoBatch048Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch048Neg45_integral_bounds :
    (384179687 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (403956749 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (960 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch048Lower hpThetaJensenCellsBatch048Upper
    hpThetaShiftTwoBatch048Neg45WeightLower hpThetaShiftTwoBatch048Neg45WeightUpper hpThetaJensenCellsBatch048_bounds hpThetaShiftTwoBatch048Neg45_weight_bounds
  have hl : (384179687 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch048Lower j * hpThetaShiftTwoBatch048Neg45WeightLower j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftTwoBatch048Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftTwoBatch048Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch048Lower j * hpThetaShiftTwoBatch048Neg45WeightUpper j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftTwoBatch048Neg45WeightUpper j) / 1600) ≤ (403956749 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftTwoBatch048Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (960 : ℝ) / 1600 = 48 / 80 by norm_num,
    show ((960 : ℝ) + 20) / 1600 = (48 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch048Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-344017369 / 125000000000 : ℝ)
  | 1 => (-1382840097 / 500000000000 : ℝ)
  | 2 => (-2779194231 / 1000000000000 : ℝ)
  | 3 => (-698170033 / 250000000000 : ℝ)
  | 4 => (-4384589 / 1562500000 : ℝ)
  | 5 => (-2819563771 / 1000000000000 : ℝ)
  | 6 => (-1416479807 / 500000000000 : ℝ)
  | 7 => (-2846323533 / 1000000000000 : ℝ)
  | 8 => (-571930913 / 200000000000 : ℝ)
  | 9 => (-1436475869 / 500000000000 : ℝ)
  | 10 => (-2886214077 / 1000000000000 : ℝ)
  | 11 => (-2899440599 / 1000000000000 : ℝ)
  | 12 => (-2912630313 / 1000000000000 : ℝ)
  | 13 => (-2925782223 / 1000000000000 : ℝ)
  | 14 => (-1469447663 / 500000000000 : ℝ)
  | 15 => (-737992153 / 250000000000 : ℝ)
  | 16 => (-370625133 / 125000000000 : ℝ)
  | 17 => (-148899583 / 50000000000 : ℝ)
  | 18 => (-299093937 / 100000000000 : ℝ)
  | 19 => (-750960789 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch048Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-684642857 / 250000000000 : ℝ)
  | 1 => (-2752138951 / 1000000000000 : ℝ)
  | 2 => (-2765680193 / 1000000000000 : ℝ)
  | 3 => (-277919423 / 100000000000 : ℝ)
  | 4 => (-2792680131 / 1000000000000 : ℝ)
  | 5 => (-2806136959 / 1000000000000 : ℝ)
  | 6 => (-281956377 / 100000000000 : ℝ)
  | 7 => (-2832959613 / 1000000000000 : ℝ)
  | 8 => (-711580883 / 250000000000 : ℝ)
  | 9 => (-714913641 / 250000000000 : ℝ)
  | 10 => (-2872951737 / 1000000000000 : ℝ)
  | 11 => (-721553519 / 250000000000 : ℝ)
  | 12 => (-1449720299 / 500000000000 : ℝ)
  | 13 => (-364078789 / 125000000000 : ℝ)
  | 14 => (-1462891111 / 500000000000 : ℝ)
  | 15 => (-117555813 / 40000000000 : ℝ)
  | 16 => (-2951968611 / 1000000000000 : ℝ)
  | 17 => (-2965001063 / 1000000000000 : ℝ)
  | 18 => (-2977991659 / 1000000000000 : ℝ)
  | 19 => (-2990939369 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch048Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((960 : ℝ) + (j.val : ℝ)) / 1600)
      (((960 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch048Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch048Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((960 : ℝ) + (j.val : ℝ)) / 1600)
    (((960 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch048Neg25WeightLower j.val) (hpThetaShiftTwoBatch048Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch048Neg25WeightLower, hpThetaShiftTwoBatch048Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch048Neg25_integral_bounds :
    (-976276381 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (48 / 80 : ℝ) ((48 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-953618563 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (960 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch048Lower hpThetaJensenCellsBatch048Upper
    hpThetaShiftTwoBatch048Neg25WeightLower hpThetaShiftTwoBatch048Neg25WeightUpper hpThetaJensenCellsBatch048_bounds hpThetaShiftTwoBatch048Neg25_weight_bounds
  have hl : (-976276381 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch048Lower j * hpThetaShiftTwoBatch048Neg25WeightLower j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftTwoBatch048Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftTwoBatch048Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch048Lower j * hpThetaShiftTwoBatch048Neg25WeightUpper j)
        (hpThetaJensenCellsBatch048Upper j * hpThetaShiftTwoBatch048Neg25WeightUpper j) / 1600) ≤ (-953618563 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch048Lower, hpThetaJensenCellsBatch048Upper,
      hpThetaShiftTwoBatch048Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (960 : ℝ) / 1600 = 48 / 80 by norm_num,
    show ((960 : ℝ) + 20) / 1600 = (48 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch048Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch048Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch048Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch048Neg25_integral_bounds
end HodgeProofHP
