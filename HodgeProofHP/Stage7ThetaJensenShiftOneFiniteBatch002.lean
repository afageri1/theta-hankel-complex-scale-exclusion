/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch002

/-! Exact signed weight and batch integral certificates, batch 2 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch002Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (302795319 / 1000000000000 : ℝ)
  | 1 => (317611561 / 1000000000000 : ℝ)
  | 2 => (33274273 / 100000000000 : ℝ)
  | 3 => (69637031 / 200000000000 : ℝ)
  | 4 => (363935081 / 1000000000000 : ℝ)
  | 5 => (5937323 / 15625000000 : ℝ)
  | 6 => (396342011 / 1000000000000 : ℝ)
  | 7 => (412991099 / 1000000000000 : ℝ)
  | 8 => (429931859 / 1000000000000 : ℝ)
  | 9 => (111790033 / 250000000000 : ℝ)
  | 10 => (464671681 / 1000000000000 : ℝ)
  | 11 => (482462189 / 1000000000000 : ℝ)
  | 12 => (250263631 / 500000000000 : ℝ)
  | 13 => (129715607 / 250000000000 : ℝ)
  | 14 => (16795723 / 31250000000 : ℝ)
  | 15 => (556324761 / 1000000000000 : ℝ)
  | 16 => (575442601 / 1000000000000 : ℝ)
  | 17 => (148702969 / 250000000000 : ℝ)
  | 18 => (76803467 / 125000000000 : ℝ)
  | 19 => (158571313 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch002Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (158805781 / 500000000000 : ℝ)
  | 1 => (332742731 / 1000000000000 : ℝ)
  | 2 => (87046289 / 250000000000 : ℝ)
  | 3 => (181967541 / 500000000000 : ℝ)
  | 4 => (379988673 / 1000000000000 : ℝ)
  | 5 => (99085503 / 250000000000 : ℝ)
  | 6 => (4129911 / 10000000000 : ℝ)
  | 7 => (21496593 / 50000000000 : ℝ)
  | 8 => (447160133 / 1000000000000 : ℝ)
  | 9 => (232335841 / 500000000000 : ℝ)
  | 10 => (48246219 / 100000000000 : ℝ)
  | 11 => (500527263 / 1000000000000 : ℝ)
  | 12 => (518862429 / 1000000000000 : ℝ)
  | 13 => (537463137 / 1000000000000 : ℝ)
  | 14 => (278162381 / 500000000000 : ℝ)
  | 15 => (287721301 / 500000000000 : ℝ)
  | 16 => (594811877 / 1000000000000 : ℝ)
  | 17 => (614427737 / 1000000000000 : ℝ)
  | 18 => (634285253 / 1000000000000 : ℝ)
  | 19 => (26175177 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch002Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((40 : ℝ) + (j.val : ℝ)) / 1600)
      (((40 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch002Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch002Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((40 : ℝ) + (j.val : ℝ)) / 1600)
    (((40 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch002Neg100WeightLower j.val) (hpThetaShiftOneBatch002Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch002Neg100WeightLower, hpThetaShiftOneBatch002Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch002Neg100_integral_bounds :
    (2026916517 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (10634125229 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (40 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch002Lower hpThetaJensenCellsBatch002Upper
    hpThetaShiftOneBatch002Neg100WeightLower hpThetaShiftOneBatch002Neg100WeightUpper hpThetaJensenCellsBatch002_bounds hpThetaShiftOneBatch002Neg100_weight_bounds
  have hl : (2026916517 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch002Lower j * hpThetaShiftOneBatch002Neg100WeightLower j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftOneBatch002Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftOneBatch002Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch002Lower j * hpThetaShiftOneBatch002Neg100WeightUpper j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftOneBatch002Neg100WeightUpper j) / 1600) ≤ (10634125229 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftOneBatch002Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (40 : ℝ) / 1600 = 2 / 80 by norm_num,
    show ((40 : ℝ) + 20) / 1600 = (2 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch002Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (153089053 / 500000000000 : ℝ)
  | 1 => (160671781 / 500000000000 : ℝ)
  | 2 => (168425077 / 500000000000 : ℝ)
  | 3 => (176347733 / 500000000000 : ℝ)
  | 4 => (184438513 / 500000000000 : ℝ)
  | 5 => (96348077 / 250000000000 : ℝ)
  | 6 => (40223873 / 100000000000 : ℝ)
  | 7 => (52426707 / 125000000000 : ℝ)
  | 8 => (436914393 / 1000000000000 : ℝ)
  | 9 => (113684549 / 250000000000 : ℝ)
  | 10 => (59110283 / 125000000000 : ℝ)
  | 11 => (3838623 / 7812500000 : ℝ)
  | 12 => (255059863 / 500000000000 : ℝ)
  | 13 => (529207249 / 1000000000000 : ℝ)
  | 14 => (548603297 / 1000000000000 : ℝ)
  | 15 => (284152401 / 500000000000 : ℝ)
  | 16 => (294154321 / 500000000000 : ℝ)
  | 17 => (608611643 / 1000000000000 : ℝ)
  | 18 => (629210579 / 1000000000000 : ℝ)
  | 19 => (650102169 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch002Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (321343563 / 1000000000000 : ℝ)
  | 1 => (67370031 / 200000000000 : ℝ)
  | 2 => (352695467 / 1000000000000 : ℝ)
  | 3 => (368877027 / 1000000000000 : ℝ)
  | 4 => (385392309 / 1000000000000 : ℝ)
  | 5 => (402238731 / 1000000000000 : ℝ)
  | 6 => (419413657 / 1000000000000 : ℝ)
  | 7 => (218457197 / 500000000000 : ℝ)
  | 8 => (454738197 / 1000000000000 : ℝ)
  | 9 => (94576453 / 200000000000 : ℝ)
  | 10 => (98268749 / 200000000000 : ℝ)
  | 11 => (510119727 / 1000000000000 : ℝ)
  | 12 => (2116829 / 4000000000 : ℝ)
  | 13 => (274301649 / 500000000000 : ℝ)
  | 14 => (568304803 / 1000000000000 : ℝ)
  | 15 => (588308643 / 1000000000000 : ℝ)
  | 16 => (152152911 / 250000000000 : ℝ)
  | 17 => (31460529 / 50000000000 : ℝ)
  | 18 => (65010217 / 100000000000 : ℝ)
  | 19 => (335641543 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch002Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((40 : ℝ) + (j.val : ℝ)) / 1600)
      (((40 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch002Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch002Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((40 : ℝ) + (j.val : ℝ)) / 1600)
    (((40 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch002Neg65WeightLower j.val) (hpThetaShiftOneBatch002Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch002Neg65WeightLower, hpThetaShiftOneBatch002Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch002Neg65_integral_bounds :
    (5160977511 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (5419268069 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (40 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch002Lower hpThetaJensenCellsBatch002Upper
    hpThetaShiftOneBatch002Neg65WeightLower hpThetaShiftOneBatch002Neg65WeightUpper hpThetaJensenCellsBatch002_bounds hpThetaShiftOneBatch002Neg65_weight_bounds
  have hl : (5160977511 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch002Lower j * hpThetaShiftOneBatch002Neg65WeightLower j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftOneBatch002Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftOneBatch002Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch002Lower j * hpThetaShiftOneBatch002Neg65WeightUpper j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftOneBatch002Neg65WeightUpper j) / 1600) ≤ (5419268069 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftOneBatch002Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (40 : ℝ) / 1600 = 2 / 80 by norm_num,
    show ((40 : ℝ) + 20) / 1600 = (2 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch002Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (308603509 / 1000000000000 : ℝ)
  | 1 => (324019861 / 1000000000000 : ℝ)
  | 2 => (10618633 / 31250000000 : ℝ)
  | 3 => (355931197 / 1000000000000 : ℝ)
  | 4 => (372423147 / 1000000000000 : ℝ)
  | 5 => (194635269 / 500000000000 : ℝ)
  | 6 => (81294353 / 200000000000 : ℝ)
  | 7 => (106006297 / 250000000000 : ℝ)
  | 8 => (88385827 / 200000000000 : ℝ)
  | 9 => (230090947 / 500000000000 : ℝ)
  | 10 => (19151269 / 40000000000 : ℝ)
  | 11 => (497726847 / 1000000000000 : ℝ)
  | 12 => (64626931 / 125000000000 : ℝ)
  | 13 => (268322841 / 500000000000 : ℝ)
  | 14 => (556615667 / 1000000000000 : ℝ)
  | 15 => (18028859 / 31250000000 : ℝ)
  | 16 => (298783597 / 500000000000 : ℝ)
  | 17 => (618544803 / 1000000000000 : ℝ)
  | 18 => (79981787 / 125000000000 : ℝ)
  | 19 => (330746811 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch002Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (162009931 / 500000000000 : ℝ)
  | 1 => (339796257 / 1000000000000 : ℝ)
  | 2 => (177965599 / 500000000000 : ℝ)
  | 3 => (93105787 / 250000000000 : ℝ)
  | 4 => (389270539 / 1000000000000 : ℝ)
  | 5 => (203235883 / 500000000000 : ℝ)
  | 6 => (424025189 / 1000000000000 : ℝ)
  | 7 => (27620571 / 62500000000 : ℝ)
  | 8 => (92036379 / 200000000000 : ℝ)
  | 9 => (239390863 / 500000000000 : ℝ)
  | 10 => (3888491 / 7812500000 : ℝ)
  | 11 => (517015449 / 1000000000000 : ℝ)
  | 12 => (536645683 / 1000000000000 : ℝ)
  | 13 => (139153917 / 250000000000 : ℝ)
  | 14 => (576923489 / 1000000000000 : ℝ)
  | 15 => (119513439 / 200000000000 : ℝ)
  | 16 => (154636201 / 250000000000 : ℝ)
  | 17 => (639854297 / 1000000000000 : ℝ)
  | 18 => (661493623 / 1000000000000 : ℝ)
  | 19 => (683460697 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch002Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((40 : ℝ) + (j.val : ℝ)) / 1600)
      (((40 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch002Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch002Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((40 : ℝ) + (j.val : ℝ)) / 1600)
    (((40 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch002Neg40WeightLower j.val) (hpThetaShiftOneBatch002Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch002Neg40WeightLower, hpThetaShiftOneBatch002Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch002Neg40_integral_bounds :
    (1307082679 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (10985527147 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (40 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch002Lower hpThetaJensenCellsBatch002Upper
    hpThetaShiftOneBatch002Neg40WeightLower hpThetaShiftOneBatch002Neg40WeightUpper hpThetaJensenCellsBatch002_bounds hpThetaShiftOneBatch002Neg40_weight_bounds
  have hl : (1307082679 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch002Lower j * hpThetaShiftOneBatch002Neg40WeightLower j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftOneBatch002Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftOneBatch002Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch002Lower j * hpThetaShiftOneBatch002Neg40WeightUpper j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftOneBatch002Neg40WeightUpper j) / 1600) ≤ (10985527147 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftOneBatch002Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (40 : ℝ) / 1600 = 2 / 80 by norm_num,
    show ((40 : ℝ) + 20) / 1600 = (2 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch002Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (62109863 / 200000000000 : ℝ)
  | 1 => (163083629 / 500000000000 : ℝ)
  | 2 => (85540121 / 250000000000 : ℝ)
  | 3 => (4481603 / 12500000000 : ℝ)
  | 4 => (375269753 / 1000000000000 : ℝ)
  | 5 => (392384231 / 1000000000000 : ℝ)
  | 6 => (409870867 / 1000000000000 : ℝ)
  | 7 => (427728833 / 1000000000000 : ℝ)
  | 8 => (222978643 / 500000000000 : ℝ)
  | 9 => (116138841 / 250000000000 : ℝ)
  | 10 => (483522187 / 1000000000000 : ℝ)
  | 11 => (62857107 / 125000000000 : ℝ)
  | 12 => (522558457 / 1000000000000 : ℝ)
  | 13 => (542626057 / 1000000000000 : ℝ)
  | 14 => (35191169 / 62500000000 : ℝ)
  | 15 => (583855429 / 1000000000000 : ℝ)
  | 16 => (302507623 / 500000000000 : ℝ)
  | 17 => (9789643 / 15625000000 : ℝ)
  | 18 => (5187361 / 8000000000 : ℝ)
  | 19 => (1073061 / 1600000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch002Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (326167259 / 1000000000000 : ℝ)
  | 1 => (68432097 / 200000000000 : ℝ)
  | 2 => (358528241 / 1000000000000 : ℝ)
  | 3 => (187634877 / 500000000000 : ℝ)
  | 4 => (49048029 / 125000000000 : ℝ)
  | 5 => (102467717 / 250000000000 : ℝ)
  | 6 => (213864417 / 500000000000 : ℝ)
  | 7 => (445957287 / 1000000000000 : ℝ)
  | 8 => (92911073 / 200000000000 : ℝ)
  | 9 => (120880547 / 250000000000 : ℝ)
  | 10 => (502856857 / 1000000000000 : ℝ)
  | 11 => (261279229 / 500000000000 : ℝ)
  | 12 => (271313029 / 500000000000 : ℝ)
  | 13 => (112611741 / 200000000000 : ℝ)
  | 14 => (58385543 / 100000000000 : ℝ)
  | 15 => (605015247 / 1000000000000 : ℝ)
  | 16 => (626537153 / 1000000000000 : ℝ)
  | 17 => (324210063 / 500000000000 : ℝ)
  | 18 => (335331563 / 500000000000 : ℝ)
  | 19 => (86658137 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch002Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((40 : ℝ) + (j.val : ℝ)) / 1600)
      (((40 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch002Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch002Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((40 : ℝ) + (j.val : ℝ)) / 1600)
    (((40 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch002Neg20WeightLower j.val) (hpThetaShiftOneBatch002Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch002Neg20WeightLower, hpThetaShiftOneBatch002Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch002Neg20_integral_bounds :
    (10564949043 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (2 / 80 : ℝ) ((2 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (5551855593 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (40 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch002Lower hpThetaJensenCellsBatch002Upper
    hpThetaShiftOneBatch002Neg20WeightLower hpThetaShiftOneBatch002Neg20WeightUpper hpThetaJensenCellsBatch002_bounds hpThetaShiftOneBatch002Neg20_weight_bounds
  have hl : (10564949043 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch002Lower j * hpThetaShiftOneBatch002Neg20WeightLower j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftOneBatch002Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftOneBatch002Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch002Lower j * hpThetaShiftOneBatch002Neg20WeightUpper j)
        (hpThetaJensenCellsBatch002Upper j * hpThetaShiftOneBatch002Neg20WeightUpper j) / 1600) ≤ (5551855593 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch002Lower, hpThetaJensenCellsBatch002Upper,
      hpThetaShiftOneBatch002Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (40 : ℝ) / 1600 = 2 / 80 by norm_num,
    show ((40 : ℝ) + 20) / 1600 = (2 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch002Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch002Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch002Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch002Neg20_integral_bounds
end HodgeProofHP
