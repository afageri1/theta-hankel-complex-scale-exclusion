/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch001

/-! Exact signed weight and batch integral certificates, batch 1 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch001Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (77515601 / 1000000000000 : ℝ)
  | 1 => (85392203 / 1000000000000 : ℝ)
  | 2 => (93639323 / 1000000000000 : ℝ)
  | 3 => (3195469 / 31250000000 : ℝ)
  | 4 => (111237221 / 1000000000000 : ℝ)
  | 5 => (15072979 / 125000000000 : ℝ)
  | 6 => (1042341 / 8000000000 : ℝ)
  | 7 => (28072259 / 200000000000 : ℝ)
  | 8 => (18848431 / 125000000000 : ℝ)
  | 9 => (80784303 / 500000000000 : ℝ)
  | 10 => (172702199 / 1000000000000 : ℝ)
  | 11 => (46046393 / 250000000000 : ℝ)
  | 12 => (12250999 / 62500000000 : ℝ)
  | 13 => (208190607 / 1000000000000 : ℝ)
  | 14 => (220706527 / 1000000000000 : ℝ)
  | 15 => (233560743 / 1000000000000 : ℝ)
  | 16 => (24675017 / 100000000000 : ℝ)
  | 17 => (260271639 / 1000000000000 : ℝ)
  | 18 => (274121893 / 1000000000000 : ℝ)
  | 19 => (144148797 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch001Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (21348051 / 250000000000 : ℝ)
  | 1 => (23409831 / 250000000000 : ℝ)
  | 2 => (102255009 / 1000000000000 : ℝ)
  | 3 => (55618611 / 500000000000 : ℝ)
  | 4 => (120583833 / 1000000000000 : ℝ)
  | 5 => (65146313 / 500000000000 : ℝ)
  | 6 => (8772581 / 62500000000 : ℝ)
  | 7 => (150787449 / 1000000000000 : ℝ)
  | 8 => (161568607 / 1000000000000 : ℝ)
  | 9 => (863511 / 5000000000 : ℝ)
  | 10 => (184185573 / 1000000000000 : ℝ)
  | 11 => (39203197 / 200000000000 : ℝ)
  | 12 => (13011913 / 62500000000 : ℝ)
  | 13 => (6897079 / 31250000000 : ℝ)
  | 14 => (29195093 / 125000000000 : ℝ)
  | 15 => (246750171 / 1000000000000 : ℝ)
  | 16 => (6506791 / 25000000000 : ℝ)
  | 17 => (137060947 / 500000000000 : ℝ)
  | 18 => (57659519 / 200000000000 : ℝ)
  | 19 => (7569883 / 25000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch001Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((20 : ℝ) + (j.val : ℝ)) / 1600)
      (((20 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch001Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch001Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((20 : ℝ) + (j.val : ℝ)) / 1600)
    (((20 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch001Neg100WeightLower j.val) (hpThetaShiftOneBatch001Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch001Neg100WeightLower, hpThetaShiftOneBatch001Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch001Neg100_integral_bounds :
    (3826410349 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (4119113867 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (20 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch001Lower hpThetaJensenCellsBatch001Upper
    hpThetaShiftOneBatch001Neg100WeightLower hpThetaShiftOneBatch001Neg100WeightUpper hpThetaJensenCellsBatch001_bounds hpThetaShiftOneBatch001Neg100_weight_bounds
  have hl : (3826410349 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch001Lower j * hpThetaShiftOneBatch001Neg100WeightLower j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftOneBatch001Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftOneBatch001Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch001Lower j * hpThetaShiftOneBatch001Neg100WeightUpper j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftOneBatch001Neg100WeightUpper j) / 1600) ≤ (4119113867 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftOneBatch001Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (20 : ℝ) / 1600 = 1 / 80 by norm_num,
    show ((20 : ℝ) + 20) / 1600 = (1 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch001Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (38864337 / 500000000000 : ℝ)
  | 1 => (42825563 / 500000000000 : ℝ)
  | 2 => (93951113 / 1000000000000 : ℝ)
  | 3 => (102627363 / 1000000000000 : ℝ)
  | 4 => (55839273 / 500000000000 : ℝ)
  | 5 => (121103273 / 1000000000000 : ℝ)
  | 6 => (130900097 / 1000000000000 : ℝ)
  | 7 => (70533757 / 500000000000 : ℝ)
  | 8 => (3790099 / 25000000000 : ℝ)
  | 9 => (81253907 / 500000000000 : ℝ)
  | 10 => (86888699 / 500000000000 : ℝ)
  | 11 => (185410977 / 1000000000000 : ℝ)
  | 12 => (39481351 / 200000000000 : ℝ)
  | 13 => (209762883 / 1000000000000 : ℝ)
  | 14 => (55619363 / 250000000000 : ℝ)
  | 15 => (235548497 / 1000000000000 : ℝ)
  | 16 => (62243499 / 250000000000 : ℝ)
  | 17 => (26275187 / 100000000000 : ℝ)
  | 18 => (276879983 / 1000000000000 : ℝ)
  | 19 => (58271229 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch001Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (85651127 / 1000000000000 : ℝ)
  | 1 => (46975557 / 500000000000 : ℝ)
  | 2 => (25656841 / 250000000000 : ℝ)
  | 3 => (111678547 / 1000000000000 : ℝ)
  | 4 => (60551637 / 500000000000 : ℝ)
  | 5 => (65450049 / 500000000000 : ℝ)
  | 6 => (28213503 / 200000000000 : ℝ)
  | 7 => (151603961 / 1000000000000 : ℝ)
  | 8 => (32501563 / 200000000000 : ℝ)
  | 9 => (173777399 / 1000000000000 : ℝ)
  | 10 => (92705489 / 500000000000 : ℝ)
  | 11 => (49351689 / 250000000000 : ℝ)
  | 12 => (52440721 / 250000000000 : ℝ)
  | 13 => (222477453 / 1000000000000 : ℝ)
  | 14 => (117774249 / 500000000000 : ℝ)
  | 15 => (248973997 / 1000000000000 : ℝ)
  | 16 => (262751871 / 1000000000000 : ℝ)
  | 17 => (17304999 / 62500000000 : ℝ)
  | 18 => (145678073 / 500000000000 : ℝ)
  | 19 => (306178107 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch001Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((20 : ℝ) + (j.val : ℝ)) / 1600)
      (((20 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch001Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch001Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((20 : ℝ) + (j.val : ℝ)) / 1600)
    (((20 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch001Neg65WeightLower j.val) (hpThetaShiftOneBatch001Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch001Neg65WeightLower, hpThetaShiftOneBatch001Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch001Neg65_integral_bounds :
    (1926880359 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (2075149621 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (20 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch001Lower hpThetaJensenCellsBatch001Upper
    hpThetaShiftOneBatch001Neg65WeightLower hpThetaShiftOneBatch001Neg65WeightUpper hpThetaJensenCellsBatch001_bounds hpThetaShiftOneBatch001Neg65_weight_bounds
  have hl : (1926880359 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch001Lower j * hpThetaShiftOneBatch001Neg65WeightLower j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftOneBatch001Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftOneBatch001Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch001Lower j * hpThetaShiftOneBatch001Neg65WeightUpper j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftOneBatch001Neg65WeightUpper j) / 1600) ≤ (2075149621 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftOneBatch001Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (20 : ℝ) / 1600 = 1 / 80 by norm_num,
    show ((20 : ℝ) + 20) / 1600 = (1 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch001Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (77881011 / 1000000000000 : ℝ)
  | 1 => (42918131 / 500000000000 : ℝ)
  | 2 => (94174073 / 1000000000000 : ℝ)
  | 3 => (102893661 / 1000000000000 : ℝ)
  | 4 => (22398841 / 200000000000 : ℝ)
  | 5 => (121474847 / 1000000000000 : ℝ)
  | 6 => (16416837 / 125000000000 : ℝ)
  | 7 => (141572821 / 1000000000000 : ℝ)
  | 8 => (152188257 / 1000000000000 : ℝ)
  | 9 => (32636001 / 200000000000 : ℝ)
  | 10 => (6981881 / 40000000000 : ℝ)
  | 11 => (93144123 / 500000000000 : ℝ)
  | 12 => (198402559 / 1000000000000 : ℝ)
  | 13 => (105444409 / 500000000000 : ℝ)
  | 14 => (55936461 / 250000000000 : ℝ)
  | 15 => (236972421 / 1000000000000 : ℝ)
  | 16 => (1957557 / 7812500000 : ℝ)
  | 17 => (264529183 / 1000000000000 : ℝ)
  | 18 => (278856759 / 1000000000000 : ℝ)
  | 19 => (146774333 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch001Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (85836263 / 1000000000000 : ℝ)
  | 1 => (47087037 / 500000000000 : ℝ)
  | 2 => (51446831 / 500000000000 : ℝ)
  | 3 => (55997103 / 500000000000 : ℝ)
  | 4 => (3796089 / 31250000000 : ℝ)
  | 5 => (131334697 / 1000000000000 : ℝ)
  | 6 => (70786411 / 500000000000 : ℝ)
  | 7 => (76094129 / 500000000000 : ℝ)
  | 8 => (81590003 / 500000000000 : ℝ)
  | 9 => (87273513 / 500000000000 : ℝ)
  | 10 => (186288247 / 1000000000000 : ℝ)
  | 11 => (77501 / 390625000 : ℝ)
  | 12 => (210888819 / 1000000000000 : ℝ)
  | 13 => (44749169 / 200000000000 : ℝ)
  | 14 => (118486211 / 500000000000 : ℝ)
  | 15 => (250567297 / 1000000000000 : ℝ)
  | 16 => (8266537 / 31250000000 : ℝ)
  | 17 => (6971419 / 25000000000 : ℝ)
  | 18 => (293548667 / 1000000000000 : ℝ)
  | 19 => (30860351 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch001Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((20 : ℝ) + (j.val : ℝ)) / 1600)
      (((20 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch001Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch001Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((20 : ℝ) + (j.val : ℝ)) / 1600)
    (((20 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch001Neg40WeightLower j.val) (hpThetaShiftOneBatch001Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch001Neg40WeightLower, hpThetaShiftOneBatch001Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch001Neg40_integral_bounds :
    (774669821 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (52157969 / 12500000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (20 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch001Lower hpThetaJensenCellsBatch001Upper
    hpThetaShiftOneBatch001Neg40WeightLower hpThetaShiftOneBatch001Neg40WeightUpper hpThetaJensenCellsBatch001_bounds hpThetaShiftOneBatch001Neg40_weight_bounds
  have hl : (774669821 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch001Lower j * hpThetaShiftOneBatch001Neg40WeightLower j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftOneBatch001Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftOneBatch001Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch001Lower j * hpThetaShiftOneBatch001Neg40WeightUpper j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftOneBatch001Neg40WeightUpper j) / 1600) ≤ (52157969 / 12500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftOneBatch001Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (20 : ℝ) / 1600 = 1 / 80 by norm_num,
    show ((20 : ℝ) + 20) / 1600 = (1 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch001Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (78002967 / 1000000000000 : ℝ)
  | 1 => (42992243 / 500000000000 : ℝ)
  | 2 => (47176297 / 500000000000 : ℝ)
  | 3 => (51553449 / 500000000000 : ℝ)
  | 4 => (28061747 / 250000000000 : ℝ)
  | 5 => (60886217 / 500000000000 : ℝ)
  | 6 => (131682789 / 1000000000000 : ℝ)
  | 7 => (70988793 / 500000000000 : ℝ)
  | 8 => (152656341 / 1000000000000 : ℝ)
  | 9 => (81859277 / 500000000000 : ℝ)
  | 10 => (175163703 / 1000000000000 : ℝ)
  | 11 => (149593 / 800000000 : ℝ)
  | 12 => (199200639 / 1000000000000 : ℝ)
  | 13 => (3309239 / 15625000000 : ℝ)
  | 14 => (224762627 / 1000000000000 : ℝ)
  | 15 => (238114021 / 1000000000000 : ℝ)
  | 16 => (251844851 / 1000000000000 : ℝ)
  | 17 => (26595447 / 100000000000 : ℝ)
  | 18 => (280442211 / 1000000000000 : ℝ)
  | 19 => (295307393 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch001Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (85984487 / 1000000000000 : ℝ)
  | 1 => (18870519 / 200000000000 : ℝ)
  | 2 => (103106899 / 1000000000000 : ℝ)
  | 3 => (112246989 / 1000000000000 : ℝ)
  | 4 => (24354487 / 200000000000 : ℝ)
  | 5 => (13168279 / 100000000000 : ℝ)
  | 6 => (141977587 / 1000000000000 : ℝ)
  | 7 => (76328171 / 500000000000 : ℝ)
  | 8 => (32743711 / 200000000000 : ℝ)
  | 9 => (21895463 / 125000000000 : ℝ)
  | 10 => (186991251 / 1000000000000 : ℝ)
  | 11 => (311251 / 1562500000 : ℝ)
  | 12 => (211791297 / 1000000000000 : ℝ)
  | 13 => (56190657 / 250000000000 : ℝ)
  | 14 => (119057011 / 500000000000 : ℝ)
  | 15 => (62961213 / 250000000000 : ℝ)
  | 16 => (265954471 / 1000000000000 : ℝ)
  | 17 => (70110553 / 250000000000 : ℝ)
  | 18 => (147653697 / 500000000000 : ℝ)
  | 19 => (77637329 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch001Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((20 : ℝ) + (j.val : ℝ)) / 1600)
      (((20 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch001Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch001Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((20 : ℝ) + (j.val : ℝ)) / 1600)
    (((20 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch001Neg20WeightLower j.val) (hpThetaShiftOneBatch001Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch001Neg20WeightLower, hpThetaShiftOneBatch001Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch001Neg20_integral_bounds :
    (3889051291 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (1 / 80 : ℝ) ((1 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (2095272993 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (20 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch001Lower hpThetaJensenCellsBatch001Upper
    hpThetaShiftOneBatch001Neg20WeightLower hpThetaShiftOneBatch001Neg20WeightUpper hpThetaJensenCellsBatch001_bounds hpThetaShiftOneBatch001Neg20_weight_bounds
  have hl : (3889051291 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch001Lower j * hpThetaShiftOneBatch001Neg20WeightLower j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftOneBatch001Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftOneBatch001Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch001Lower j * hpThetaShiftOneBatch001Neg20WeightUpper j)
        (hpThetaJensenCellsBatch001Upper j * hpThetaShiftOneBatch001Neg20WeightUpper j) / 1600) ≤ (2095272993 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch001Lower, hpThetaJensenCellsBatch001Upper,
      hpThetaShiftOneBatch001Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (20 : ℝ) / 1600 = 1 / 80 by norm_num,
    show ((20 : ℝ) + 20) / 1600 = (1 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch001Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch001Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch001Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch001Neg20_integral_bounds
end HodgeProofHP
