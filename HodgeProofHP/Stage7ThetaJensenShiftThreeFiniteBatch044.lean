/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch044

/-! Exact signed weight and batch integral certificates, batch 44 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch044Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (24137391 / 250000000000 : ℝ)
  | 1 => (24344293 / 250000000000 : ℝ)
  | 2 => (98201037 / 1000000000000 : ℝ)
  | 3 => (49510439 / 500000000000 : ℝ)
  | 4 => (12479551 / 125000000000 : ℝ)
  | 5 => (100647333 / 1000000000000 : ℝ)
  | 6 => (20290671 / 200000000000 : ℝ)
  | 7 => (102254167 / 1000000000000 : ℝ)
  | 8 => (51524729 / 500000000000 : ℝ)
  | 9 => (103838911 / 1000000000000 : ℝ)
  | 10 => (523111 / 5000000000 : ℝ)
  | 11 => (52699497 / 500000000000 : ℝ)
  | 12 => (26542239 / 250000000000 : ℝ)
  | 13 => (53465871 / 500000000000 : ℝ)
  | 14 => (107687 / 1000000000 : ℝ)
  | 15 => (108434373 / 1000000000000 : ℝ)
  | 16 => (21834699 / 200000000000 : ℝ)
  | 17 => (54951997 / 500000000000 : ℝ)
  | 18 => (110625491 / 1000000000000 : ℝ)
  | 19 => (111337599 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch044Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (97377173 / 1000000000000 : ℝ)
  | 1 => (49100519 / 500000000000 : ℝ)
  | 2 => (99020879 / 1000000000000 : ℝ)
  | 3 => (99836409 / 1000000000000 : ℝ)
  | 4 => (50323667 / 500000000000 : ℝ)
  | 5 => (25363339 / 250000000000 : ℝ)
  | 6 => (12781771 / 125000000000 : ℝ)
  | 7 => (103049459 / 1000000000000 : ℝ)
  | 8 => (1622483 / 15625000000 : ℝ)
  | 9 => (104622201 / 1000000000000 : ℝ)
  | 10 => (21079799 / 200000000000 : ℝ)
  | 11 => (106168957 / 1000000000000 : ℝ)
  | 12 => (106931743 / 1000000000000 : ℝ)
  | 13 => (107687001 / 1000000000000 : ℝ)
  | 14 => (54217187 / 500000000000 : ℝ)
  | 15 => (13646687 / 125000000000 : ℝ)
  | 16 => (21980799 / 200000000000 : ℝ)
  | 17 => (27656373 / 250000000000 : ℝ)
  | 18 => (34793 / 312500000 : ℝ)
  | 19 => (56019963 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch044Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((880 : ℝ) + (j.val : ℝ)) / 1600)
      (((880 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch044Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch044Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((880 : ℝ) + (j.val : ℝ)) / 1600)
    (((880 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch044Neg100WeightLower j.val) (hpThetaShiftThreeBatch044Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch044Neg100WeightLower, hpThetaShiftThreeBatch044Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch044Neg100_integral_bounds :
    (74245529 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (38065199 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (880 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch044Lower hpThetaJensenCellsBatch044Upper
    hpThetaShiftThreeBatch044Neg100WeightLower hpThetaShiftThreeBatch044Neg100WeightUpper hpThetaJensenCellsBatch044_bounds hpThetaShiftThreeBatch044Neg100_weight_bounds
  have hl : (74245529 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch044Lower j * hpThetaShiftThreeBatch044Neg100WeightLower j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftThreeBatch044Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftThreeBatch044Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch044Lower j * hpThetaShiftThreeBatch044Neg100WeightUpper j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftThreeBatch044Neg100WeightUpper j) / 1600) ≤ (38065199 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftThreeBatch044Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (880 : ℝ) / 1600 = 44 / 80 by norm_num,
    show ((880 : ℝ) + 20) / 1600 = (44 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch044Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (20252931 / 1000000000000 : ℝ)
  | 1 => (2092007 / 100000000000 : ℝ)
  | 2 => (10798139 / 500000000000 : ℝ)
  | 3 => (22281617 / 1000000000000 : ℝ)
  | 4 => (11488073 / 500000000000 : ℝ)
  | 5 => (947197 / 40000000000 : ℝ)
  | 6 => (24393011 / 1000000000000 : ℝ)
  | 7 => (3139433 / 125000000000 : ℝ)
  | 8 => (25847341 / 1000000000000 : ℝ)
  | 9 => (13294351 / 500000000000 : ℝ)
  | 10 => (27339603 / 1000000000000 : ℝ)
  | 11 => (281001 / 10000000000 : ℝ)
  | 12 => (7217563 / 250000000000 : ℝ)
  | 13 => (14825057 / 500000000000 : ℝ)
  | 14 => (30439741 / 1000000000000 : ℝ)
  | 15 => (3123919 / 100000000000 : ℝ)
  | 16 => (16024257 / 500000000000 : ℝ)
  | 17 => (32867769 / 1000000000000 : ℝ)
  | 18 => (2106063 / 62500000000 : ℝ)
  | 19 => (8634071 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch044Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (20920071 / 1000000000000 : ℝ)
  | 1 => (21596279 / 1000000000000 : ℝ)
  | 2 => (11140809 / 500000000000 : ℝ)
  | 3 => (22976147 / 1000000000000 : ℝ)
  | 4 => (11839963 / 500000000000 : ℝ)
  | 5 => (6098253 / 250000000000 : ℝ)
  | 6 => (5023093 / 200000000000 : ℝ)
  | 7 => (12923671 / 500000000000 : ℝ)
  | 8 => (26588703 / 1000000000000 : ℝ)
  | 9 => (6834901 / 250000000000 : ℝ)
  | 10 => (28100101 / 1000000000000 : ℝ)
  | 11 => (28870253 / 1000000000000 : ℝ)
  | 12 => (5930023 / 200000000000 : ℝ)
  | 13 => (15219871 / 500000000000 : ℝ)
  | 14 => (31239191 / 1000000000000 : ℝ)
  | 15 => (6409703 / 200000000000 : ℝ)
  | 16 => (3286777 / 100000000000 : ℝ)
  | 17 => (33697009 / 1000000000000 : ℝ)
  | 18 => (6907257 / 200000000000 : ℝ)
  | 19 => (35385651 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch044Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((880 : ℝ) + (j.val : ℝ)) / 1600)
      (((880 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch044Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch044Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((880 : ℝ) + (j.val : ℝ)) / 1600)
    (((880 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch044Neg70WeightLower j.val) (hpThetaShiftThreeBatch044Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch044Neg70WeightLower, hpThetaShiftThreeBatch044Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch044Neg70_integral_bounds :
    (9611583 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (20113421 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (880 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch044Lower hpThetaJensenCellsBatch044Upper
    hpThetaShiftThreeBatch044Neg70WeightLower hpThetaShiftThreeBatch044Neg70WeightUpper hpThetaJensenCellsBatch044_bounds hpThetaShiftThreeBatch044Neg70_weight_bounds
  have hl : (9611583 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch044Lower j * hpThetaShiftThreeBatch044Neg70WeightLower j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftThreeBatch044Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftThreeBatch044Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch044Lower j * hpThetaShiftThreeBatch044Neg70WeightUpper j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftThreeBatch044Neg70WeightUpper j) / 1600) ≤ (20113421 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftThreeBatch044Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (880 : ℝ) / 1600 = 44 / 80 by norm_num,
    show ((880 : ℝ) + 20) / 1600 = (44 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch044Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-38480941 / 1000000000000 : ℝ)
  | 1 => (-77343 / 2000000000 : ℝ)
  | 2 => (-9715111 / 250000000000 : ℝ)
  | 3 => (-3904773 / 100000000000 : ℝ)
  | 4 => (-3923331 / 100000000000 : ℝ)
  | 5 => (-19708571 / 500000000000 : ℝ)
  | 6 => (-19799589 / 500000000000 : ℝ)
  | 7 => (-39779373 / 1000000000000 : ℝ)
  | 8 => (-499471 / 12500000000 : ℝ)
  | 9 => (-10033513 / 250000000000 : ℝ)
  | 10 => (-20154221 / 500000000000 : ℝ)
  | 11 => (-50601 / 1250000000 : ℝ)
  | 12 => (-1016277 / 25000000000 : ℝ)
  | 13 => (-1275601 / 31250000000 : ℝ)
  | 14 => (-20492603 / 500000000000 : ℝ)
  | 15 => (-5143619 / 125000000000 : ℝ)
  | 16 => (-2065521 / 50000000000 : ℝ)
  | 17 => (-1036739 / 25000000000 : ℝ)
  | 18 => (-41626319 / 1000000000000 : ℝ)
  | 19 => (-20890323 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch044Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-38288809 / 1000000000000 : ℝ)
  | 1 => (-1924047 / 50000000000 : ℝ)
  | 2 => (-38671499 / 1000000000000 : ℝ)
  | 3 => (-38860443 / 1000000000000 : ℝ)
  | 4 => (-39047729 / 1000000000000 : ℝ)
  | 5 => (-39233309 / 1000000000000 : ℝ)
  | 6 => (-39417141 / 1000000000000 : ℝ)
  | 7 => (-39599177 / 1000000000000 : ℝ)
  | 8 => (-9944843 / 250000000000 : ℝ)
  | 9 => (-39957679 / 1000000000000 : ℝ)
  | 10 => (-40134051 / 1000000000000 : ℝ)
  | 11 => (-40308441 / 1000000000000 : ℝ)
  | 12 => (-40480799 / 1000000000000 : ℝ)
  | 13 => (-40651079 / 1000000000000 : ℝ)
  | 14 => (-40819231 / 1000000000000 : ℝ)
  | 15 => (-8197041 / 200000000000 : ℝ)
  | 16 => (-41148951 / 1000000000000 : ℝ)
  | 17 => (-41310419 / 1000000000000 : ℝ)
  | 18 => (-41469559 / 1000000000000 : ℝ)
  | 19 => (-20813159 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch044Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((880 : ℝ) + (j.val : ℝ)) / 1600)
      (((880 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch044Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch044Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((880 : ℝ) + (j.val : ℝ)) / 1600)
    (((880 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch044Neg45WeightLower j.val) (hpThetaShiftThreeBatch044Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch044Neg45WeightLower, hpThetaShiftThreeBatch044Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch044Neg45_integral_bounds :
    (-29192493 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-7139339 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (880 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch044Lower hpThetaJensenCellsBatch044Upper
    hpThetaShiftThreeBatch044Neg45WeightLower hpThetaShiftThreeBatch044Neg45WeightUpper hpThetaJensenCellsBatch044_bounds hpThetaShiftThreeBatch044Neg45_weight_bounds
  have hl : (-29192493 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch044Lower j * hpThetaShiftThreeBatch044Neg45WeightLower j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftThreeBatch044Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftThreeBatch044Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch044Lower j * hpThetaShiftThreeBatch044Neg45WeightUpper j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftThreeBatch044Neg45WeightUpper j) / 1600) ≤ (-7139339 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftThreeBatch044Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (880 : ℝ) / 1600 = 44 / 80 by norm_num,
    show ((880 : ℝ) + 20) / 1600 = (44 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch044Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4370517 / 1000000000000 : ℝ)
  | 1 => (-582641 / 125000000000 : ℝ)
  | 2 => (-198187 / 40000000000 : ℝ)
  | 3 => (-5251171 / 1000000000000 : ℝ)
  | 4 => (-5550627 / 1000000000000 : ℝ)
  | 5 => (-45727 / 7812500000 : ℝ)
  | 6 => (-615847 / 100000000000 : ℝ)
  | 7 => (-3233441 / 500000000000 : ℝ)
  | 8 => (-6778303 / 1000000000000 : ℝ)
  | 9 => (-3546373 / 500000000000 : ℝ)
  | 10 => (-7410223 / 1000000000000 : ℝ)
  | 11 => (-3865373 / 500000000000 : ℝ)
  | 12 => (-4027163 / 500000000000 : ℝ)
  | 13 => (-523811 / 62500000000 : ℝ)
  | 14 => (-8710707 / 1000000000000 : ℝ)
  | 15 => (-9043531 / 1000000000000 : ℝ)
  | 16 => (-9379459 / 1000000000000 : ℝ)
  | 17 => (-1214813 / 125000000000 : ℝ)
  | 18 => (-2515169 / 250000000000 : ℝ)
  | 19 => (-10405987 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch044Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4082827 / 1000000000000 : ℝ)
  | 1 => (-1092629 / 250000000000 : ℝ)
  | 2 => (-4661127 / 1000000000000 : ℝ)
  | 3 => (-2477337 / 500000000000 : ℝ)
  | 4 => (-525117 / 100000000000 : ℝ)
  | 5 => (-2775313 / 500000000000 : ℝ)
  | 6 => (-1170611 / 200000000000 : ℝ)
  | 7 => (-6158469 / 1000000000000 : ℝ)
  | 8 => (-6466881 / 1000000000000 : ℝ)
  | 9 => (-3389151 / 500000000000 : ℝ)
  | 10 => (-1418549 / 200000000000 : ℝ)
  | 11 => (-3705111 / 500000000000 : ℝ)
  | 12 => (-1546149 / 200000000000 : ℝ)
  | 13 => (-322173 / 40000000000 : ℝ)
  | 14 => (-335239 / 40000000000 : ℝ)
  | 15 => (-4355353 / 500000000000 : ℝ)
  | 16 => (-904353 / 100000000000 : ℝ)
  | 17 => (-4689729 / 500000000000 : ℝ)
  | 18 => (-9718503 / 1000000000000 : ℝ)
  | 19 => (-402427 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch044Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((880 : ℝ) + (j.val : ℝ)) / 1600)
      (((880 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch044Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch044Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((880 : ℝ) + (j.val : ℝ)) / 1600)
    (((880 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch044Neg25WeightLower j.val) (hpThetaShiftThreeBatch044Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch044Neg25WeightLower, hpThetaShiftThreeBatch044Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch044Neg25_integral_bounds :
    (-5242451 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-4925481 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (880 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch044Lower hpThetaJensenCellsBatch044Upper
    hpThetaShiftThreeBatch044Neg25WeightLower hpThetaShiftThreeBatch044Neg25WeightUpper hpThetaJensenCellsBatch044_bounds hpThetaShiftThreeBatch044Neg25_weight_bounds
  have hl : (-5242451 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch044Lower j * hpThetaShiftThreeBatch044Neg25WeightLower j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftThreeBatch044Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftThreeBatch044Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch044Lower j * hpThetaShiftThreeBatch044Neg25WeightUpper j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftThreeBatch044Neg25WeightUpper j) / 1600) ≤ (-4925481 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftThreeBatch044Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (880 : ℝ) / 1600 = 44 / 80 by norm_num,
    show ((880 : ℝ) + 20) / 1600 = (44 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch044Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch044Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch044Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch044Neg25_integral_bounds
end HodgeProofHP
