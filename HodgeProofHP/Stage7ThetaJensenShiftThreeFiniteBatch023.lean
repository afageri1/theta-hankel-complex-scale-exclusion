/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch023

/-! Exact signed weight and batch integral certificates, batch 23 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch023Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-58809 / 200000000000 : ℝ)
  | 1 => (-307237 / 1000000000000 : ℝ)
  | 2 => (-501 / 1562500000 : ℝ)
  | 3 => (-334257 / 1000000000000 : ℝ)
  | 4 => (-348087 / 1000000000000 : ℝ)
  | 5 => (-362133 / 1000000000000 : ℝ)
  | 6 => (-94099 / 250000000000 : ℝ)
  | 7 => (-3127 / 8000000000 : ℝ)
  | 8 => (-101393 / 250000000000 : ℝ)
  | 9 => (-52561 / 125000000000 : ℝ)
  | 10 => (-697 / 1600000000 : ℝ)
  | 11 => (-450981 / 1000000000000 : ℝ)
  | 12 => (-466559 / 1000000000000 : ℝ)
  | 13 => (-482359 / 1000000000000 : ℝ)
  | 14 => (-249191 / 500000000000 : ℝ)
  | 15 => (-128657 / 250000000000 : ℝ)
  | 16 => (-531099 / 1000000000000 : ℝ)
  | 17 => (-273897 / 500000000000 : ℝ)
  | 18 => (-282357 / 500000000000 : ℝ)
  | 19 => (-581859 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch023Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-35133 / 125000000000 : ℝ)
  | 1 => (-73511 / 250000000000 : ℝ)
  | 2 => (-76809 / 250000000000 : ℝ)
  | 3 => (-320639 / 1000000000000 : ℝ)
  | 4 => (-20891 / 62500000000 : ℝ)
  | 5 => (-174043 / 500000000000 : ℝ)
  | 6 => (-90533 / 250000000000 : ℝ)
  | 7 => (-75279 / 200000000000 : ℝ)
  | 8 => (-195437 / 500000000000 : ℝ)
  | 9 => (-405571 / 1000000000000 : ℝ)
  | 10 => (-420487 / 1000000000000 : ℝ)
  | 11 => (-54453 / 125000000000 : ℝ)
  | 12 => (-22549 / 50000000000 : ℝ)
  | 13 => (-233279 / 500000000000 : ℝ)
  | 14 => (-241179 / 500000000000 : ℝ)
  | 15 => (-498381 / 1000000000000 : ℝ)
  | 16 => (-514627 / 1000000000000 : ℝ)
  | 17 => (-265549 / 500000000000 : ℝ)
  | 18 => (-547793 / 1000000000000 : ℝ)
  | 19 => (-564713 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch023Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((460 : ℝ) + (j.val : ℝ)) / 1600)
      (((460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch023Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch023Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((460 : ℝ) + (j.val : ℝ)) / 1600)
    (((460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch023Neg100WeightLower j.val) (hpThetaShiftThreeBatch023Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch023Neg100WeightLower, hpThetaShiftThreeBatch023Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch023Neg100_integral_bounds :
    (-826019 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-3934451 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch023Lower hpThetaJensenCellsBatch023Upper
    hpThetaShiftThreeBatch023Neg100WeightLower hpThetaShiftThreeBatch023Neg100WeightUpper hpThetaJensenCellsBatch023_bounds hpThetaShiftThreeBatch023Neg100_weight_bounds
  have hl : (-826019 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch023Lower j * hpThetaShiftThreeBatch023Neg100WeightLower j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftThreeBatch023Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftThreeBatch023Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch023Lower j * hpThetaShiftThreeBatch023Neg100WeightUpper j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftThreeBatch023Neg100WeightUpper j) / 1600) ≤ (-3934451 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftThreeBatch023Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (460 : ℝ) / 1600 = 23 / 80 by norm_num,
    show ((460 : ℝ) + 20) / 1600 = (23 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch023Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (578683 / 1000000000000 : ℝ)
  | 1 => (574799 / 1000000000000 : ℝ)
  | 2 => (71341 / 125000000000 : ℝ)
  | 3 => (141617 / 250000000000 : ℝ)
  | 4 => (281007 / 500000000000 : ℝ)
  | 5 => (278683 / 500000000000 : ℝ)
  | 6 => (552519 / 1000000000000 : ℝ)
  | 7 => (547471 / 1000000000000 : ℝ)
  | 8 => (542219 / 1000000000000 : ℝ)
  | 9 => (13419 / 25000000000 : ℝ)
  | 10 => (531093 / 1000000000000 : ℝ)
  | 11 => (525213 / 1000000000000 : ℝ)
  | 12 => (259559 / 500000000000 : ℝ)
  | 13 => (102561 / 200000000000 : ℝ)
  | 14 => (506271 / 1000000000000 : ℝ)
  | 15 => (249757 / 500000000000 : ℝ)
  | 16 => (49253 / 100000000000 : ℝ)
  | 17 => (485317 / 1000000000000 : ℝ)
  | 18 => (477871 / 1000000000000 : ℝ)
  | 19 => (470191 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch023Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (582383 / 1000000000000 : ℝ)
  | 1 => (144671 / 250000000000 : ℝ)
  | 2 => (1437 / 2500000000 : ℝ)
  | 3 => (570729 / 1000000000000 : ℝ)
  | 4 => (566469 / 1000000000000 : ℝ)
  | 5 => (112403 / 200000000000 : ℝ)
  | 6 => (557367 / 1000000000000 : ℝ)
  | 7 => (13813 / 25000000000 : ℝ)
  | 8 => (34217 / 62500000000 : ℝ)
  | 9 => (27111 / 50000000000 : ℝ)
  | 10 => (536761 / 1000000000000 : ℝ)
  | 11 => (265547 / 500000000000 : ℝ)
  | 12 => (262607 / 500000000000 : ℝ)
  | 13 => (519119 / 1000000000000 : ℝ)
  | 14 => (256403 / 500000000000 : ℝ)
  | 15 => (15821 / 31250000000 : ℝ)
  | 16 => (99903 / 200000000000 : ℝ)
  | 17 => (492531 / 1000000000000 : ℝ)
  | 18 => (242659 / 500000000000 : ℝ)
  | 19 => (29867 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch023Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((460 : ℝ) + (j.val : ℝ)) / 1600)
      (((460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch023Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch023Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((460 : ℝ) + (j.val : ℝ)) / 1600)
    (((460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch023Neg70WeightLower j.val) (hpThetaShiftThreeBatch023Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch023Neg70WeightLower, hpThetaShiftThreeBatch023Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch023Neg70_integral_bounds :
    (5038739 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (5158127 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch023Lower hpThetaJensenCellsBatch023Upper
    hpThetaShiftThreeBatch023Neg70WeightLower hpThetaShiftThreeBatch023Neg70WeightUpper hpThetaJensenCellsBatch023_bounds hpThetaShiftThreeBatch023Neg70_weight_bounds
  have hl : (5038739 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch023Lower j * hpThetaShiftThreeBatch023Neg70WeightLower j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftThreeBatch023Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftThreeBatch023Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch023Lower j * hpThetaShiftThreeBatch023Neg70WeightUpper j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftThreeBatch023Neg70WeightUpper j) / 1600) ≤ (5158127 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftThreeBatch023Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (460 : ℝ) / 1600 = 23 / 80 by norm_num,
    show ((460 : ℝ) + 20) / 1600 = (23 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch023Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (843249 / 500000000000 : ℝ)
  | 1 => (849173 / 500000000000 : ℝ)
  | 2 => (1710169 / 1000000000000 : ℝ)
  | 3 => (344393 / 200000000000 : ℝ)
  | 4 => (1733731 / 1000000000000 : ℝ)
  | 5 => (1745467 / 1000000000000 : ℝ)
  | 6 => (109823 / 62500000000 : ℝ)
  | 7 => (353767 / 200000000000 : ℝ)
  | 8 => (1780463 / 1000000000000 : ℝ)
  | 9 => (448013 / 250000000000 : ℝ)
  | 10 => (901799 / 500000000000 : ℝ)
  | 11 => (18151 / 10000000000 : ℝ)
  | 12 => (365311 / 200000000000 : ℝ)
  | 13 => (1837961 / 1000000000000 : ℝ)
  | 14 => (462329 / 250000000000 : ℝ)
  | 15 => (1860617 / 1000000000000 : ℝ)
  | 16 => (1871861 / 1000000000000 : ℝ)
  | 17 => (1883047 / 1000000000000 : ℝ)
  | 18 => (1894171 / 1000000000000 : ℝ)
  | 19 => (119077 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch023Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1698347 / 1000000000000 : ℝ)
  | 1 => (171017 / 100000000000 : ℝ)
  | 2 => (860983 / 500000000000 : ℝ)
  | 3 => (433433 / 250000000000 : ℝ)
  | 4 => (436367 / 250000000000 : ℝ)
  | 5 => (1757169 / 1000000000000 : ℝ)
  | 6 => (442209 / 250000000000 : ℝ)
  | 7 => (111279 / 62500000000 : ℝ)
  | 8 => (1792053 / 1000000000000 : ℝ)
  | 9 => (1803599 / 1000000000000 : ℝ)
  | 10 => (1815101 / 1000000000000 : ℝ)
  | 11 => (456639 / 250000000000 : ℝ)
  | 12 => (918981 / 500000000000 : ℝ)
  | 13 => (1849317 / 1000000000000 : ℝ)
  | 14 => (930309 / 500000000000 : ℝ)
  | 15 => (935931 / 500000000000 : ℝ)
  | 16 => (235381 / 125000000000 : ℝ)
  | 17 => (473543 / 250000000000 : ℝ)
  | 18 => (1905233 / 1000000000000 : ℝ)
  | 19 => (479057 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch023Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((460 : ℝ) + (j.val : ℝ)) / 1600)
      (((460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch023Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch023Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((460 : ℝ) + (j.val : ℝ)) / 1600)
    (((460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch023Neg45WeightLower j.val) (hpThetaShiftThreeBatch023Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch023Neg45WeightLower, hpThetaShiftThreeBatch023Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch023Neg45_integral_bounds :
    (8516899 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (1085407 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch023Lower hpThetaJensenCellsBatch023Upper
    hpThetaShiftThreeBatch023Neg45WeightLower hpThetaShiftThreeBatch023Neg45WeightUpper hpThetaJensenCellsBatch023_bounds hpThetaShiftThreeBatch023Neg45_weight_bounds
  have hl : (8516899 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch023Lower j * hpThetaShiftThreeBatch023Neg45WeightLower j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftThreeBatch023Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftThreeBatch023Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch023Lower j * hpThetaShiftThreeBatch023Neg45WeightUpper j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftThreeBatch023Neg45WeightUpper j) / 1600) ≤ (1085407 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftThreeBatch023Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (460 : ℝ) / 1600 = 23 / 80 by norm_num,
    show ((460 : ℝ) + 20) / 1600 = (23 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch023Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (285387 / 100000000000 : ℝ)
  | 1 => (721031 / 250000000000 : ℝ)
  | 2 => (291459 / 100000000000 : ℝ)
  | 3 => (294527 / 100000000000 : ℝ)
  | 4 => (2976163 / 1000000000000 : ℝ)
  | 5 => (300727 / 100000000000 : ℝ)
  | 6 => (3038591 / 1000000000000 : ℝ)
  | 7 => (1535063 / 500000000000 : ℝ)
  | 8 => (775469 / 250000000000 : ℝ)
  | 9 => (39173 / 12500000000 : ℝ)
  | 10 => (1583009 / 500000000000 : ℝ)
  | 11 => (799603 / 250000000000 : ℝ)
  | 12 => (161551 / 50000000000 : ℝ)
  | 13 => (3263843 / 1000000000000 : ℝ)
  | 14 => (3296881 / 1000000000000 : ℝ)
  | 15 => (666027 / 200000000000 : ℝ)
  | 16 => (3363603 / 1000000000000 : ℝ)
  | 17 => (1698643 / 500000000000 : ℝ)
  | 18 => (686237 / 200000000000 : ℝ)
  | 19 => (3465299 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch023Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (23073 / 8000000000 : ℝ)
  | 1 => (2914591 / 1000000000000 : ℝ)
  | 2 => (2945271 / 1000000000000 : ℝ)
  | 3 => (744041 / 250000000000 : ℝ)
  | 4 => (3007271 / 1000000000000 : ℝ)
  | 5 => (23739 / 7812500000 : ℝ)
  | 6 => (3070127 / 1000000000000 : ℝ)
  | 7 => (3101877 / 1000000000000 : ℝ)
  | 8 => (3133841 / 1000000000000 : ℝ)
  | 9 => (3166019 / 1000000000000 : ℝ)
  | 10 => (3198413 / 1000000000000 : ℝ)
  | 11 => (3231021 / 1000000000000 : ℝ)
  | 12 => (815961 / 250000000000 : ℝ)
  | 13 => (1648441 / 500000000000 : ℝ)
  | 14 => (416267 / 125000000000 : ℝ)
  | 15 => (840901 / 250000000000 : ℝ)
  | 16 => (3397287 / 1000000000000 : ℝ)
  | 17 => (1715593 / 500000000000 : ℝ)
  | 18 => (34653 / 10000000000 : ℝ)
  | 19 => (874907 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch023Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((460 : ℝ) + (j.val : ℝ)) / 1600)
      (((460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch023Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch023Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((460 : ℝ) + (j.val : ℝ)) / 1600)
    (((460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch023Neg25WeightLower j.val) (hpThetaShiftThreeBatch023Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch023Neg25WeightLower, hpThetaShiftThreeBatch023Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch023Neg25_integral_bounds :
    (1867229 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (30575559 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch023Lower hpThetaJensenCellsBatch023Upper
    hpThetaShiftThreeBatch023Neg25WeightLower hpThetaShiftThreeBatch023Neg25WeightUpper hpThetaJensenCellsBatch023_bounds hpThetaShiftThreeBatch023Neg25_weight_bounds
  have hl : (1867229 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch023Lower j * hpThetaShiftThreeBatch023Neg25WeightLower j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftThreeBatch023Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftThreeBatch023Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch023Lower j * hpThetaShiftThreeBatch023Neg25WeightUpper j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftThreeBatch023Neg25WeightUpper j) / 1600) ≤ (30575559 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftThreeBatch023Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (460 : ℝ) / 1600 = 23 / 80 by norm_num,
    show ((460 : ℝ) + 20) / 1600 = (23 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch023Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch023Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch023Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch023Neg25_integral_bounds
end HodgeProofHP
