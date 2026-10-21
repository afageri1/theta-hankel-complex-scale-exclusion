/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch053

/-! Exact signed weight and batch integral certificates, batch 53 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch053Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-18121721383 / 250000000000 : ℝ)
  | 1 => (-9215787111 / 125000000000 : ℝ)
  | 2 => (-18745404457 / 250000000000 : ℝ)
  | 3 => (-15250602267 / 200000000000 : ℝ)
  | 4 => (-15508128349 / 200000000000 : ℝ)
  | 5 => (-1971116869 / 25000000000 : ℝ)
  | 6 => (-16033055491 / 200000000000 : ℝ)
  | 7 => (-81502618289 / 1000000000000 : ℝ)
  | 8 => (-8285686711 / 100000000000 : ℝ)
  | 9 => (-84228195173 / 1000000000000 : ℝ)
  | 10 => (-85616775139 / 1000000000000 : ℝ)
  | 11 => (-87022781093 / 1000000000000 : ℝ)
  | 12 => (-88446388547 / 1000000000000 : ℝ)
  | 13 => (-44943887227 / 500000000000 : ℝ)
  | 14 => (-2854597413 / 31250000000 : ℝ)
  | 15 => (-23206149173 / 250000000000 : ℝ)
  | 16 => (-23580098553 / 250000000000 : ℝ)
  | 17 => (-47917346291 / 500000000000 : ℝ)
  | 18 => (-19473535219 / 200000000000 : ℝ)
  | 19 => (-6182470659 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch053Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-35631611063 / 500000000000 : ℝ)
  | 1 => (-72486885531 / 1000000000000 : ℝ)
  | 2 => (-73726296887 / 1000000000000 : ℝ)
  | 3 => (-74981617827 / 1000000000000 : ℝ)
  | 4 => (-38126505667 / 500000000000 : ℝ)
  | 5 => (-4846290109 / 62500000000 : ℝ)
  | 6 => (-78844674759 / 1000000000000 : ℝ)
  | 7 => (-40082638727 / 500000000000 : ℝ)
  | 8 => (-5093913643 / 62500000000 : ℝ)
  | 9 => (-82856867109 / 1000000000000 : ℝ)
  | 10 => (-21057048793 / 250000000000 : ℝ)
  | 11 => (-42808387569 / 500000000000 : ℝ)
  | 12 => (-21755695273 / 250000000000 : ℝ)
  | 13 => (-44223194273 / 500000000000 : ℝ)
  | 14 => (-89887774453 / 1000000000000 : ℝ)
  | 15 => (-18269423443 / 200000000000 : ℝ)
  | 16 => (-92824596691 / 1000000000000 : ℝ)
  | 17 => (-94320394211 / 1000000000000 : ℝ)
  | 18 => (-95834692581 / 1000000000000 : ℝ)
  | 19 => (-48683838047 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch053Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1060 : ℝ) + (j.val : ℝ)) / 1600)
      (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch053Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch053Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1060 : ℝ) + (j.val : ℝ)) / 1600)
    (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch053Neg100WeightLower j.val) (hpThetaShiftTwoBatch053Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch053Neg100WeightLower, hpThetaShiftTwoBatch053Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch053Neg100_integral_bounds :
    (-76239921 / 8000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-1836808639 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1060 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch053Lower hpThetaJensenCellsBatch053Upper
    hpThetaShiftTwoBatch053Neg100WeightLower hpThetaShiftTwoBatch053Neg100WeightUpper hpThetaJensenCellsBatch053_bounds hpThetaShiftTwoBatch053Neg100_weight_bounds
  have hl : (-76239921 / 8000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch053Lower j * hpThetaShiftTwoBatch053Neg100WeightLower j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftTwoBatch053Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftTwoBatch053Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch053Lower j * hpThetaShiftTwoBatch053Neg100WeightUpper j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftTwoBatch053Neg100WeightUpper j) / 1600) ≤ (-1836808639 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftTwoBatch053Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1060 : ℝ) / 1600 = 53 / 80 by norm_num,
    show ((1060 : ℝ) + 20) / 1600 = (53 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch053Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (10721247947 / 1000000000000 : ℝ)
  | 1 => (85756947 / 8000000000 : ℝ)
  | 2 => (10716549423 / 1000000000000 : ℝ)
  | 3 => (10712016487 / 1000000000000 : ℝ)
  | 4 => (669124669 / 62500000000 : ℝ)
  | 5 => (5349229471 / 500000000000 : ℝ)
  | 6 => (10689383807 / 1000000000000 : ℝ)
  | 7 => (1067874363 / 100000000000 : ℝ)
  | 8 => (426660499 / 40000000000 : ℝ)
  | 9 => (2663166033 / 250000000000 : ℝ)
  | 10 => (2127434423 / 200000000000 : ℝ)
  | 11 => (531000483 / 50000000000 : ℝ)
  | 12 => (2650287431 / 250000000000 : ℝ)
  | 13 => (5290282491 / 500000000000 : ℝ)
  | 14 => (5279113913 / 500000000000 : ℝ)
  | 15 => (263352759 / 25000000000 : ℝ)
  | 16 => (5254092201 / 500000000000 : ℝ)
  | 17 => (10480421477 / 1000000000000 : ℝ)
  | 18 => (522539641 / 50000000000 : ℝ)
  | 19 => (10419269367 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch053Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5360781797 / 500000000000 : ℝ)
  | 1 => (2680311987 / 250000000000 : ℝ)
  | 2 => (1339952297 / 125000000000 : ℝ)
  | 3 => (669784339 / 62500000000 : ℝ)
  | 4 => (1339002061 / 125000000000 : ℝ)
  | 5 => (2141198941 / 200000000000 : ℝ)
  | 6 => (10698458943 / 1000000000000 : ℝ)
  | 7 => (83510811 / 7812500000 : ℝ)
  | 8 => (10678743631 / 1000000000000 : ℝ)
  | 9 => (2666628119 / 250000000000 : ℝ)
  | 10 => (10652664133 / 1000000000000 : ℝ)
  | 11 => (2659293029 / 250000000000 : ℝ)
  | 12 => (10620009661 / 1000000000000 : ℝ)
  | 13 => (424045989 / 40000000000 : ℝ)
  | 14 => (10580564983 / 1000000000000 : ℝ)
  | 15 => (10558227827 / 1000000000000 : ℝ)
  | 16 => (10534110361 / 1000000000000 : ℝ)
  | 17 => (10508184403 / 1000000000000 : ℝ)
  | 18 => (5240210739 / 500000000000 : ℝ)
  | 19 => (10450792821 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch053Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1060 : ℝ) + (j.val : ℝ)) / 1600)
      (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch053Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch053Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1060 : ℝ) + (j.val : ℝ)) / 1600)
    (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch053Neg65WeightLower j.val) (hpThetaShiftTwoBatch053Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch053Neg65WeightLower, hpThetaShiftTwoBatch053Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch053Neg65_integral_bounds :
    (146447257 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (37423903 / 31250000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1060 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch053Lower hpThetaJensenCellsBatch053Upper
    hpThetaShiftTwoBatch053Neg65WeightLower hpThetaShiftTwoBatch053Neg65WeightUpper hpThetaJensenCellsBatch053_bounds hpThetaShiftTwoBatch053Neg65_weight_bounds
  have hl : (146447257 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch053Lower j * hpThetaShiftTwoBatch053Neg65WeightLower j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftTwoBatch053Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftTwoBatch053Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch053Lower j * hpThetaShiftTwoBatch053Neg65WeightUpper j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftTwoBatch053Neg65WeightUpper j) / 1600) ≤ (37423903 / 31250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftTwoBatch053Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1060 : ℝ) / 1600 = 53 / 80 by norm_num,
    show ((1060 : ℝ) + 20) / 1600 = (53 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch053Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (6044180479 / 1000000000000 : ℝ)
  | 1 => (6116276901 / 1000000000000 : ℝ)
  | 2 => (154719017 / 25000000000 : ℝ)
  | 3 => (1565407669 / 250000000000 : ℝ)
  | 4 => (3167442851 / 500000000000 : ℝ)
  | 5 => (400532783 / 62500000000 : ℝ)
  | 6 => (3241272937 / 500000000000 : ℝ)
  | 7 => (102452319 / 15625000000 : ℝ)
  | 8 => (6631730783 / 1000000000000 : ℝ)
  | 9 => (1341378311 / 200000000000 : ℝ)
  | 10 => (423901829 / 62500000000 : ℝ)
  | 11 => (1371668479 / 200000000000 : ℝ)
  | 12 => (6934629381 / 1000000000000 : ℝ)
  | 13 => (219102769 / 31250000000 : ℝ)
  | 14 => (7088318409 / 1000000000000 : ℝ)
  | 15 => (7165717069 / 1000000000000 : ℝ)
  | 16 => (362174141 / 50000000000 : ℝ)
  | 17 => (3660806921 / 500000000000 : ℝ)
  | 18 => (7400108263 / 1000000000000 : ℝ)
  | 19 => (7478964159 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch053Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3058138451 / 500000000000 : ℝ)
  | 1 => (6188760681 / 1000000000000 : ℝ)
  | 2 => (6261630677 / 1000000000000 : ℝ)
  | 3 => (6334885703 / 1000000000000 : ℝ)
  | 4 => (6408524529 / 1000000000000 : ℝ)
  | 5 => (51860367 / 8000000000 : ℝ)
  | 6 => (6556948417 / 1000000000000 : ℝ)
  | 7 => (207241587 / 31250000000 : ℝ)
  | 8 => (1676722889 / 250000000000 : ℝ)
  | 9 => (1356485853 / 200000000000 : ℝ)
  | 10 => (1714585599 / 250000000000 : ℝ)
  | 11 => (3467314691 / 500000000000 : ℝ)
  | 12 => (7011288609 / 1000000000000 : ℝ)
  | 13 => (708831841 / 100000000000 : ℝ)
  | 14 => (716571707 / 100000000000 : ℝ)
  | 15 => (7243482821 / 1000000000000 : ℝ)
  | 16 => (7321613843 / 1000000000000 : ℝ)
  | 17 => (925013533 / 125000000000 : ℝ)
  | 18 => (23371763 / 3125000000 : ℝ)
  | 19 => (7558179551 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch053Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1060 : ℝ) + (j.val : ℝ)) / 1600)
      (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch053Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch053Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1060 : ℝ) + (j.val : ℝ)) / 1600)
    (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch053Neg45WeightLower j.val) (hpThetaShiftTwoBatch053Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch053Neg45WeightLower, hpThetaShiftTwoBatch053Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch053Neg45_integral_bounds :
    (46322859 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (382543221 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1060 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch053Lower hpThetaJensenCellsBatch053Upper
    hpThetaShiftTwoBatch053Neg45WeightLower hpThetaShiftTwoBatch053Neg45WeightUpper hpThetaJensenCellsBatch053_bounds hpThetaShiftTwoBatch053Neg45_weight_bounds
  have hl : (46322859 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch053Lower j * hpThetaShiftTwoBatch053Neg45WeightLower j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftTwoBatch053Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftTwoBatch053Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch053Lower j * hpThetaShiftTwoBatch053Neg45WeightUpper j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftTwoBatch053Neg45WeightUpper j) / 1600) ≤ (382543221 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftTwoBatch053Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1060 : ℝ) / 1600 = 53 / 80 by norm_num,
    show ((1060 : ℝ) + 20) / 1600 = (53 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch053Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3794799079 / 1000000000000 : ℝ)
  | 1 => (-1899961499 / 500000000000 : ℝ)
  | 2 => (-3804893081 / 1000000000000 : ℝ)
  | 3 => (-1904853857 / 500000000000 : ℝ)
  | 4 => (-3814365277 / 1000000000000 : ℝ)
  | 5 => (-763772829 / 200000000000 : ℝ)
  | 6 => (-955800671 / 250000000000 : ℝ)
  | 7 => (-765475851 / 200000000000 : ℝ)
  | 8 => (-3831392213 / 1000000000000 : ℝ)
  | 9 => (-3835239903 / 1000000000000 : ℝ)
  | 10 => (-3838920667 / 1000000000000 : ℝ)
  | 11 => (-1921216419 / 500000000000 : ℝ)
  | 12 => (-3845774743 / 1000000000000 : ℝ)
  | 13 => (-60139761 / 15625000000 : ℝ)
  | 14 => (-1925970517 / 500000000000 : ℝ)
  | 15 => (-3854762041 / 1000000000000 : ℝ)
  | 16 => (-154296241 / 40000000000 : ℝ)
  | 17 => (-1929935641 / 500000000000 : ℝ)
  | 18 => (-1931078049 / 500000000000 : ℝ)
  | 19 => (-966064689 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch053Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3789522927 / 1000000000000 : ℝ)
  | 1 => (-1897399539 / 500000000000 : ℝ)
  | 2 => (-3799922997 / 1000000000000 : ℝ)
  | 3 => (-95122327 / 25000000000 : ℝ)
  | 4 => (-3809707713 / 1000000000000 : ℝ)
  | 5 => (-953591319 / 250000000000 : ℝ)
  | 6 => (-238679009 / 62500000000 : ℝ)
  | 7 => (-3823202683 / 1000000000000 : ℝ)
  | 8 => (-1913689627 / 500000000000 : ℝ)
  | 9 => (-957848053 / 250000000000 : ℝ)
  | 10 => (-1917619951 / 500000000000 : ℝ)
  | 11 => (-1919460333 / 500000000000 : ℝ)
  | 12 => (-3842432837 / 1000000000000 : ℝ)
  | 13 => (-1922887371 / 500000000000 : ℝ)
  | 14 => (-3848944703 / 1000000000000 : ℝ)
  | 15 => (-3851941033 / 1000000000000 : ℝ)
  | 16 => (-96369051 / 25000000000 : ℝ)
  | 17 => (-482175753 / 125000000000 : ℝ)
  | 18 => (-3859871281 / 1000000000000 : ℝ)
  | 19 => (-3862156097 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch053Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1060 : ℝ) + (j.val : ℝ)) / 1600)
      (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch053Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch053Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1060 : ℝ) + (j.val : ℝ)) / 1600)
    (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch053Neg25WeightLower j.val) (hpThetaShiftTwoBatch053Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch053Neg25WeightLower, hpThetaShiftTwoBatch053Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch053Neg25_integral_bounds :
    (-431471107 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-211131439 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1060 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch053Lower hpThetaJensenCellsBatch053Upper
    hpThetaShiftTwoBatch053Neg25WeightLower hpThetaShiftTwoBatch053Neg25WeightUpper hpThetaJensenCellsBatch053_bounds hpThetaShiftTwoBatch053Neg25_weight_bounds
  have hl : (-431471107 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch053Lower j * hpThetaShiftTwoBatch053Neg25WeightLower j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftTwoBatch053Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftTwoBatch053Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch053Lower j * hpThetaShiftTwoBatch053Neg25WeightUpper j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftTwoBatch053Neg25WeightUpper j) / 1600) ≤ (-211131439 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftTwoBatch053Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1060 : ℝ) / 1600 = 53 / 80 by norm_num,
    show ((1060 : ℝ) + 20) / 1600 = (53 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch053Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch053Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch053Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch053Neg25_integral_bounds
end HodgeProofHP
