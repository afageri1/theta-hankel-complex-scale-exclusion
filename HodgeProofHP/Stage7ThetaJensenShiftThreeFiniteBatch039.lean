/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch039

/-! Exact signed weight and batch integral certificates, batch 39 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch039Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (23497831 / 1000000000000 : ℝ)
  | 1 => (11997233 / 500000000000 : ℝ)
  | 2 => (24496697 / 1000000000000 : ℝ)
  | 3 => (12502267 / 500000000000 : ℝ)
  | 4 => (6379497 / 250000000000 : ℝ)
  | 5 => (6509267 / 250000000000 : ℝ)
  | 6 => (26561783 / 1000000000000 : ℝ)
  | 7 => (27092141 / 1000000000000 : ℝ)
  | 8 => (13814073 / 500000000000 : ℝ)
  | 9 => (5633961 / 200000000000 : ℝ)
  | 10 => (28717121 / 1000000000000 : ℝ)
  | 11 => (29270097 / 1000000000000 : ℝ)
  | 12 => (5965747 / 200000000000 : ℝ)
  | 13 => (6078607 / 200000000000 : ℝ)
  | 14 => (7740749 / 250000000000 : ℝ)
  | 15 => (31538617 / 1000000000000 : ℝ)
  | 16 => (6423979 / 200000000000 : ℝ)
  | 17 => (32706823 / 1000000000000 : ℝ)
  | 18 => (33299397 / 1000000000000 : ℝ)
  | 19 => (33897609 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch039Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (23994467 / 1000000000000 : ℝ)
  | 1 => (12248349 / 500000000000 : ℝ)
  | 2 => (5000907 / 200000000000 : ℝ)
  | 3 => (25517989 / 1000000000000 : ℝ)
  | 4 => (26037069 / 1000000000000 : ℝ)
  | 5 => (3320223 / 125000000000 : ℝ)
  | 6 => (13546071 / 500000000000 : ℝ)
  | 7 => (27628147 / 1000000000000 : ℝ)
  | 8 => (14084903 / 500000000000 : ℝ)
  | 9 => (14358561 / 500000000000 : ℝ)
  | 10 => (14635049 / 500000000000 : ℝ)
  | 11 => (233037 / 7812500000 : ℝ)
  | 12 => (7598259 / 250000000000 : ℝ)
  | 13 => (30962997 / 1000000000000 : ℝ)
  | 14 => (15769309 / 500000000000 : ℝ)
  | 15 => (4014987 / 125000000000 : ℝ)
  | 16 => (4088353 / 125000000000 : ℝ)
  | 17 => (16649699 / 500000000000 : ℝ)
  | 18 => (3389761 / 100000000000 : ℝ)
  | 19 => (34501451 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch039Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((780 : ℝ) + (j.val : ℝ)) / 1600)
      (((780 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch039Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch039Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((780 : ℝ) + (j.val : ℝ)) / 1600)
    (((780 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch039Neg100WeightLower j.val) (hpThetaShiftThreeBatch039Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch039Neg100WeightLower, hpThetaShiftThreeBatch039Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch039Neg100_integral_bounds :
    (9187839 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (47594663 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (780 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch039Lower hpThetaJensenCellsBatch039Upper
    hpThetaShiftThreeBatch039Neg100WeightLower hpThetaShiftThreeBatch039Neg100WeightUpper hpThetaJensenCellsBatch039_bounds hpThetaShiftThreeBatch039Neg100_weight_bounds
  have hl : (9187839 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch039Lower j * hpThetaShiftThreeBatch039Neg100WeightLower j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftThreeBatch039Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftThreeBatch039Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch039Lower j * hpThetaShiftThreeBatch039Neg100WeightUpper j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftThreeBatch039Neg100WeightUpper j) / 1600) ≤ (47594663 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftThreeBatch039Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (780 : ℝ) / 1600 = 39 / 80 by norm_num,
    show ((780 : ℝ) + 20) / 1600 = (39 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch039Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-11253809 / 1000000000000 : ℝ)
  | 1 => (-11185861 / 1000000000000 : ℝ)
  | 2 => (-1111469 / 100000000000 : ℝ)
  | 3 => (-11040251 / 1000000000000 : ℝ)
  | 4 => (-5481247 / 500000000000 : ℝ)
  | 5 => (-2720343 / 250000000000 : ℝ)
  | 6 => (-10796837 / 1000000000000 : ℝ)
  | 7 => (-10708841 / 1000000000000 : ℝ)
  | 8 => (-5308667 / 500000000000 : ℝ)
  | 9 => (-10522267 / 1000000000000 : ℝ)
  | 10 => (-1302949 / 125000000000 : ℝ)
  | 11 => (-10321257 / 1000000000000 : ℝ)
  | 12 => (-10215213 / 1000000000000 : ℝ)
  | 13 => (-10105409 / 1000000000000 : ℝ)
  | 14 => (-4995897 / 500000000000 : ℝ)
  | 15 => (-4937159 / 500000000000 : ℝ)
  | 16 => (-9752929 / 1000000000000 : ℝ)
  | 17 => (-385103 / 40000000000 : ℝ)
  | 18 => (-2374551 / 250000000000 : ℝ)
  | 19 => (-9364763 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch039Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-559293 / 50000000000 : ℝ)
  | 1 => (-11114689 / 1000000000000 : ℝ)
  | 2 => (-44161 / 4000000000 : ℝ)
  | 3 => (-10962493 / 1000000000000 : ℝ)
  | 4 => (-10881371 / 1000000000000 : ℝ)
  | 5 => (-2699209 / 250000000000 : ℝ)
  | 6 => (-267721 / 25000000000 : ℝ)
  | 7 => (-10617333 / 1000000000000 : ℝ)
  | 8 => (-5261133 / 500000000000 : ℝ)
  | 9 => (-10423591 / 1000000000000 : ℝ)
  | 10 => (-1290157 / 125000000000 : ℝ)
  | 11 => (-2553803 / 250000000000 : ℝ)
  | 12 => (-157897 / 15625000000 : ℝ)
  | 13 => (-9991793 / 1000000000000 : ℝ)
  | 14 => (-9874317 / 1000000000000 : ℝ)
  | 15 => (-304779 / 31250000000 : ℝ)
  | 16 => (-4813787 / 500000000000 : ℝ)
  | 17 => (-9498203 / 1000000000000 : ℝ)
  | 18 => (-4682381 / 500000000000 : ℝ)
  | 19 => (-5767 / 625000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch039Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((780 : ℝ) + (j.val : ℝ)) / 1600)
      (((780 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch039Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch039Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((780 : ℝ) + (j.val : ℝ)) / 1600)
    (((780 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch039Neg70WeightLower j.val) (hpThetaShiftThreeBatch039Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch039Neg70WeightLower, hpThetaShiftThreeBatch039Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch039Neg70_integral_bounds :
    (-17159503 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-334409 / 20000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (780 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch039Lower hpThetaJensenCellsBatch039Upper
    hpThetaShiftThreeBatch039Neg70WeightLower hpThetaShiftThreeBatch039Neg70WeightUpper hpThetaJensenCellsBatch039_bounds hpThetaShiftThreeBatch039Neg70_weight_bounds
  have hl : (-17159503 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch039Lower j * hpThetaShiftThreeBatch039Neg70WeightLower j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftThreeBatch039Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftThreeBatch039Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch039Lower j * hpThetaShiftThreeBatch039Neg70WeightUpper j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftThreeBatch039Neg70WeightUpper j) / 1600) ≤ (-334409 / 20000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftThreeBatch039Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (780 : ℝ) / 1600 = 39 / 80 by norm_num,
    show ((780 : ℝ) + 20) / 1600 = (39 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch039Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8528319 / 500000000000 : ℝ)
  | 1 => (-8626881 / 500000000000 : ℝ)
  | 2 => (-1745177 / 100000000000 : ℝ)
  | 3 => (-17650653 / 1000000000000 : ℝ)
  | 4 => (-8925201 / 500000000000 : ℝ)
  | 5 => (-4512751 / 250000000000 : ℝ)
  | 6 => (-18252451 / 1000000000000 : ℝ)
  | 7 => (-18454731 / 1000000000000 : ℝ)
  | 8 => (-9328917 / 500000000000 : ℝ)
  | 9 => (-4715437 / 250000000000 : ℝ)
  | 10 => (-9533231 / 500000000000 : ℝ)
  | 11 => (-19271963 / 1000000000000 : ℝ)
  | 12 => (-19478241 / 1000000000000 : ℝ)
  | 13 => (-9842641 / 500000000000 : ℝ)
  | 14 => (-795723 / 40000000000 : ℝ)
  | 15 => (-10050803 / 500000000000 : ℝ)
  | 16 => (-20310863 / 1000000000000 : ℝ)
  | 17 => (-160319 / 7812500000 : ℝ)
  | 18 => (-20731501 / 1000000000000 : ℝ)
  | 19 => (-10471427 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch039Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2107551 / 125000000000 : ℝ)
  | 1 => (-17056637 / 1000000000000 : ℝ)
  | 2 => (-17253761 / 1000000000000 : ℝ)
  | 3 => (-17451769 / 1000000000000 : ℝ)
  | 4 => (-4412663 / 250000000000 : ℝ)
  | 5 => (-17850401 / 1000000000000 : ℝ)
  | 6 => (-18051003 / 1000000000000 : ℝ)
  | 7 => (-365049 / 20000000000 : ℝ)
  | 8 => (-1845473 / 100000000000 : ℝ)
  | 9 => (-18657833 / 1000000000000 : ℝ)
  | 10 => (-18861747 / 1000000000000 : ℝ)
  | 11 => (-19066461 / 1000000000000 : ℝ)
  | 12 => (-9635981 / 500000000000 : ℝ)
  | 13 => (-121739 / 6250000000 : ℝ)
  | 14 => (-19685281 / 1000000000000 : ℝ)
  | 15 => (-9946537 / 500000000000 : ℝ)
  | 16 => (-4020321 / 200000000000 : ℝ)
  | 17 => (-10155431 / 500000000000 : ℝ)
  | 18 => (-20520831 / 1000000000000 : ℝ)
  | 19 => (-41463 / 2000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch039Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((780 : ℝ) + (j.val : ℝ)) / 1600)
      (((780 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch039Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch039Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((780 : ℝ) + (j.val : ℝ)) / 1600)
    (((780 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch039Neg45WeightLower j.val) (hpThetaShiftThreeBatch039Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch039Neg45WeightLower, hpThetaShiftThreeBatch039Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch039Neg45_integral_bounds :
    (-15557873 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-30284037 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (780 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch039Lower hpThetaJensenCellsBatch039Upper
    hpThetaShiftThreeBatch039Neg45WeightLower hpThetaShiftThreeBatch039Neg45WeightUpper hpThetaJensenCellsBatch039_bounds hpThetaShiftThreeBatch039Neg45_weight_bounds
  have hl : (-15557873 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch039Lower j * hpThetaShiftThreeBatch039Neg45WeightLower j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftThreeBatch039Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftThreeBatch039Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch039Lower j * hpThetaShiftThreeBatch039Neg45WeightUpper j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftThreeBatch039Neg45WeightUpper j) / 1600) ≤ (-30284037 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftThreeBatch039Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (780 : ℝ) / 1600 = 39 / 80 by norm_num,
    show ((780 : ℝ) + 20) / 1600 = (39 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch039Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (12157333 / 1000000000000 : ℝ)
  | 1 => (604617 / 50000000000 : ℝ)
  | 2 => (12025763 / 1000000000000 : ℝ)
  | 3 => (1195759 / 100000000000 : ℝ)
  | 4 => (11887807 / 1000000000000 : ℝ)
  | 5 => (5908201 / 500000000000 : ℝ)
  | 6 => (5871681 / 500000000000 : ℝ)
  | 7 => (11668673 / 1000000000000 : ℝ)
  | 8 => (5796161 / 500000000000 : ℝ)
  | 9 => (2302859 / 200000000000 : ℝ)
  | 10 => (571729 / 50000000000 : ℝ)
  | 11 => (11353163 / 1000000000000 : ℝ)
  | 12 => (1127003 / 100000000000 : ℝ)
  | 13 => (11185169 / 1000000000000 : ℝ)
  | 14 => (5549283 / 500000000000 : ℝ)
  | 15 => (344069 / 31250000000 : ℝ)
  | 16 => (136501 / 12500000000 : ℝ)
  | 17 => (10828171 / 1000000000000 : ℝ)
  | 18 => (2146893 / 200000000000 : ℝ)
  | 19 => (212779 / 20000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch039Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (6110379 / 500000000000 : ℝ)
  | 1 => (6078667 / 500000000000 : ℝ)
  | 2 => (12092341 / 1000000000000 : ℝ)
  | 3 => (3006441 / 250000000000 : ℝ)
  | 4 => (11957591 / 1000000000000 : ℝ)
  | 5 => (185747 / 15625000000 : ℝ)
  | 6 => (11816403 / 1000000000000 : ℝ)
  | 7 => (11743363 / 1000000000000 : ℝ)
  | 8 => (5834337 / 500000000000 : ℝ)
  | 9 => (11592323 / 1000000000000 : ℝ)
  | 10 => (1439287 / 125000000000 : ℝ)
  | 11 => (11434581 / 1000000000000 : ℝ)
  | 12 => (2838291 / 250000000000 : ℝ)
  | 13 => (11270031 / 1000000000000 : ℝ)
  | 14 => (1118517 / 100000000000 : ℝ)
  | 15 => (11098567 / 1000000000000 : ℝ)
  | 16 => (11010209 / 1000000000000 : ℝ)
  | 17 => (10920081 / 1000000000000 : ℝ)
  | 18 => (2707043 / 250000000000 : ℝ)
  | 19 => (5367233 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch039Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((780 : ℝ) + (j.val : ℝ)) / 1600)
      (((780 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch039Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch039Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((780 : ℝ) + (j.val : ℝ)) / 1600)
    (((780 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch039Neg25WeightLower j.val) (hpThetaShiftThreeBatch039Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch039Neg25WeightLower, hpThetaShiftThreeBatch039Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch039Neg25_integral_bounds :
    (18546907 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (18980147 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (780 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch039Lower hpThetaJensenCellsBatch039Upper
    hpThetaShiftThreeBatch039Neg25WeightLower hpThetaShiftThreeBatch039Neg25WeightUpper hpThetaJensenCellsBatch039_bounds hpThetaShiftThreeBatch039Neg25_weight_bounds
  have hl : (18546907 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch039Lower j * hpThetaShiftThreeBatch039Neg25WeightLower j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftThreeBatch039Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftThreeBatch039Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch039Lower j * hpThetaShiftThreeBatch039Neg25WeightUpper j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftThreeBatch039Neg25WeightUpper j) / 1600) ≤ (18980147 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftThreeBatch039Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (780 : ℝ) / 1600 = 39 / 80 by norm_num,
    show ((780 : ℝ) + 20) / 1600 = (39 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch039Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch039Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch039Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch039Neg25_integral_bounds
end HodgeProofHP
