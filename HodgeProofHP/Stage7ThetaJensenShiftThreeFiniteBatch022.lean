/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch022

/-! Exact signed weight and batch integral certificates, batch 22 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch022Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-72831 / 1000000000000 : ℝ)
  | 1 => (-1641 / 20000000000 : ℝ)
  | 2 => (-45727 / 500000000000 : ℝ)
  | 3 => (-50523 / 500000000000 : ℝ)
  | 4 => (-4433 / 40000000000 : ℝ)
  | 5 => (-120793 / 1000000000000 : ℝ)
  | 6 => (-130953 / 1000000000000 : ℝ)
  | 7 => (-70653 / 500000000000 : ℝ)
  | 8 => (-37963 / 250000000000 : ℝ)
  | 9 => (-81297 / 500000000000 : ℝ)
  | 10 => (-173533 / 1000000000000 : ℝ)
  | 11 => (-18467 / 100000000000 : ℝ)
  | 12 => (-196007 / 1000000000000 : ℝ)
  | 13 => (-25943 / 125000000000 : ℝ)
  | 14 => (-54821 / 250000000000 : ℝ)
  | 15 => (-57807 / 250000000000 : ℝ)
  | 16 => (-243377 / 1000000000000 : ℝ)
  | 17 => (-63933 / 250000000000 : ℝ)
  | 18 => (-134147 / 500000000000 : ℝ)
  | 19 => (-56213 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch022Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-31897 / 500000000000 : ℝ)
  | 1 => (-7283 / 100000000000 : ℝ)
  | 2 => (-82049 / 1000000000000 : ℝ)
  | 3 => (-91453 / 1000000000000 : ℝ)
  | 4 => (-20209 / 200000000000 : ℝ)
  | 5 => (-13853 / 125000000000 : ℝ)
  | 6 => (-15099 / 125000000000 : ℝ)
  | 7 => (-16369 / 125000000000 : ℝ)
  | 8 => (-28261 / 200000000000 : ℝ)
  | 9 => (-151851 / 1000000000000 : ℝ)
  | 10 => (-162593 / 1000000000000 : ℝ)
  | 11 => (-43383 / 250000000000 : ℝ)
  | 12 => (-184669 / 1000000000000 : ℝ)
  | 13 => (-98003 / 500000000000 : ℝ)
  | 14 => (-207543 / 1000000000000 : ℝ)
  | 15 => (-219283 / 1000000000000 : ℝ)
  | 16 => (-231227 / 1000000000000 : ℝ)
  | 17 => (-15211 / 62500000000 : ℝ)
  | 18 => (-255731 / 1000000000000 : ℝ)
  | 19 => (-268293 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch022Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((440 : ℝ) + (j.val : ℝ)) / 1600)
      (((440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch022Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch022Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((440 : ℝ) + (j.val : ℝ)) / 1600)
    (((440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch022Neg100WeightLower j.val) (hpThetaShiftThreeBatch022Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch022Neg100WeightLower, hpThetaShiftThreeBatch022Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch022Neg100_integral_bounds :
    (-1759327 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-325231 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch022Lower hpThetaJensenCellsBatch022Upper
    hpThetaShiftThreeBatch022Neg100WeightLower hpThetaShiftThreeBatch022Neg100WeightUpper hpThetaJensenCellsBatch022_bounds hpThetaShiftThreeBatch022Neg100_weight_bounds
  have hl : (-1759327 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch022Lower j * hpThetaShiftThreeBatch022Neg100WeightLower j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftThreeBatch022Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftThreeBatch022Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch022Lower j * hpThetaShiftThreeBatch022Neg100WeightUpper j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftThreeBatch022Neg100WeightUpper j) / 1600) ≤ (-325231 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftThreeBatch022Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (440 : ℝ) / 1600 = 22 / 80 by norm_num,
    show ((440 : ℝ) + 20) / 1600 = (22 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch022Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (621113 / 1000000000000 : ℝ)
  | 1 => (620423 / 1000000000000 : ℝ)
  | 2 => (619597 / 1000000000000 : ℝ)
  | 3 => (618633 / 1000000000000 : ℝ)
  | 4 => (617529 / 1000000000000 : ℝ)
  | 5 => (616281 / 1000000000000 : ℝ)
  | 6 => (76861 / 125000000000 : ℝ)
  | 7 => (613347 / 1000000000000 : ℝ)
  | 8 => (76457 / 125000000000 : ℝ)
  | 9 => (609811 / 1000000000000 : ℝ)
  | 10 => (607811 / 1000000000000 : ℝ)
  | 11 => (151413 / 250000000000 : ℝ)
  | 12 => (603333 / 1000000000000 : ℝ)
  | 13 => (600851 / 1000000000000 : ℝ)
  | 14 => (598203 / 1000000000000 : ℝ)
  | 15 => (297693 / 500000000000 : ℝ)
  | 16 => (296199 / 500000000000 : ℝ)
  | 17 => (589237 / 1000000000000 : ℝ)
  | 18 => (585899 / 1000000000000 : ℝ)
  | 19 => (291191 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch022Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (621671 / 1000000000000 : ℝ)
  | 1 => (310557 / 500000000000 : ℝ)
  | 2 => (77553 / 125000000000 : ℝ)
  | 3 => (309799 / 500000000000 : ℝ)
  | 4 => (309317 / 500000000000 : ℝ)
  | 5 => (61753 / 100000000000 : ℝ)
  | 6 => (308141 / 500000000000 : ℝ)
  | 7 => (614889 / 1000000000000 : ℝ)
  | 8 => (153337 / 250000000000 : ℝ)
  | 9 => (611657 / 1000000000000 : ℝ)
  | 10 => (152453 / 250000000000 : ℝ)
  | 11 => (151953 / 250000000000 : ℝ)
  | 12 => (605653 / 1000000000000 : ℝ)
  | 13 => (301667 / 500000000000 : ℝ)
  | 14 => (150213 / 250000000000 : ℝ)
  | 15 => (149551 / 250000000000 : ℝ)
  | 16 => (595387 / 1000000000000 : ℝ)
  | 17 => (592399 / 1000000000000 : ℝ)
  | 18 => (294619 / 500000000000 : ℝ)
  | 19 => (5859 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch022Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((440 : ℝ) + (j.val : ℝ)) / 1600)
      (((440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch022Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch022Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((440 : ℝ) + (j.val : ℝ)) / 1600)
    (((440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch022Neg70WeightLower j.val) (hpThetaShiftThreeBatch022Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch022Neg70WeightLower, hpThetaShiftThreeBatch022Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch022Neg70_integral_bounds :
    (3098073 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (629613 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch022Lower hpThetaJensenCellsBatch022Upper
    hpThetaShiftThreeBatch022Neg70WeightLower hpThetaShiftThreeBatch022Neg70WeightUpper hpThetaJensenCellsBatch022_bounds hpThetaShiftThreeBatch022Neg70_weight_bounds
  have hl : (3098073 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch022Lower j * hpThetaShiftThreeBatch022Neg70WeightLower j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftThreeBatch022Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftThreeBatch022Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch022Lower j * hpThetaShiftThreeBatch022Neg70WeightUpper j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftThreeBatch022Neg70WeightUpper j) / 1600) ≤ (629613 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftThreeBatch022Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (440 : ℝ) / 1600 = 22 / 80 by norm_num,
    show ((440 : ℝ) + 20) / 1600 = (22 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch022Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (289437 / 200000000000 : ℝ)
  | 1 => (729573 / 500000000000 : ℝ)
  | 2 => (735559 / 500000000000 : ℝ)
  | 3 => (741549 / 500000000000 : ℝ)
  | 4 => (299017 / 200000000000 : ℝ)
  | 5 => (753539 / 500000000000 : ℝ)
  | 6 => (759537 / 500000000000 : ℝ)
  | 7 => (765537 / 500000000000 : ℝ)
  | 8 => (771537 / 500000000000 : ℝ)
  | 9 => (1555073 / 1000000000000 : ℝ)
  | 10 => (1567069 / 1000000000000 : ℝ)
  | 11 => (789531 / 500000000000 : ℝ)
  | 12 => (198881 / 125000000000 : ℝ)
  | 13 => (801513 / 500000000000 : ℝ)
  | 14 => (807497 / 500000000000 : ℝ)
  | 15 => (1626951 / 1000000000000 : ℝ)
  | 16 => (327779 / 200000000000 : ℝ)
  | 17 => (1650823 / 1000000000000 : ℝ)
  | 18 => (332547 / 200000000000 : ℝ)
  | 19 => (1674627 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch022Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1459147 / 1000000000000 : ℝ)
  | 1 => (1471119 / 1000000000000 : ℝ)
  | 2 => (1483099 / 1000000000000 : ℝ)
  | 3 => (747543 / 500000000000 : ℝ)
  | 4 => (1507079 / 1000000000000 : ℝ)
  | 5 => (60763 / 40000000000 : ℝ)
  | 6 => (61243 / 40000000000 : ℝ)
  | 7 => (61723 / 40000000000 : ℝ)
  | 8 => (777537 / 500000000000 : ℝ)
  | 9 => (156707 / 100000000000 : ℝ)
  | 10 => (1579063 / 1000000000000 : ℝ)
  | 11 => (1591049 / 1000000000000 : ℝ)
  | 12 => (1603027 / 1000000000000 : ℝ)
  | 13 => (322999 / 200000000000 : ℝ)
  | 14 => (203369 / 125000000000 : ℝ)
  | 15 => (102431 / 62500000000 : ℝ)
  | 16 => (206353 / 125000000000 : ℝ)
  | 17 => (103921 / 62500000000 : ℝ)
  | 18 => (418657 / 250000000000 : ℝ)
  | 19 => (1686499 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch022Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((440 : ℝ) + (j.val : ℝ)) / 1600)
      (((440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch022Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch022Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((440 : ℝ) + (j.val : ℝ)) / 1600)
    (((440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch022Neg45WeightLower j.val) (hpThetaShiftThreeBatch022Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch022Neg45WeightLower, hpThetaShiftThreeBatch022Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch022Neg45_integral_bounds :
    (15933873 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (16263071 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch022Lower hpThetaJensenCellsBatch022Upper
    hpThetaShiftThreeBatch022Neg45WeightLower hpThetaShiftThreeBatch022Neg45WeightUpper hpThetaJensenCellsBatch022_bounds hpThetaShiftThreeBatch022Neg45_weight_bounds
  have hl : (15933873 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch022Lower j * hpThetaShiftThreeBatch022Neg45WeightLower j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftThreeBatch022Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftThreeBatch022Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch022Lower j * hpThetaShiftThreeBatch022Neg45WeightUpper j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftThreeBatch022Neg45WeightUpper j) / 1600) ≤ (16263071 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftThreeBatch022Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (440 : ℝ) / 1600 = 22 / 80 by norm_num,
    show ((440 : ℝ) + 20) / 1600 = (22 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch022Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (71657 / 31250000000 : ℝ)
  | 1 => (579773 / 250000000000 : ℝ)
  | 2 => (469073 / 200000000000 : ℝ)
  | 3 => (2371843 / 1000000000000 : ℝ)
  | 4 => (37477 / 15625000000 : ℝ)
  | 5 => (2425419 / 1000000000000 : ℝ)
  | 6 => (2452517 / 1000000000000 : ℝ)
  | 7 => (1239911 / 500000000000 : ℝ)
  | 8 => (313417 / 125000000000 : ℝ)
  | 9 => (1267529 / 500000000000 : ℝ)
  | 10 => (640747 / 250000000000 : ℝ)
  | 11 => (323891 / 125000000000 : ℝ)
  | 12 => (1309739 / 500000000000 : ℝ)
  | 13 => (1324019 / 500000000000 : ℝ)
  | 14 => (334601 / 125000000000 : ℝ)
  | 15 => (2705789 / 1000000000000 : ℝ)
  | 16 => (1367491 / 500000000000 : ℝ)
  | 17 => (1382193 / 500000000000 : ℝ)
  | 18 => (1397001 / 500000000000 : ℝ)
  | 19 => (282383 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch022Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2319093 / 1000000000000 : ℝ)
  | 1 => (1172683 / 500000000000 : ℝ)
  | 2 => (592961 / 250000000000 : ℝ)
  | 3 => (2398529 / 1000000000000 : ℝ)
  | 4 => (121271 / 50000000000 : ℝ)
  | 5 => (1226259 / 500000000000 : ℝ)
  | 6 => (2479823 / 1000000000000 : ℝ)
  | 7 => (2507337 / 1000000000000 : ℝ)
  | 8 => (2535059 / 1000000000000 : ℝ)
  | 9 => (2562989 / 1000000000000 : ℝ)
  | 10 => (2591129 / 1000000000000 : ℝ)
  | 11 => (2619479 / 1000000000000 : ℝ)
  | 12 => (2648039 / 1000000000000 : ℝ)
  | 13 => (2676809 / 1000000000000 : ℝ)
  | 14 => (270579 / 100000000000 : ℝ)
  | 15 => (2734983 / 1000000000000 : ℝ)
  | 16 => (2764387 / 1000000000000 : ℝ)
  | 17 => (2794003 / 1000000000000 : ℝ)
  | 18 => (2823831 / 1000000000000 : ℝ)
  | 19 => (2853871 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch022Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((440 : ℝ) + (j.val : ℝ)) / 1600)
      (((440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch022Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch022Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((440 : ℝ) + (j.val : ℝ)) / 1600)
    (((440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch022Neg25WeightLower j.val) (hpThetaShiftThreeBatch022Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch022Neg25WeightLower, hpThetaShiftThreeBatch022Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch022Neg25_integral_bounds :
    (26043851 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (22 / 80 : ℝ) ((22 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (833421 / 31250000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch022Lower hpThetaJensenCellsBatch022Upper
    hpThetaShiftThreeBatch022Neg25WeightLower hpThetaShiftThreeBatch022Neg25WeightUpper hpThetaJensenCellsBatch022_bounds hpThetaShiftThreeBatch022Neg25_weight_bounds
  have hl : (26043851 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch022Lower j * hpThetaShiftThreeBatch022Neg25WeightLower j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftThreeBatch022Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftThreeBatch022Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch022Lower j * hpThetaShiftThreeBatch022Neg25WeightUpper j)
        (hpThetaJensenCellsBatch022Upper j * hpThetaShiftThreeBatch022Neg25WeightUpper j) / 1600) ≤ (833421 / 31250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch022Lower, hpThetaJensenCellsBatch022Upper,
      hpThetaShiftThreeBatch022Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (440 : ℝ) / 1600 = 22 / 80 by norm_num,
    show ((440 : ℝ) + 20) / 1600 = (22 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch022Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch022Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch022Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch022Neg25_integral_bounds
end HodgeProofHP
