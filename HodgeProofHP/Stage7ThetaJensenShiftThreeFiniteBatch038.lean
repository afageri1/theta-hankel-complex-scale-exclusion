/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch038

/-! Exact signed weight and batch integral certificates, batch 38 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch038Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (14715021 / 1000000000000 : ℝ)
  | 1 => (1887929 / 125000000000 : ℝ)
  | 2 => (7748521 / 500000000000 : ℝ)
  | 3 => (3973969 / 250000000000 : ℝ)
  | 4 => (16299959 / 1000000000000 : ℝ)
  | 5 => (8354659 / 500000000000 : ℝ)
  | 6 => (17123977 / 1000000000000 : ℝ)
  | 7 => (438599 / 25000000000 : ℝ)
  | 8 => (17969289 / 1000000000000 : ℝ)
  | 9 => (4599997 / 250000000000 : ℝ)
  | 10 => (9418039 / 500000000000 : ℝ)
  | 11 => (9638791 / 500000000000 : ℝ)
  | 12 => (9862259 / 500000000000 : ℝ)
  | 13 => (5044227 / 250000000000 : ℝ)
  | 14 => (20634771 / 1000000000000 : ℝ)
  | 15 => (5274531 / 250000000000 : ℝ)
  | 16 => (4313397 / 200000000000 : ℝ)
  | 17 => (2204137 / 100000000000 : ℝ)
  | 18 => (22521297 / 1000000000000 : ℝ)
  | 19 => (23006779 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch038Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (15103433 / 1000000000000 : ℝ)
  | 1 => (15497043 / 1000000000000 : ℝ)
  | 2 => (15895877 / 1000000000000 : ℝ)
  | 3 => (407499 / 25000000000 : ℝ)
  | 4 => (16709319 / 1000000000000 : ℝ)
  | 5 => (8561989 / 500000000000 : ℝ)
  | 6 => (17543961 / 1000000000000 : ℝ)
  | 7 => (1796929 / 100000000000 : ℝ)
  | 8 => (18399989 / 1000000000000 : ℝ)
  | 9 => (18836079 / 1000000000000 : ℝ)
  | 10 => (19277583 / 1000000000000 : ℝ)
  | 11 => (19724519 / 1000000000000 : ℝ)
  | 12 => (20176909 / 1000000000000 : ℝ)
  | 13 => (5158693 / 250000000000 : ℝ)
  | 14 => (33757 / 1600000000 : ℝ)
  | 15 => (10783493 / 500000000000 : ℝ)
  | 16 => (22041371 / 1000000000000 : ℝ)
  | 17 => (11260649 / 500000000000 : ℝ)
  | 18 => (1150339 / 50000000000 : ℝ)
  | 19 => (2937229 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch038Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((760 : ℝ) + (j.val : ℝ)) / 1600)
      (((760 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch038Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch038Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((760 : ℝ) + (j.val : ℝ)) / 1600)
    (((760 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch038Neg100WeightLower j.val) (hpThetaShiftThreeBatch038Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch038Neg100WeightLower, hpThetaShiftThreeBatch038Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch038Neg100_integral_bounds :
    (1741987 / 50000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (18117691 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (760 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch038Lower hpThetaJensenCellsBatch038Upper
    hpThetaShiftThreeBatch038Neg100WeightLower hpThetaShiftThreeBatch038Neg100WeightUpper hpThetaJensenCellsBatch038_bounds hpThetaShiftThreeBatch038Neg100_weight_bounds
  have hl : (1741987 / 50000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch038Lower j * hpThetaShiftThreeBatch038Neg100WeightLower j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftThreeBatch038Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftThreeBatch038Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch038Lower j * hpThetaShiftThreeBatch038Neg100WeightUpper j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftThreeBatch038Neg100WeightUpper j) / 1600) ≤ (18117691 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftThreeBatch038Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (760 : ℝ) / 1600 = 38 / 80 by norm_num,
    show ((760 : ℝ) + 20) / 1600 = (38 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch038Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-12005831 / 1000000000000 : ℝ)
  | 1 => (-11992933 / 1000000000000 : ℝ)
  | 2 => (-2395537 / 200000000000 : ℝ)
  | 3 => (-747503 / 62500000000 : ℝ)
  | 4 => (-11939981 / 1000000000000 : ℝ)
  | 5 => (-5958721 / 500000000000 : ℝ)
  | 6 => (-11892391 / 1000000000000 : ℝ)
  | 7 => (-2372957 / 200000000000 : ℝ)
  | 8 => (-5917291 / 500000000000 : ℝ)
  | 9 => (-590087 / 50000000000 : ℝ)
  | 10 => (-1470777 / 125000000000 : ℝ)
  | 11 => (-11727967 / 1000000000000 : ℝ)
  | 12 => (-233739 / 20000000000 : ℝ)
  | 13 => (-145539 / 12500000000 : ℝ)
  | 14 => (-11596433 / 1000000000000 : ℝ)
  | 15 => (-5773423 / 500000000000 : ℝ)
  | 16 => (-1436789 / 125000000000 : ℝ)
  | 17 => (-11438787 / 1000000000000 : ℝ)
  | 18 => (-5690113 / 500000000000 : ℝ)
  | 19 => (-5659291 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch038Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2998233 / 250000000000 : ℝ)
  | 1 => (-2994421 / 250000000000 : ℝ)
  | 2 => (-11960047 / 1000000000000 : ℝ)
  | 3 => (-596999 / 50000000000 : ℝ)
  | 4 => (-11917441 / 1000000000000 : ℝ)
  | 5 => (-1189239 / 100000000000 : ℝ)
  | 6 => (-741549 / 62500000000 : ℝ)
  | 7 => (-11834581 / 1000000000000 : ℝ)
  | 8 => (-11801739 / 1000000000000 : ℝ)
  | 9 => (-2353243 / 200000000000 : ℝ)
  | 10 => (-5863983 / 500000000000 : ℝ)
  | 11 => (-11686949 / 1000000000000 : ℝ)
  | 12 => (-11643119 / 1000000000000 : ℝ)
  | 13 => (-724777 / 62500000000 : ℝ)
  | 14 => (-2309369 / 200000000000 : ℝ)
  | 15 => (-11494311 / 1000000000000 : ℝ)
  | 16 => (-5719393 / 500000000000 : ℝ)
  | 17 => (-455209 / 40000000000 : ℝ)
  | 18 => (-11318581 / 1000000000000 : ℝ)
  | 19 => (-703363 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch038Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((760 : ℝ) + (j.val : ℝ)) / 1600)
      (((760 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch038Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch038Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((760 : ℝ) + (j.val : ℝ)) / 1600)
    (((760 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch038Neg70WeightLower j.val) (hpThetaShiftThreeBatch038Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch038Neg70WeightLower, hpThetaShiftThreeBatch038Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch038Neg70_integral_bounds :
    (-2235667 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-21932553 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (760 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch038Lower hpThetaJensenCellsBatch038Upper
    hpThetaShiftThreeBatch038Neg70WeightLower hpThetaShiftThreeBatch038Neg70WeightUpper hpThetaJensenCellsBatch038_bounds hpThetaShiftThreeBatch038Neg70_weight_bounds
  have hl : (-2235667 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch038Lower j * hpThetaShiftThreeBatch038Neg70WeightLower j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftThreeBatch038Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftThreeBatch038Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch038Lower j * hpThetaShiftThreeBatch038Neg70WeightUpper j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftThreeBatch038Neg70WeightUpper j) / 1600) ≤ (-21932553 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftThreeBatch038Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (760 : ℝ) / 1600 = 38 / 80 by norm_num,
    show ((760 : ℝ) + 20) / 1600 = (38 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch038Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-13313061 / 1000000000000 : ℝ)
  | 1 => (-6745387 / 500000000000 : ℝ)
  | 2 => (-13669523 / 1000000000000 : ℝ)
  | 3 => (-138493 / 10000000000 : ℝ)
  | 4 => (-14030101 / 1000000000000 : ℝ)
  | 5 => (-177649 / 12500000000 : ℝ)
  | 6 => (-57579 / 4000000000 : ℝ)
  | 7 => (-2915717 / 200000000000 : ℝ)
  | 8 => (-14763419 / 1000000000000 : ℝ)
  | 9 => (-3737311 / 250000000000 : ℝ)
  | 10 => (-7568027 / 500000000000 : ℝ)
  | 11 => (-7661921 / 500000000000 : ℝ)
  | 12 => (-77563 / 5000000000 : ℝ)
  | 13 => (-196279 / 12500000000 : ℝ)
  | 14 => (-3973249 / 250000000000 : ℝ)
  | 15 => (-8042309 / 500000000000 : ℝ)
  | 16 => (-16277179 / 1000000000000 : ℝ)
  | 17 => (-16470671 / 1000000000000 : ℝ)
  | 18 => (-4166271 / 250000000000 : ℝ)
  | 19 => (-16860409 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch038Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6568193 / 500000000000 : ℝ)
  | 1 => (-665653 / 50000000000 : ℝ)
  | 2 => (-13490773 / 1000000000000 : ℝ)
  | 3 => (-6834761 / 500000000000 : ℝ)
  | 4 => (-13849299 / 1000000000000 : ℝ)
  | 5 => (-140301 / 10000000000 : ℝ)
  | 6 => (-14211919 / 1000000000000 : ℝ)
  | 7 => (-14394749 / 1000000000000 : ℝ)
  | 8 => (-1822323 / 125000000000 : ℝ)
  | 9 => (-7381709 / 500000000000 : ℝ)
  | 10 => (-14949243 / 1000000000000 : ℝ)
  | 11 => (-15136053 / 1000000000000 : ℝ)
  | 12 => (-15323841 / 1000000000000 : ℝ)
  | 13 => (-15512599 / 1000000000000 : ℝ)
  | 14 => (-15702319 / 1000000000000 : ℝ)
  | 15 => (-3178599 / 200000000000 : ℝ)
  | 16 => (-16084617 / 1000000000000 : ℝ)
  | 17 => (-8138589 / 500000000000 : ℝ)
  | 18 => (-1647067 / 100000000000 : ℝ)
  | 19 => (-16665083 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch038Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((760 : ℝ) + (j.val : ℝ)) / 1600)
      (((760 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch038Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch038Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((760 : ℝ) + (j.val : ℝ)) / 1600)
    (((760 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch038Neg45WeightLower j.val) (hpThetaShiftThreeBatch038Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch038Neg45WeightLower, hpThetaShiftThreeBatch038Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch038Neg45_integral_bounds :
    (-3571579 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-27770573 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (760 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch038Lower hpThetaJensenCellsBatch038Upper
    hpThetaShiftThreeBatch038Neg45WeightLower hpThetaShiftThreeBatch038Neg45WeightUpper hpThetaJensenCellsBatch038_bounds hpThetaShiftThreeBatch038Neg45_weight_bounds
  have hl : (-3571579 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch038Lower j * hpThetaShiftThreeBatch038Neg45WeightLower j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftThreeBatch038Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftThreeBatch038Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch038Lower j * hpThetaShiftThreeBatch038Neg45WeightUpper j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftThreeBatch038Neg45WeightUpper j) / 1600) ≤ (-27770573 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftThreeBatch038Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (760 : ℝ) / 1600 = 38 / 80 by norm_num,
    show ((760 : ℝ) + 20) / 1600 = (38 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch038Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (65723 / 5000000000 : ℝ)
  | 1 => (6554287 / 500000000000 : ℝ)
  | 2 => (653561 / 50000000000 : ℝ)
  | 3 => (521301 / 40000000000 : ℝ)
  | 4 => (519699 / 40000000000 : ℝ)
  | 5 => (647553 / 50000000000 : ℝ)
  | 6 => (6454133 / 500000000000 : ℝ)
  | 7 => (6432041 / 500000000000 : ℝ)
  | 8 => (12818493 / 1000000000000 : ℝ)
  | 9 => (12771489 / 1000000000000 : ℝ)
  | 10 => (2544611 / 200000000000 : ℝ)
  | 11 => (633659 / 50000000000 : ℝ)
  | 12 => (12621851 / 1000000000000 : ℝ)
  | 13 => (2513811 / 200000000000 : ℝ)
  | 14 => (625739 / 50000000000 : ℝ)
  | 15 => (3114753 / 250000000000 : ℝ)
  | 16 => (6200869 / 500000000000 : ℝ)
  | 17 => (12342947 / 1000000000000 : ℝ)
  | 18 => (47979 / 3906250000 : ℝ)
  | 19 => (12220757 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch038Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (13179309 / 1000000000000 : ℝ)
  | 1 => (13144601 / 1000000000000 : ℝ)
  | 2 => (524343 / 40000000000 : ℝ)
  | 3 => (13071221 / 1000000000000 : ℝ)
  | 4 => (6516263 / 500000000000 : ℝ)
  | 5 => (3248119 / 250000000000 : ℝ)
  | 6 => (12951061 / 1000000000000 : ℝ)
  | 7 => (12908267 / 1000000000000 : ℝ)
  | 8 => (12864083 / 1000000000000 : ℝ)
  | 9 => (6409247 / 500000000000 : ℝ)
  | 10 => (1277149 / 100000000000 : ℝ)
  | 11 => (795191 / 62500000000 : ℝ)
  | 12 => (12673181 / 1000000000000 : ℝ)
  | 13 => (3155463 / 250000000000 : ℝ)
  | 14 => (392783 / 31250000000 : ℝ)
  | 15 => (12514781 / 1000000000000 : ℝ)
  | 16 => (12459013 / 1000000000000 : ℝ)
  | 17 => (12401739 / 1000000000000 : ℝ)
  | 18 => (3085737 / 250000000000 : ℝ)
  | 19 => (98261 / 8000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch038Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((760 : ℝ) + (j.val : ℝ)) / 1600)
      (((760 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch038Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch038Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((760 : ℝ) + (j.val : ℝ)) / 1600)
    (((760 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch038Neg25WeightLower j.val) (hpThetaShiftThreeBatch038Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch038Neg25WeightLower, hpThetaShiftThreeBatch038Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch038Neg25_integral_bounds :
    (11925369 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (4865207 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (760 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch038Lower hpThetaJensenCellsBatch038Upper
    hpThetaShiftThreeBatch038Neg25WeightLower hpThetaShiftThreeBatch038Neg25WeightUpper hpThetaJensenCellsBatch038_bounds hpThetaShiftThreeBatch038Neg25_weight_bounds
  have hl : (11925369 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch038Lower j * hpThetaShiftThreeBatch038Neg25WeightLower j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftThreeBatch038Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftThreeBatch038Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch038Lower j * hpThetaShiftThreeBatch038Neg25WeightUpper j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftThreeBatch038Neg25WeightUpper j) / 1600) ≤ (4865207 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftThreeBatch038Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (760 : ℝ) / 1600 = 38 / 80 by norm_num,
    show ((760 : ℝ) + 20) / 1600 = (38 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch038Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch038Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch038Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch038Neg25_integral_bounds
end HodgeProofHP
