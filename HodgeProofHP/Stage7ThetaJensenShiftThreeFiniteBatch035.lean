/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch035

/-! Exact signed weight and batch integral certificates, batch 35 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch035Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-289831 / 1000000000000 : ℝ)
  | 1 => (-6109 / 40000000000 : ℝ)
  | 2 => (-12497 / 1000000000000 : ℝ)
  | 3 => (130891 / 1000000000000 : ℝ)
  | 4 => (11099 / 40000000000 : ℝ)
  | 5 => (427291 / 1000000000000 : ℝ)
  | 6 => (72547 / 125000000000 : ℝ)
  | 7 => (368383 / 500000000000 : ℝ)
  | 8 => (896499 / 1000000000000 : ℝ)
  | 9 => (1059611 / 1000000000000 : ℝ)
  | 10 => (1226139 / 1000000000000 : ℝ)
  | 11 => (34903 / 25000000000 : ℝ)
  | 12 => (1569591 / 1000000000000 : ℝ)
  | 13 => (1746589 / 1000000000000 : ℝ)
  | 14 => (1927151 / 1000000000000 : ℝ)
  | 15 => (1055657 / 500000000000 : ℝ)
  | 16 => (459823 / 200000000000 : ℝ)
  | 17 => (2490591 / 1000000000000 : ℝ)
  | 18 => (134289 / 50000000000 : ℝ)
  | 19 => (1442359 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch035Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-38181 / 250000000000 : ℝ)
  | 1 => (-781 / 62500000000 : ℝ)
  | 2 => (32723 / 250000000000 : ℝ)
  | 3 => (69369 / 250000000000 : ℝ)
  | 4 => (106823 / 250000000000 : ℝ)
  | 5 => (580377 / 1000000000000 : ℝ)
  | 6 => (736767 / 1000000000000 : ℝ)
  | 7 => (1793 / 2000000000 : ℝ)
  | 8 => (264903 / 250000000000 : ℝ)
  | 9 => (61307 / 50000000000 : ℝ)
  | 10 => (1396121 / 1000000000000 : ℝ)
  | 11 => (196199 / 125000000000 : ℝ)
  | 12 => (174659 / 100000000000 : ℝ)
  | 13 => (120447 / 62500000000 : ℝ)
  | 14 => (422263 / 200000000000 : ℝ)
  | 15 => (574779 / 250000000000 : ℝ)
  | 16 => (77831 / 31250000000 : ℝ)
  | 17 => (2685781 / 1000000000000 : ℝ)
  | 18 => (2884719 / 1000000000000 : ℝ)
  | 19 => (771861 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch035Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((700 : ℝ) + (j.val : ℝ)) / 1600)
      (((700 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch035Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch035Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((700 : ℝ) + (j.val : ℝ)) / 1600)
    (((700 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch035Neg100WeightLower j.val) (hpThetaShiftThreeBatch035Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch035Neg100WeightLower, hpThetaShiftThreeBatch035Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch035Neg100_integral_bounds :
    (3277863 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (3810909 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (700 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch035Lower hpThetaJensenCellsBatch035Upper
    hpThetaShiftThreeBatch035Neg100WeightLower hpThetaShiftThreeBatch035Neg100WeightUpper hpThetaJensenCellsBatch035_bounds hpThetaShiftThreeBatch035Neg100_weight_bounds
  have hl : (3277863 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch035Lower j * hpThetaShiftThreeBatch035Neg100WeightLower j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftThreeBatch035Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftThreeBatch035Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch035Lower j * hpThetaShiftThreeBatch035Neg100WeightUpper j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftThreeBatch035Neg100WeightUpper j) / 1600) ≤ (3810909 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftThreeBatch035Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (700 : ℝ) / 1600 = 35 / 80 by norm_num,
    show ((700 : ℝ) + 20) / 1600 = (35 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch035Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-9873883 / 1000000000000 : ℝ)
  | 1 => (-2485047 / 250000000000 : ℝ)
  | 2 => (-10005939 / 1000000000000 : ℝ)
  | 3 => (-2517779 / 250000000000 : ℝ)
  | 4 => (-2027139 / 200000000000 : ℝ)
  | 5 => (-1274957 / 125000000000 : ℝ)
  | 6 => (-160359 / 15625000000 : ℝ)
  | 7 => (-80669 / 7812500000 : ℝ)
  | 8 => (-5193801 / 500000000000 : ℝ)
  | 9 => (-10448863 / 1000000000000 : ℝ)
  | 10 => (-10509391 / 1000000000000 : ℝ)
  | 11 => (-5284581 / 500000000000 : ℝ)
  | 12 => (-1328519 / 125000000000 : ℝ)
  | 13 => (-5343169 / 500000000000 : ℝ)
  | 14 => (-5371847 / 500000000000 : ℝ)
  | 15 => (-2160039 / 200000000000 : ℝ)
  | 16 => (-10855817 / 1000000000000 : ℝ)
  | 17 => (-5455267 / 500000000000 : ℝ)
  | 18 => (-10964319 / 1000000000000 : ℝ)
  | 19 => (-2754287 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch035Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2451761 / 250000000000 : ℝ)
  | 1 => (-4936941 / 500000000000 : ℝ)
  | 2 => (-9940187 / 1000000000000 : ℝ)
  | 3 => (-5002969 / 500000000000 : ℝ)
  | 4 => (-2014223 / 200000000000 : ℝ)
  | 5 => (-5067847 / 500000000000 : ℝ)
  | 6 => (-2039931 / 200000000000 : ℝ)
  | 7 => (-410519 / 40000000000 : ℝ)
  | 8 => (-10325631 / 1000000000000 : ℝ)
  | 9 => (-10387601 / 1000000000000 : ℝ)
  | 10 => (-5224431 / 500000000000 : ℝ)
  | 11 => (-1050939 / 100000000000 : ℝ)
  | 12 => (-10569161 / 1000000000000 : ℝ)
  | 13 => (-10628151 / 1000000000000 : ℝ)
  | 14 => (-10686337 / 1000000000000 : ℝ)
  | 15 => (-10743693 / 1000000000000 : ℝ)
  | 16 => (-5400097 / 500000000000 : ℝ)
  | 17 => (-1356977 / 125000000000 : ℝ)
  | 18 => (-10910533 / 1000000000000 : ℝ)
  | 19 => (-5482159 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch035Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((700 : ℝ) + (j.val : ℝ)) / 1600)
      (((700 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch035Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch035Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((700 : ℝ) + (j.val : ℝ)) / 1600)
    (((700 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch035Neg70WeightLower j.val) (hpThetaShiftThreeBatch035Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch035Neg70WeightLower, hpThetaShiftThreeBatch035Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch035Neg70_integral_bounds :
    (-29903637 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-1463949 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (700 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch035Lower hpThetaJensenCellsBatch035Upper
    hpThetaShiftThreeBatch035Neg70WeightLower hpThetaShiftThreeBatch035Neg70WeightUpper hpThetaJensenCellsBatch035_bounds hpThetaShiftThreeBatch035Neg70_weight_bounds
  have hl : (-29903637 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch035Lower j * hpThetaShiftThreeBatch035Neg70WeightLower j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftThreeBatch035Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftThreeBatch035Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch035Lower j * hpThetaShiftThreeBatch035Neg70WeightUpper j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftThreeBatch035Neg70WeightUpper j) / 1600) ≤ (-1463949 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftThreeBatch035Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (700 : ℝ) / 1600 = 35 / 80 by norm_num,
    show ((700 : ℝ) + 20) / 1600 = (35 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch035Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4654897 / 1000000000000 : ℝ)
  | 1 => (-1191613 / 250000000000 : ℝ)
  | 2 => (-609887 / 125000000000 : ℝ)
  | 3 => (-78013 / 15625000000 : ℝ)
  | 4 => (-5107661 / 1000000000000 : ℝ)
  | 5 => (-5223587 / 1000000000000 : ℝ)
  | 6 => (-1335153 / 250000000000 : ℝ)
  | 7 => (-5458739 / 1000000000000 : ℝ)
  | 8 => (-348623 / 62500000000 : ℝ)
  | 9 => (-2849151 / 500000000000 : ℝ)
  | 10 => (-181867 / 31250000000 : ℝ)
  | 11 => (-2971147 / 500000000000 : ℝ)
  | 12 => (-1213191 / 200000000000 : ℝ)
  | 13 => (-6190729 / 1000000000000 : ℝ)
  | 14 => (-789577 / 125000000000 : ℝ)
  | 15 => (-6443619 / 1000000000000 : ℝ)
  | 16 => (-6571739 / 1000000000000 : ℝ)
  | 17 => (-418811 / 62500000000 : ℝ)
  | 18 => (-1707833 / 250000000000 : ℝ)
  | 19 => (-870351 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch035Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4544427 / 1000000000000 : ℝ)
  | 1 => (-290931 / 62500000000 : ℝ)
  | 2 => (-4766451 / 1000000000000 : ℝ)
  | 3 => (-975819 / 200000000000 : ℝ)
  | 4 => (-4992831 / 1000000000000 : ℝ)
  | 5 => (-255383 / 50000000000 : ℝ)
  | 6 => (-2611793 / 500000000000 : ℝ)
  | 7 => (-5340611 / 1000000000000 : ℝ)
  | 8 => (-2729369 / 500000000000 : ℝ)
  | 9 => (-5577967 / 1000000000000 : ℝ)
  | 10 => (-5698301 / 1000000000000 : ℝ)
  | 11 => (-5819743 / 1000000000000 : ℝ)
  | 12 => (-5942293 / 1000000000000 : ℝ)
  | 13 => (-3032977 / 500000000000 : ℝ)
  | 14 => (-773841 / 125000000000 : ℝ)
  | 15 => (-1263323 / 200000000000 : ℝ)
  | 16 => (-3221809 / 500000000000 : ℝ)
  | 17 => (-3285869 / 500000000000 : ℝ)
  | 18 => (-268039 / 40000000000 : ℝ)
  | 19 => (-6831331 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch035Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((700 : ℝ) + (j.val : ℝ)) / 1600)
      (((700 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch035Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch035Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((700 : ℝ) + (j.val : ℝ)) / 1600)
    (((700 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch035Neg45WeightLower j.val) (hpThetaShiftThreeBatch035Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch035Neg45WeightLower, hpThetaShiftThreeBatch035Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch035Neg45_integral_bounds :
    (-411299 / 25000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-15862241 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (700 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch035Lower hpThetaJensenCellsBatch035Upper
    hpThetaShiftThreeBatch035Neg45WeightLower hpThetaShiftThreeBatch035Neg45WeightUpper hpThetaJensenCellsBatch035_bounds hpThetaShiftThreeBatch035Neg45_weight_bounds
  have hl : (-411299 / 25000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch035Lower j * hpThetaShiftThreeBatch035Neg45WeightLower j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftThreeBatch035Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftThreeBatch035Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch035Lower j * hpThetaShiftThreeBatch035Neg45WeightUpper j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftThreeBatch035Neg45WeightUpper j) / 1600) ≤ (-15862241 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftThreeBatch035Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (700 : ℝ) / 1600 = 35 / 80 by norm_num,
    show ((700 : ℝ) + 20) / 1600 = (35 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch035Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (13290753 / 1000000000000 : ℝ)
  | 1 => (3328567 / 250000000000 : ℝ)
  | 2 => (13337119 / 1000000000000 : ℝ)
  | 3 => (2671859 / 200000000000 : ℝ)
  | 4 => (3345197 / 250000000000 : ℝ)
  | 5 => (3350397 / 250000000000 : ℝ)
  | 6 => (2684337 / 200000000000 : ℝ)
  | 7 => (1344107 / 100000000000 : ℝ)
  | 8 => (13459733 / 1000000000000 : ℝ)
  | 9 => (421177 / 31250000000 : ℝ)
  | 10 => (2698971 / 200000000000 : ℝ)
  | 11 => (2702259 / 200000000000 : ℝ)
  | 12 => (13526973 / 1000000000000 : ℝ)
  | 13 => (6770941 / 500000000000 : ℝ)
  | 14 => (13556009 / 1000000000000 : ℝ)
  | 15 => (6784673 / 500000000000 : ℝ)
  | 16 => (13581883 / 1000000000000 : ℝ)
  | 17 => (13593609 / 1000000000000 : ℝ)
  | 18 => (6802257 / 500000000000 : ℝ)
  | 19 => (3403647 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch035Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (13314269 / 1000000000000 : ℝ)
  | 1 => (83357 / 6250000000 : ℝ)
  | 2 => (208739 / 15625000000 : ℝ)
  | 3 => (13380789 / 1000000000000 : ℝ)
  | 4 => (13401589 / 1000000000000 : ℝ)
  | 5 => (6710843 / 500000000000 : ℝ)
  | 6 => (13441071 / 1000000000000 : ℝ)
  | 7 => (6729867 / 500000000000 : ℝ)
  | 8 => (2695533 / 200000000000 : ℝ)
  | 9 => (1686857 / 125000000000 : ℝ)
  | 10 => (105557 / 7812500000 : ℝ)
  | 11 => (6763487 / 500000000000 : ℝ)
  | 12 => (13541883 / 1000000000000 : ℝ)
  | 13 => (1355601 / 100000000000 : ℝ)
  | 14 => (13569347 / 1000000000000 : ℝ)
  | 15 => (3395471 / 250000000000 : ℝ)
  | 16 => (1359361 / 100000000000 : ℝ)
  | 17 => (2720903 / 200000000000 : ℝ)
  | 18 => (13614589 / 1000000000000 : ℝ)
  | 19 => (13623821 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch035Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((700 : ℝ) + (j.val : ℝ)) / 1600)
      (((700 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch035Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch035Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((700 : ℝ) + (j.val : ℝ)) / 1600)
    (((700 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch035Neg25WeightLower j.val) (hpThetaShiftThreeBatch035Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch035Neg25WeightLower, hpThetaShiftThreeBatch035Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch035Neg25_integral_bounds :
    (7589457 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (19290003 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (700 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch035Lower hpThetaJensenCellsBatch035Upper
    hpThetaShiftThreeBatch035Neg25WeightLower hpThetaShiftThreeBatch035Neg25WeightUpper hpThetaJensenCellsBatch035_bounds hpThetaShiftThreeBatch035Neg25_weight_bounds
  have hl : (7589457 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch035Lower j * hpThetaShiftThreeBatch035Neg25WeightLower j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftThreeBatch035Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftThreeBatch035Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch035Lower j * hpThetaShiftThreeBatch035Neg25WeightUpper j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftThreeBatch035Neg25WeightUpper j) / 1600) ≤ (19290003 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftThreeBatch035Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (700 : ℝ) / 1600 = 35 / 80 by norm_num,
    show ((700 : ℝ) + 20) / 1600 = (35 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch035Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch035Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch035Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch035Neg25_integral_bounds
end HodgeProofHP
