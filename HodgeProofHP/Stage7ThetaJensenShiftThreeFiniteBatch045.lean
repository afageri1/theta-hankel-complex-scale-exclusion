/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch045

/-! Exact signed weight and batch integral certificates, batch 45 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch045Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4481597 / 40000000000 : ℝ)
  | 1 => (112732067 / 1000000000000 : ℝ)
  | 2 => (7088351 / 62500000000 : ℝ)
  | 3 => (22816831 / 200000000000 : ℝ)
  | 4 => (5737163 / 50000000000 : ℝ)
  | 5 => (115390499 / 1000000000000 : ℝ)
  | 6 => (116025431 / 1000000000000 : ℝ)
  | 7 => (116647607 / 1000000000000 : ℝ)
  | 8 => (117256571 / 1000000000000 : ℝ)
  | 9 => (117851859 / 1000000000000 : ℝ)
  | 10 => (23686599 / 200000000000 : ℝ)
  | 11 => (237999 / 2000000000 : ℝ)
  | 12 => (119550881 / 1000000000000 : ℝ)
  | 13 => (120086641 / 1000000000000 : ℝ)
  | 14 => (120606269 / 1000000000000 : ℝ)
  | 15 => (484437 / 4000000000 : ℝ)
  | 16 => (7599691 / 62500000000 : ℝ)
  | 17 => (122063153 / 1000000000000 : ℝ)
  | 18 => (61256497 / 500000000000 : ℝ)
  | 19 => (122944027 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch045Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (28183017 / 250000000000 : ℝ)
  | 1 => (113413617 / 1000000000000 : ℝ)
  | 2 => (28521039 / 250000000000 : ℝ)
  | 3 => (114743261 / 1000000000000 : ℝ)
  | 4 => (230781 / 2000000000 : ℝ)
  | 5 => (14503179 / 125000000000 : ℝ)
  | 6 => (14580951 / 125000000000 : ℝ)
  | 7 => (29314143 / 250000000000 : ℝ)
  | 8 => (5892593 / 50000000000 : ℝ)
  | 9 => (29608249 / 250000000000 : ℝ)
  | 10 => (118999501 / 1000000000000 : ℝ)
  | 11 => (59775441 / 500000000000 : ℝ)
  | 12 => (60043321 / 500000000000 : ℝ)
  | 13 => (12060627 / 100000000000 : ℝ)
  | 14 => (121109251 / 1000000000000 : ℝ)
  | 15 => (121595057 / 1000000000000 : ℝ)
  | 16 => (61031577 / 500000000000 : ℝ)
  | 17 => (24502599 / 200000000000 : ℝ)
  | 18 => (30736007 / 250000000000 : ℝ)
  | 19 => (123355687 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch045Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((900 : ℝ) + (j.val : ℝ)) / 1600)
      (((900 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch045Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch045Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((900 : ℝ) + (j.val : ℝ)) / 1600)
    (((900 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch045Neg100WeightLower j.val) (hpThetaShiftThreeBatch045Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch045Neg100WeightLower, hpThetaShiftThreeBatch045Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch045Neg100_integral_bounds :
    (8773899 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (71806419 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (900 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch045Lower hpThetaJensenCellsBatch045Upper
    hpThetaShiftThreeBatch045Neg100WeightLower hpThetaShiftThreeBatch045Neg100WeightUpper hpThetaJensenCellsBatch045_bounds hpThetaShiftThreeBatch045Neg100_weight_bounds
  have hl : (8773899 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch045Lower j * hpThetaShiftThreeBatch045Neg100WeightLower j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftThreeBatch045Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftThreeBatch045Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch045Lower j * hpThetaShiftThreeBatch045Neg100WeightUpper j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftThreeBatch045Neg100WeightUpper j) / 1600) ≤ (71806419 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftThreeBatch045Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (900 : ℝ) / 1600 = 45 / 80 by norm_num,
    show ((900 : ℝ) + 20) / 1600 = (45 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch045Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (707713 / 20000000000 : ℝ)
  | 1 => (36245157 / 1000000000000 : ℝ)
  | 2 => (37114859 / 1000000000000 : ℝ)
  | 3 => (7598961 / 200000000000 : ℝ)
  | 4 => (7777009 / 200000000000 : ℝ)
  | 5 => (39785631 / 1000000000000 : ℝ)
  | 6 => (40696609 / 1000000000000 : ℝ)
  | 7 => (4161803 / 100000000000 : ℝ)
  | 8 => (2127497 / 50000000000 : ℝ)
  | 9 => (21746193 / 500000000000 : ℝ)
  | 10 => (22222707 / 500000000000 : ℝ)
  | 11 => (4540907 / 100000000000 : ℝ)
  | 12 => (46383399 / 1000000000000 : ℝ)
  | 13 => (11842111 / 250000000000 : ℝ)
  | 14 => (6045531 / 125000000000 : ℝ)
  | 15 => (24685427 / 500000000000 : ℝ)
  | 16 => (50388301 / 1000000000000 : ℝ)
  | 17 => (6427079 / 125000000000 : ℝ)
  | 18 => (10491177 / 200000000000 : ℝ)
  | 19 => (53506099 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch045Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (18122579 / 500000000000 : ℝ)
  | 1 => (1855743 / 50000000000 : ℝ)
  | 2 => (18997403 / 500000000000 : ℝ)
  | 3 => (19442523 / 500000000000 : ℝ)
  | 4 => (1243301 / 31250000000 : ℝ)
  | 5 => (4069661 / 100000000000 : ℝ)
  | 6 => (41618031 / 1000000000000 : ℝ)
  | 7 => (42549941 / 1000000000000 : ℝ)
  | 8 => (43492387 / 1000000000000 : ℝ)
  | 9 => (8889083 / 200000000000 : ℝ)
  | 10 => (45409071 / 1000000000000 : ℝ)
  | 11 => (231917 / 5000000000 : ℝ)
  | 12 => (9473689 / 200000000000 : ℝ)
  | 13 => (48364249 / 1000000000000 : ℝ)
  | 14 => (9874171 / 200000000000 : ℝ)
  | 15 => (25194151 / 500000000000 : ℝ)
  | 16 => (51416633 / 1000000000000 : ℝ)
  | 17 => (26227943 / 500000000000 : ℝ)
  | 18 => (535061 / 10000000000 : ℝ)
  | 19 => (54567313 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch045Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((900 : ℝ) + (j.val : ℝ)) / 1600)
      (((900 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch045Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch045Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((900 : ℝ) + (j.val : ℝ)) / 1600)
    (((900 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch045Neg70WeightLower j.val) (hpThetaShiftThreeBatch045Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch045Neg70WeightLower, hpThetaShiftThreeBatch045Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch045Neg70_integral_bounds :
    (26145309 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (849951 / 31250000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (900 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch045Lower hpThetaJensenCellsBatch045Upper
    hpThetaShiftThreeBatch045Neg70WeightLower hpThetaShiftThreeBatch045Neg70WeightUpper hpThetaJensenCellsBatch045_bounds hpThetaShiftThreeBatch045Neg70_weight_bounds
  have hl : (26145309 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch045Lower j * hpThetaShiftThreeBatch045Neg70WeightLower j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftThreeBatch045Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftThreeBatch045Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch045Lower j * hpThetaShiftThreeBatch045Neg70WeightUpper j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftThreeBatch045Neg70WeightUpper j) / 1600) ≤ (849951 / 31250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftThreeBatch045Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (900 : ℝ) / 1600 = 45 / 80 by norm_num,
    show ((900 : ℝ) + 20) / 1600 = (45 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch045Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-41932489 / 1000000000000 : ℝ)
  | 1 => (-8416359 / 200000000000 : ℝ)
  | 2 => (-42228509 / 1000000000000 : ℝ)
  | 3 => (-2118629 / 50000000000 : ℝ)
  | 4 => (-42513951 / 1000000000000 : ℝ)
  | 5 => (-42652569 / 1000000000000 : ℝ)
  | 6 => (-42788379 / 1000000000000 : ℝ)
  | 7 => (-42921323 / 1000000000000 : ℝ)
  | 8 => (-43051347 / 1000000000000 : ℝ)
  | 9 => (-5397299 / 125000000000 : ℝ)
  | 10 => (-43302403 / 1000000000000 : ℝ)
  | 11 => (-43423321 / 1000000000000 : ℝ)
  | 12 => (-43541087 / 1000000000000 : ℝ)
  | 13 => (-10913911 / 250000000000 : ℝ)
  | 14 => (-43766931 / 1000000000000 : ℝ)
  | 15 => (-43874889 / 1000000000000 : ℝ)
  | 16 => (-43979457 / 1000000000000 : ℝ)
  | 17 => (-1763223 / 40000000000 : ℝ)
  | 18 => (-22089091 / 500000000000 : ℝ)
  | 19 => (-8854443 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch045Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8356129 / 200000000000 : ℝ)
  | 1 => (-5241561 / 125000000000 : ℝ)
  | 2 => (-21040897 / 500000000000 : ℝ)
  | 3 => (-10557127 / 250000000000 : ℝ)
  | 4 => (-42372579 / 1000000000000 : ℝ)
  | 5 => (-850279 / 20000000000 : ℝ)
  | 6 => (-5331571 / 125000000000 : ℝ)
  | 7 => (-21394189 / 500000000000 : ℝ)
  | 8 => (-21460661 / 500000000000 : ℝ)
  | 9 => (-21525673 / 500000000000 : ℝ)
  | 10 => (-43178391 / 1000000000000 : ℝ)
  | 11 => (-21651201 / 500000000000 : ℝ)
  | 12 => (-1085583 / 25000000000 : ℝ)
  | 13 => (-21770543 / 500000000000 : ℝ)
  | 14 => (-43655643 / 1000000000000 : ℝ)
  | 15 => (-4376693 / 100000000000 : ℝ)
  | 16 => (-5484361 / 125000000000 : ℝ)
  | 17 => (-687179 / 15625000000 : ℝ)
  | 18 => (-22040287 / 500000000000 : ℝ)
  | 19 => (-44178181 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch045Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((900 : ℝ) + (j.val : ℝ)) / 1600)
      (((900 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch045Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch045Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((900 : ℝ) + (j.val : ℝ)) / 1600)
    (((900 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch045Neg45WeightLower j.val) (hpThetaShiftThreeBatch045Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch045Neg45WeightLower, hpThetaShiftThreeBatch045Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch045Neg45_integral_bounds :
    (-13096537 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-1603319 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (900 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch045Lower hpThetaJensenCellsBatch045Upper
    hpThetaShiftThreeBatch045Neg45WeightLower hpThetaShiftThreeBatch045Neg45WeightUpper hpThetaJensenCellsBatch045_bounds hpThetaShiftThreeBatch045Neg45_weight_bounds
  have hl : (-13096537 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch045Lower j * hpThetaShiftThreeBatch045Neg45WeightLower j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftThreeBatch045Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftThreeBatch045Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch045Lower j * hpThetaShiftThreeBatch045Neg45WeightUpper j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftThreeBatch045Neg45WeightUpper j) / 1600) ≤ (-1603319 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftThreeBatch045Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (900 : ℝ) / 1600 = 45 / 80 by norm_num,
    show ((900 : ℝ) + 20) / 1600 = (45 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch045Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-672153 / 62500000000 : ℝ)
  | 1 => (-1110607 / 100000000000 : ℝ)
  | 2 => (-2292173 / 200000000000 : ℝ)
  | 3 => (-11818843 / 1000000000000 : ℝ)
  | 4 => (-761251 / 62500000000 : ℝ)
  | 5 => (-6272197 / 500000000000 : ℝ)
  | 6 => (-3227997 / 250000000000 : ℝ)
  | 7 => (-13282809 / 1000000000000 : ℝ)
  | 8 => (-13656867 / 1000000000000 : ℝ)
  | 9 => (-14034173 / 1000000000000 : ℝ)
  | 10 => (-14414737 / 1000000000000 : ℝ)
  | 11 => (-1479857 / 100000000000 : ℝ)
  | 12 => (-15185681 / 1000000000000 : ℝ)
  | 13 => (-15576081 / 1000000000000 : ℝ)
  | 14 => (-798489 / 50000000000 : ℝ)
  | 15 => (-16366787 / 1000000000000 : ℝ)
  | 16 => (-16767113 / 1000000000000 : ℝ)
  | 17 => (-17170767 / 1000000000000 : ℝ)
  | 18 => (-17577759 / 1000000000000 : ℝ)
  | 19 => (-17988097 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch045Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5202993 / 500000000000 : ℝ)
  | 1 => (-10754447 / 1000000000000 : ℝ)
  | 2 => (-11106069 / 1000000000000 : ℝ)
  | 3 => (-44769 / 3906250000 : ℝ)
  | 4 => (-5909421 / 500000000000 : ℝ)
  | 5 => (-2436003 / 200000000000 : ℝ)
  | 6 => (-12544393 / 1000000000000 : ℝ)
  | 7 => (-12911987 / 1000000000000 : ℝ)
  | 8 => (-1660351 / 125000000000 : ℝ)
  | 9 => (-6828433 / 500000000000 : ℝ)
  | 10 => (-3508543 / 250000000000 : ℝ)
  | 11 => (-900921 / 62500000000 : ℝ)
  | 12 => (-14798569 / 1000000000000 : ℝ)
  | 13 => (-189821 / 12500000000 : ℝ)
  | 14 => (-194701 / 12500000000 : ℝ)
  | 15 => (-15969779 / 1000000000000 : ℝ)
  | 16 => (-8183393 / 500000000000 : ℝ)
  | 17 => (-2095889 / 125000000000 : ℝ)
  | 18 => (-8585383 / 500000000000 : ℝ)
  | 19 => (-8788879 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch045Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((900 : ℝ) + (j.val : ℝ)) / 1600)
      (((900 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch045Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch045Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((900 : ℝ) + (j.val : ℝ)) / 1600)
    (((900 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch045Neg25WeightLower j.val) (hpThetaShiftThreeBatch045Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch045Neg25WeightLower, hpThetaShiftThreeBatch045Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch045Neg25_integral_bounds :
    (-4298121 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-8218053 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (900 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch045Lower hpThetaJensenCellsBatch045Upper
    hpThetaShiftThreeBatch045Neg25WeightLower hpThetaShiftThreeBatch045Neg25WeightUpper hpThetaJensenCellsBatch045_bounds hpThetaShiftThreeBatch045Neg25_weight_bounds
  have hl : (-4298121 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch045Lower j * hpThetaShiftThreeBatch045Neg25WeightLower j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftThreeBatch045Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftThreeBatch045Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch045Lower j * hpThetaShiftThreeBatch045Neg25WeightUpper j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftThreeBatch045Neg25WeightUpper j) / 1600) ≤ (-8218053 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftThreeBatch045Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (900 : ℝ) / 1600 = 45 / 80 by norm_num,
    show ((900 : ℝ) + 20) / 1600 = (45 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch045Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch045Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch045Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch045Neg25_integral_bounds
end HodgeProofHP
