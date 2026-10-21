/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch070

/-! Exact signed weight and batch integral certificates, batch 70 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch070Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-10045719581 / 100000000000 : ℝ)
  | 1 => (-25384472513 / 250000000000 : ℝ)
  | 2 => (-12828607001 / 125000000000 : ℝ)
  | 3 => (-103730179751 / 1000000000000 : ℝ)
  | 4 => (-52420973993 / 500000000000 : ℝ)
  | 5 => (-105964248057 / 1000000000000 : ℝ)
  | 6 => (-13387145993 / 125000000000 : ℝ)
  | 7 => (-4329631851 / 40000000000 : ℝ)
  | 8 => (-4375808893 / 40000000000 : ℝ)
  | 9 => (-55280268011 / 500000000000 : ℝ)
  | 10 => (-111736827951 / 1000000000000 : ℝ)
  | 11 => (-112924189359 / 1000000000000 : ℝ)
  | 12 => (-114122712157 / 1000000000000 : ℝ)
  | 13 => (-28833122231 / 250000000000 : ℝ)
  | 14 => (-29138403229 / 250000000000 : ℝ)
  | 15 => (-23557235613 / 200000000000 : ℝ)
  | 16 => (-23806055797 / 200000000000 : ℝ)
  | 17 => (-60143005489 / 500000000000 : ℝ)
  | 18 => (-24310694007 / 200000000000 : ℝ)
  | 19 => (-122832752843 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch070Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-24846671959 / 250000000000 : ℝ)
  | 1 => (-100457195809 / 1000000000000 : ℝ)
  | 2 => (-101537890051 / 1000000000000 : ℝ)
  | 3 => (-102628856007 / 1000000000000 : ℝ)
  | 4 => (-414920719 / 4000000000 : ℝ)
  | 5 => (-20968389597 / 200000000000 : ℝ)
  | 6 => (-13245531007 / 125000000000 : ℝ)
  | 7 => (-107097167943 / 1000000000000 : ℝ)
  | 8 => (-54120398137 / 500000000000 : ℝ)
  | 9 => (-27348805581 / 250000000000 : ℝ)
  | 10 => (-110560536021 / 1000000000000 : ℝ)
  | 11 => (-2234736559 / 20000000000 : ℝ)
  | 12 => (-56462094679 / 500000000000 : ℝ)
  | 13 => (-28530678039 / 250000000000 : ℝ)
  | 14 => (-115332488923 / 1000000000000 : ℝ)
  | 15 => (-23310722583 / 200000000000 : ℝ)
  | 16 => (-7361636129 / 62500000000 : ℝ)
  | 17 => (-14878784873 / 125000000000 : ℝ)
  | 18 => (-120286010977 / 1000000000000 : ℝ)
  | 19 => (-60776735017 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch070Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1400 : ℝ) + (j.val : ℝ)) / 1600)
      (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch070Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch070Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1400 : ℝ) + (j.val : ℝ)) / 1600)
    (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch070Neg100WeightLower j.val) (hpThetaShiftThreeBatch070Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch070Neg100WeightLower, hpThetaShiftThreeBatch070Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch070Neg100_integral_bounds :
    (-6056123 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-29121491 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch070Lower hpThetaJensenCellsBatch070Upper
    hpThetaShiftThreeBatch070Neg100WeightLower hpThetaShiftThreeBatch070Neg100WeightUpper hpThetaJensenCellsBatch070_bounds hpThetaShiftThreeBatch070Neg100_weight_bounds
  have hl : (-6056123 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch070Lower j * hpThetaShiftThreeBatch070Neg100WeightLower j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftThreeBatch070Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftThreeBatch070Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch070Lower j * hpThetaShiftThreeBatch070Neg100WeightUpper j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftThreeBatch070Neg100WeightUpper j) / 1600) ≤ (-29121491 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftThreeBatch070Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1400 : ℝ) / 1600 = 70 / 80 by norm_num,
    show ((1400 : ℝ) + 20) / 1600 = (70 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch070Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-7689780063 / 500000000000 : ℝ)
  | 1 => (-7794536729 / 500000000000 : ℝ)
  | 2 => (-7900460751 / 500000000000 : ℝ)
  | 3 => (-3203025237 / 200000000000 : ℝ)
  | 4 => (-16231709611 / 1000000000000 : ℝ)
  | 5 => (-16450694059 / 1000000000000 : ℝ)
  | 6 => (-16672101989 / 1000000000000 : ℝ)
  | 7 => (-4223989009 / 250000000000 : ℝ)
  | 8 => (-17122279017 / 1000000000000 : ℝ)
  | 9 => (-1735109393 / 100000000000 : ℝ)
  | 10 => (-17582423957 / 1000000000000 : ℝ)
  | 11 => (-8908146231 / 500000000000 : ℝ)
  | 12 => (-9026361497 / 500000000000 : ℝ)
  | 13 => (-1829173929 / 100000000000 : ℝ)
  | 14 => (-2316670659 / 125000000000 : ℝ)
  | 15 => (-3755525011 / 200000000000 : ℝ)
  | 16 => (-19024542939 / 1000000000000 : ℝ)
  | 17 => (-19274143419 / 1000000000000 : ℝ)
  | 18 => (-9763225591 / 500000000000 : ℝ)
  | 19 => (-4945372777 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch070Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-60689439 / 4000000000 : ℝ)
  | 1 => (-123036481 / 8000000000 : ℝ)
  | 2 => (-15589073457 / 1000000000000 : ℝ)
  | 3 => (-15800921501 / 1000000000000 : ℝ)
  | 4 => (-2001890773 / 125000000000 : ℝ)
  | 5 => (-1623170961 / 100000000000 : ℝ)
  | 6 => (-8225347029 / 500000000000 : ℝ)
  | 7 => (-4168025497 / 250000000000 : ℝ)
  | 8 => (-3379191207 / 200000000000 : ℝ)
  | 9 => (-2140284877 / 125000000000 : ℝ)
  | 10 => (-17351093929 / 1000000000000 : ℝ)
  | 11 => (-4395605989 / 250000000000 : ℝ)
  | 12 => (-17816292461 / 1000000000000 : ℝ)
  | 13 => (-18052722993 / 1000000000000 : ℝ)
  | 14 => (-18291739289 / 1000000000000 : ℝ)
  | 15 => (-18533365271 / 1000000000000 : ℝ)
  | 16 => (-9388812527 / 500000000000 : ℝ)
  | 17 => (-9512271469 / 500000000000 : ℝ)
  | 18 => (-9637071709 / 500000000000 : ℝ)
  | 19 => (-19526451181 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch070Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1400 : ℝ) + (j.val : ℝ)) / 1600)
      (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch070Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch070Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1400 : ℝ) + (j.val : ℝ)) / 1600)
    (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch070Neg70WeightLower j.val) (hpThetaShiftThreeBatch070Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch070Neg70WeightLower, hpThetaShiftThreeBatch070Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch070Neg70_integral_bounds :
    (-9507411 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-2279753 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch070Lower hpThetaJensenCellsBatch070Upper
    hpThetaShiftThreeBatch070Neg70WeightLower hpThetaShiftThreeBatch070Neg70WeightUpper hpThetaJensenCellsBatch070_bounds hpThetaShiftThreeBatch070Neg70_weight_bounds
  have hl : (-9507411 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch070Lower j * hpThetaShiftThreeBatch070Neg70WeightLower j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftThreeBatch070Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftThreeBatch070Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch070Lower j * hpThetaShiftThreeBatch070Neg70WeightUpper j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftThreeBatch070Neg70WeightUpper j) / 1600) ≤ (-2279753 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftThreeBatch070Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1400 : ℝ) / 1600 = 70 / 80 by norm_num,
    show ((1400 : ℝ) + 20) / 1600 = (70 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch070Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (694562297 / 500000000000 : ℝ)
  | 1 => (694076147 / 500000000000 : ℝ)
  | 2 => (1387011817 / 1000000000000 : ℝ)
  | 3 => (1385700471 / 1000000000000 : ℝ)
  | 4 => (1384215537 / 1000000000000 : ℝ)
  | 5 => (691277133 / 500000000000 : ℝ)
  | 6 => (34517847 / 25000000000 : ℝ)
  | 7 => (689345787 / 500000000000 : ℝ)
  | 8 => (137648451 / 100000000000 : ℝ)
  | 9 => (54963593 / 40000000000 : ℝ)
  | 10 => (685752311 / 500000000000 : ℝ)
  | 11 => (1368725977 / 1000000000000 : ℝ)
  | 12 => (682875467 / 500000000000 : ℝ)
  | 13 => (340644127 / 250000000000 : ℝ)
  | 14 => (1359199681 / 1000000000000 : ℝ)
  | 15 => (677808703 / 500000000000 : ℝ)
  | 16 => (337956651 / 250000000000 : ℝ)
  | 17 => (336956041 / 250000000000 : ℝ)
  | 18 => (671803473 / 500000000000 : ℝ)
  | 19 => (1339171773 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch070Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1389931381 / 1000000000000 : ℝ)
  | 1 => (277824919 / 200000000000 : ℝ)
  | 2 => (277630459 / 200000000000 : ℝ)
  | 3 => (693505909 / 500000000000 : ℝ)
  | 4 => (173212559 / 125000000000 : ℝ)
  | 5 => (692107769 / 500000000000 : ℝ)
  | 6 => (1382554267 / 1000000000000 : ℝ)
  | 7 => (1380713881 / 1000000000000 : ℝ)
  | 8 => (55147663 / 40000000000 : ℝ)
  | 9 => (1376484511 / 1000000000000 : ℝ)
  | 10 => (687044913 / 500000000000 : ℝ)
  | 11 => (1371504623 / 1000000000000 : ℝ)
  | 12 => (684362989 / 500000000000 : ℝ)
  | 13 => (273150187 / 200000000000 : ℝ)
  | 14 => (1362576509 / 1000000000000 : ℝ)
  | 15 => (679599841 / 500000000000 : ℝ)
  | 16 => (1355617407 / 1000000000000 : ℝ)
  | 17 => (270365321 / 200000000000 : ℝ)
  | 18 => (269564833 / 200000000000 : ℝ)
  | 19 => (1343606947 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch070Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1400 : ℝ) + (j.val : ℝ)) / 1600)
      (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch070Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch070Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1400 : ℝ) + (j.val : ℝ)) / 1600)
    (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch070Neg45WeightLower j.val) (hpThetaShiftThreeBatch070Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch070Neg45WeightLower, hpThetaShiftThreeBatch070Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch070Neg45_integral_bounds :
    (730169 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (23517 / 31250000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch070Lower hpThetaJensenCellsBatch070Upper
    hpThetaShiftThreeBatch070Neg45WeightLower hpThetaShiftThreeBatch070Neg45WeightUpper hpThetaJensenCellsBatch070_bounds hpThetaShiftThreeBatch070Neg45_weight_bounds
  have hl : (730169 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch070Lower j * hpThetaShiftThreeBatch070Neg45WeightLower j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftThreeBatch070Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftThreeBatch070Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch070Lower j * hpThetaShiftThreeBatch070Neg45WeightUpper j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftThreeBatch070Neg45WeightUpper j) / 1600) ≤ (23517 / 31250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftThreeBatch070Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1400 : ℝ) / 1600 = 70 / 80 by norm_num,
    show ((1400 : ℝ) + 20) / 1600 = (70 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch070Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-18549153 / 1000000000000 : ℝ)
  | 1 => (-14186611 / 1000000000000 : ℝ)
  | 2 => (-1221799 / 125000000000 : ℝ)
  | 3 => (-2656103 / 500000000000 : ℝ)
  | 4 => (-399881 / 500000000000 : ℝ)
  | 5 => (3763231 / 1000000000000 : ℝ)
  | 6 => (1047133 / 125000000000 : ℝ)
  | 7 => (13042029 / 1000000000000 : ℝ)
  | 8 => (17758419 / 1000000000000 : ℝ)
  | 9 => (901061 / 40000000000 : ℝ)
  | 10 => (341833 / 12500000000 : ℝ)
  | 11 => (16109529 / 500000000000 : ℝ)
  | 12 => (4643009 / 125000000000 : ℝ)
  | 13 => (1684879 / 40000000000 : ℝ)
  | 14 => (47153061 / 1000000000000 : ℝ)
  | 15 => (417901 / 8000000000 : ℝ)
  | 16 => (28687981 / 500000000000 : ℝ)
  | 17 => (12513673 / 200000000000 : ℝ)
  | 18 => (67815129 / 1000000000000 : ℝ)
  | 19 => (73116551 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch070Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1418661 / 100000000000 : ℝ)
  | 1 => (-9774391 / 1000000000000 : ℝ)
  | 2 => (-1062441 / 200000000000 : ℝ)
  | 3 => (-799761 / 1000000000000 : ℝ)
  | 4 => (117601 / 31250000000 : ℝ)
  | 5 => (1675413 / 200000000000 : ℝ)
  | 6 => (1304203 / 100000000000 : ℝ)
  | 7 => (887921 / 50000000000 : ℝ)
  | 8 => (11263263 / 500000000000 : ℝ)
  | 9 => (27346641 / 1000000000000 : ℝ)
  | 10 => (32219059 / 1000000000000 : ℝ)
  | 11 => (37144073 / 1000000000000 : ℝ)
  | 12 => (5265247 / 125000000000 : ℝ)
  | 13 => (23576531 / 500000000000 : ℝ)
  | 14 => (26118813 / 500000000000 : ℝ)
  | 15 => (57375963 / 1000000000000 : ℝ)
  | 16 => (31284183 / 500000000000 : ℝ)
  | 17 => (6781513 / 100000000000 : ℝ)
  | 18 => (9139569 / 125000000000 : ℝ)
  | 19 => (3138917 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch070Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1400 : ℝ) + (j.val : ℝ)) / 1600)
      (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch070Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch070Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1400 : ℝ) + (j.val : ℝ)) / 1600)
    (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch070Neg25WeightLower j.val) (hpThetaShiftThreeBatch070Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch070Neg25WeightLower, hpThetaShiftThreeBatch070Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch070Neg25_integral_bounds :
    (5997 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (15053 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch070Lower hpThetaJensenCellsBatch070Upper
    hpThetaShiftThreeBatch070Neg25WeightLower hpThetaShiftThreeBatch070Neg25WeightUpper hpThetaJensenCellsBatch070_bounds hpThetaShiftThreeBatch070Neg25_weight_bounds
  have hl : (5997 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch070Lower j * hpThetaShiftThreeBatch070Neg25WeightLower j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftThreeBatch070Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftThreeBatch070Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch070Lower j * hpThetaShiftThreeBatch070Neg25WeightUpper j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftThreeBatch070Neg25WeightUpper j) / 1600) ≤ (15053 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftThreeBatch070Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1400 : ℝ) / 1600 = 70 / 80 by norm_num,
    show ((1400 : ℝ) + 20) / 1600 = (70 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch070Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch070Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch070Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch070Neg25_integral_bounds
end HodgeProofHP
