/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch059

/-! Exact signed weight and batch integral certificates, batch 59 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch059Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6075985457 / 1000000000000 : ℝ)
  | 1 => (-385784877 / 62500000000 : ℝ)
  | 2 => (-3135197419 / 500000000000 : ℝ)
  | 3 => (-6369509869 / 1000000000000 : ℝ)
  | 4 => (-3234958627 / 500000000000 : ℝ)
  | 5 => (-6571631253 / 1000000000000 : ℝ)
  | 6 => (-6674666261 / 1000000000000 : ℝ)
  | 7 => (-6779036809 / 1000000000000 : ℝ)
  | 8 => (-1721189391 / 250000000000 : ℝ)
  | 9 => (-6991843331 / 1000000000000 : ℝ)
  | 10 => (-7100309051 / 1000000000000 : ℝ)
  | 11 => (-7210169809 / 1000000000000 : ℝ)
  | 12 => (-1830360207 / 250000000000 : ℝ)
  | 13 => (-3717068737 / 500000000000 : ℝ)
  | 14 => (-3774137627 / 500000000000 : ℝ)
  | 15 => (-7663869823 / 1000000000000 : ℝ)
  | 16 => (-7780936979 / 1000000000000 : ℝ)
  | 17 => (-7899492667 / 1000000000000 : ℝ)
  | 18 => (-8019552979 / 1000000000000 : ℝ)
  | 19 => (-8141134157 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch059Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2990331623 / 500000000000 : ℝ)
  | 1 => (-379749091 / 62500000000 : ℝ)
  | 2 => (-6172558031 / 1000000000000 : ℝ)
  | 3 => (-6270394837 / 1000000000000 : ℝ)
  | 4 => (-1592377467 / 250000000000 : ℝ)
  | 5 => (-6469917253 / 1000000000000 : ℝ)
  | 6 => (-1642907813 / 250000000000 : ℝ)
  | 7 => (-333733313 / 50000000000 : ℝ)
  | 8 => (-847379601 / 125000000000 : ℝ)
  | 9 => (-6884757563 / 1000000000000 : ℝ)
  | 10 => (-699184333 / 100000000000 : ℝ)
  | 11 => (-142006181 / 20000000000 : ℝ)
  | 12 => (-450635613 / 62500000000 : ℝ)
  | 13 => (-7321440827 / 1000000000000 : ℝ)
  | 14 => (-7434137473 / 1000000000000 : ℝ)
  | 15 => (-7548275253 / 1000000000000 : ℝ)
  | 16 => (-3831934911 / 500000000000 : ℝ)
  | 17 => (-3890468489 / 500000000000 : ℝ)
  | 18 => (-3949746333 / 500000000000 : ℝ)
  | 19 => (-4009776489 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch059Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1180 : ℝ) + (j.val : ℝ)) / 1600)
      (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch059Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch059Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1180 : ℝ) + (j.val : ℝ)) / 1600)
    (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch059Neg100WeightLower j.val) (hpThetaShiftThreeBatch059Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch059Neg100WeightLower, hpThetaShiftThreeBatch059Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch059Neg100_integral_bounds :
    (-81569503 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-156993297 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch059Lower hpThetaJensenCellsBatch059Upper
    hpThetaShiftThreeBatch059Neg100WeightLower hpThetaShiftThreeBatch059Neg100WeightUpper hpThetaJensenCellsBatch059_bounds hpThetaShiftThreeBatch059Neg100_weight_bounds
  have hl : (-81569503 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch059Lower j * hpThetaShiftThreeBatch059Neg100WeightLower j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftThreeBatch059Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftThreeBatch059Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch059Lower j * hpThetaShiftThreeBatch059Neg100WeightUpper j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftThreeBatch059Neg100WeightUpper j) / 1600) ≤ (-156993297 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftThreeBatch059Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1180 : ℝ) / 1600 = 59 / 80 by norm_num,
    show ((1180 : ℝ) + 20) / 1600 = (59 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch059Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (23140563 / 125000000000 : ℝ)
  | 1 => (8892541 / 50000000000 : ℝ)
  | 2 => (34078151 / 200000000000 : ℝ)
  | 3 => (162741509 / 1000000000000 : ℝ)
  | 4 => (19362531 / 125000000000 : ℝ)
  | 5 => (146864107 / 1000000000000 : ℝ)
  | 6 => (34657547 / 250000000000 : ℝ)
  | 7 => (130195563 / 1000000000000 : ℝ)
  | 8 => (121557267 / 1000000000000 : ℝ)
  | 9 => (22542461 / 200000000000 : ℝ)
  | 10 => (6478603 / 62500000000 : ℝ)
  | 11 => (94390231 / 1000000000000 : ℝ)
  | 12 => (42453479 / 500000000000 : ℝ)
  | 13 => (75204697 / 1000000000000 : ℝ)
  | 14 => (65280281 / 1000000000000 : ℝ)
  | 15 => (13782627 / 250000000000 : ℝ)
  | 16 => (44752143 / 1000000000000 : ℝ)
  | 17 => (4267739 / 125000000000 : ℝ)
  | 18 => (5824127 / 250000000000 : ℝ)
  | 19 => (2442517 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch059Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (192214579 / 1000000000000 : ℝ)
  | 1 => (37024901 / 200000000000 : ℝ)
  | 2 => (177850821 / 1000000000000 : ℝ)
  | 3 => (42597689 / 250000000000 : ℝ)
  | 4 => (16274151 / 100000000000 : ℝ)
  | 5 => (154900249 / 1000000000000 : ℝ)
  | 6 => (36716027 / 250000000000 : ℝ)
  | 7 => (138630189 / 1000000000000 : ℝ)
  | 8 => (32548891 / 250000000000 : ℝ)
  | 9 => (30389317 / 250000000000 : ℝ)
  | 10 => (56356153 / 500000000000 : ℝ)
  | 11 => (103657649 / 1000000000000 : ℝ)
  | 12 => (11798779 / 125000000000 : ℝ)
  | 13 => (84906959 / 1000000000000 : ℝ)
  | 14 => (37602349 / 500000000000 : ℝ)
  | 15 => (32640141 / 500000000000 : ℝ)
  | 16 => (55130509 / 1000000000000 : ℝ)
  | 17 => (2797009 / 62500000000 : ℝ)
  | 18 => (34141913 / 1000000000000 : ℝ)
  | 19 => (23296509 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch059Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1180 : ℝ) + (j.val : ℝ)) / 1600)
      (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch059Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch059Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1180 : ℝ) + (j.val : ℝ)) / 1600)
    (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch059Neg70WeightLower j.val) (hpThetaShiftThreeBatch059Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch059Neg70WeightLower, hpThetaShiftThreeBatch059Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch059Neg70_integral_bounds :
    (77421 / 31250000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (1370899 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch059Lower hpThetaJensenCellsBatch059Upper
    hpThetaShiftThreeBatch059Neg70WeightLower hpThetaShiftThreeBatch059Neg70WeightUpper hpThetaJensenCellsBatch059_bounds hpThetaShiftThreeBatch059Neg70_weight_bounds
  have hl : (77421 / 31250000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch059Lower j * hpThetaShiftThreeBatch059Neg70WeightLower j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftThreeBatch059Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftThreeBatch059Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch059Lower j * hpThetaShiftThreeBatch059Neg70WeightUpper j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftThreeBatch059Neg70WeightUpper j) / 1600) ≤ (1370899 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftThreeBatch059Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1180 : ℝ) / 1600 = 59 / 80 by norm_num,
    show ((1180 : ℝ) + 20) / 1600 = (59 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch059Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (81170767 / 250000000000 : ℝ)
  | 1 => (164406161 / 500000000000 : ℝ)
  | 2 => (166484769 / 500000000000 : ℝ)
  | 3 => (42144339 / 125000000000 : ℝ)
  | 4 => (341367839 / 1000000000000 : ℝ)
  | 5 => (345608911 / 1000000000000 : ℝ)
  | 6 => (69975583 / 200000000000 : ℝ)
  | 7 => (177087419 / 500000000000 : ℝ)
  | 8 => (358499663 / 1000000000000 : ℝ)
  | 9 => (362852369 / 1000000000000 : ℝ)
  | 10 => (91808233 / 250000000000 : ℝ)
  | 11 => (185820663 / 500000000000 : ℝ)
  | 12 => (188038761 / 500000000000 : ℝ)
  | 13 => (190270743 / 500000000000 : ℝ)
  | 14 => (192516591 / 500000000000 : ℝ)
  | 15 => (97388143 / 250000000000 : ℝ)
  | 16 => (394099613 / 1000000000000 : ℝ)
  | 17 => (398674257 / 1000000000000 : ℝ)
  | 18 => (50409557 / 125000000000 : ℝ)
  | 19 => (203953079 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch059Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (328812323 / 1000000000000 : ℝ)
  | 1 => (332969539 / 1000000000000 : ℝ)
  | 2 => (337154713 / 1000000000000 : ℝ)
  | 3 => (2133549 / 6250000000 : ℝ)
  | 4 => (21600557 / 62500000000 : ℝ)
  | 5 => (87469479 / 250000000000 : ℝ)
  | 6 => (354174839 / 1000000000000 : ℝ)
  | 7 => (22406229 / 62500000000 : ℝ)
  | 8 => (36285237 / 100000000000 : ℝ)
  | 9 => (367232933 / 1000000000000 : ℝ)
  | 10 => (371641327 / 1000000000000 : ℝ)
  | 11 => (376077523 / 1000000000000 : ℝ)
  | 12 => (380541487 / 1000000000000 : ℝ)
  | 13 => (385033183 / 1000000000000 : ℝ)
  | 14 => (389552573 / 1000000000000 : ℝ)
  | 15 => (197049807 / 500000000000 : ℝ)
  | 16 => (199337129 / 500000000000 : ℝ)
  | 17 => (403276457 / 1000000000000 : ℝ)
  | 18 => (407906159 / 1000000000000 : ℝ)
  | 19 => (82512661 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch059Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1180 : ℝ) + (j.val : ℝ)) / 1600)
      (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch059Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch059Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1180 : ℝ) + (j.val : ℝ)) / 1600)
    (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch059Neg45WeightLower j.val) (hpThetaShiftThreeBatch059Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch059Neg45WeightLower, hpThetaShiftThreeBatch059Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch059Neg45_integral_bounds :
    (13211 / 1600000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (171013 / 20000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch059Lower hpThetaJensenCellsBatch059Upper
    hpThetaShiftThreeBatch059Neg45WeightLower hpThetaShiftThreeBatch059Neg45WeightUpper hpThetaJensenCellsBatch059_bounds hpThetaShiftThreeBatch059Neg45_weight_bounds
  have hl : (13211 / 1600000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch059Lower j * hpThetaShiftThreeBatch059Neg45WeightLower j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftThreeBatch059Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftThreeBatch059Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch059Lower j * hpThetaShiftThreeBatch059Neg45WeightUpper j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftThreeBatch059Neg45WeightUpper j) / 1600) ≤ (171013 / 20000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftThreeBatch059Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1180 : ℝ) / 1600 = 59 / 80 by norm_num,
    show ((1180 : ℝ) + 20) / 1600 = (59 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch059Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-223598629 / 1000000000000 : ℝ)
  | 1 => (-56108219 / 250000000000 : ℝ)
  | 2 => (-14078877 / 62500000000 : ℝ)
  | 3 => (-226085989 / 1000000000000 : ℝ)
  | 4 => (-113452321 / 500000000000 : ℝ)
  | 5 => (-113858941 / 500000000000 : ℝ)
  | 6 => (-228525603 / 1000000000000 : ℝ)
  | 7 => (-114663847 / 500000000000 : ℝ)
  | 8 => (-46024809 / 200000000000 : ℝ)
  | 9 => (-230914547 / 1000000000000 : ℝ)
  | 10 => (-115849543 / 500000000000 : ℝ)
  | 11 => (-14529847 / 62500000000 : ℝ)
  | 12 => (-23324983 / 100000000000 : ℝ)
  | 13 => (-117007903 / 500000000000 : ℝ)
  | 14 => (-46955073 / 200000000000 : ℝ)
  | 15 => (-235528393 / 1000000000000 : ℝ)
  | 16 => (-236274771 / 1000000000000 : ℝ)
  | 17 => (-118507191 / 500000000000 : ℝ)
  | 18 => (-237747109 / 1000000000000 : ℝ)
  | 19 => (-238472831 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch059Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-222759393 / 1000000000000 : ℝ)
  | 1 => (-55899657 / 250000000000 : ℝ)
  | 2 => (-1795463 / 8000000000 : ℝ)
  | 3 => (-225262031 / 1000000000000 : ℝ)
  | 4 => (-56521497 / 250000000000 : ℝ)
  | 5 => (-226904641 / 1000000000000 : ℝ)
  | 6 => (-227717881 / 1000000000000 : ℝ)
  | 7 => (-114262801 / 500000000000 : ℝ)
  | 8 => (-229327693 / 1000000000000 : ℝ)
  | 9 => (-57531011 / 250000000000 : ℝ)
  | 10 => (-115457273 / 500000000000 : ℝ)
  | 11 => (-46339817 / 200000000000 : ℝ)
  | 12 => (-232477551 / 1000000000000 : ℝ)
  | 13 => (-233249829 / 1000000000000 : ℝ)
  | 14 => (-46803161 / 200000000000 : ℝ)
  | 15 => (-58693841 / 250000000000 : ℝ)
  | 16 => (-29441049 / 125000000000 : ℝ)
  | 17 => (-23627477 / 100000000000 : ℝ)
  | 18 => (-237014381 / 1000000000000 : ℝ)
  | 19 => (-59436777 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch059Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1180 : ℝ) + (j.val : ℝ)) / 1600)
      (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch059Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch059Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1180 : ℝ) + (j.val : ℝ)) / 1600)
    (((1180 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch059Neg25WeightLower j.val) (hpThetaShiftThreeBatch059Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch059Neg25WeightLower, hpThetaShiftThreeBatch059Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch059Neg25_integral_bounds :
    (-5366579 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (59 / 80 : ℝ) ((59 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-1045357 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1180 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch059Lower hpThetaJensenCellsBatch059Upper
    hpThetaShiftThreeBatch059Neg25WeightLower hpThetaShiftThreeBatch059Neg25WeightUpper hpThetaJensenCellsBatch059_bounds hpThetaShiftThreeBatch059Neg25_weight_bounds
  have hl : (-5366579 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch059Lower j * hpThetaShiftThreeBatch059Neg25WeightLower j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftThreeBatch059Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftThreeBatch059Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch059Lower j * hpThetaShiftThreeBatch059Neg25WeightUpper j)
        (hpThetaJensenCellsBatch059Upper j * hpThetaShiftThreeBatch059Neg25WeightUpper j) / 1600) ≤ (-1045357 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch059Lower, hpThetaJensenCellsBatch059Upper,
      hpThetaShiftThreeBatch059Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1180 : ℝ) / 1600 = 59 / 80 by norm_num,
    show ((1180 : ℝ) + 20) / 1600 = (59 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch059Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch059Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch059Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch059Neg25_integral_bounds
end HodgeProofHP
