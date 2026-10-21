/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch036

/-! Exact signed weight and batch integral certificates, batch 36 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch036Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (151134835379 / 1000000000000 : ℝ)
  | 1 => (75946728353 / 500000000000 : ℝ)
  | 2 => (152640450137 / 1000000000000 : ℝ)
  | 3 => (153375510771 / 1000000000000 : ℝ)
  | 4 => (77049165043 / 500000000000 : ℝ)
  | 5 => (15480859591 / 100000000000 : ℝ)
  | 6 => (77752996197 / 500000000000 : ℝ)
  | 7 => (78095099993 / 500000000000 : ℝ)
  | 8 => (784304477 / 5000000000 : ℝ)
  | 9 => (157517751589 / 1000000000000 : ℝ)
  | 10 => (3954010943 / 25000000000 : ℝ)
  | 11 => (79394309571 / 500000000000 : ℝ)
  | 12 => (159401957359 / 1000000000000 : ℝ)
  | 13 => (80000055001 / 500000000000 : ℝ)
  | 14 => (160582730801 / 1000000000000 : ℝ)
  | 15 => (161149469553 / 1000000000000 : ℝ)
  | 16 => (161699972099 / 1000000000000 : ℝ)
  | 17 => (162233880287 / 1000000000000 : ℝ)
  | 18 => (162750831951 / 1000000000000 : ℝ)
  | 19 => (163250460877 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch036Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (151893456707 / 1000000000000 : ℝ)
  | 1 => (76320225069 / 500000000000 : ℝ)
  | 2 => (38343877693 / 250000000000 : ℝ)
  | 3 => (154098330087 / 1000000000000 : ℝ)
  | 4 => (154808595911 / 1000000000000 : ℝ)
  | 5 => (31101198479 / 200000000000 : ℝ)
  | 6 => (156190199987 / 1000000000000 : ℝ)
  | 7 => (156860895401 / 1000000000000 : ℝ)
  | 8 => (15751775159 / 100000000000 : ℝ)
  | 9 => (158160437721 / 1000000000000 : ℝ)
  | 10 => (158788619143 / 1000000000000 : ℝ)
  | 11 => (1992524467 / 12500000000 : ℝ)
  | 12 => (160000110003 / 1000000000000 : ℝ)
  | 13 => (80291365401 / 500000000000 : ℝ)
  | 14 => (80574734777 / 500000000000 : ℝ)
  | 15 => (1616999721 / 10000000000 : ℝ)
  | 16 => (5069808759 / 31250000000 : ℝ)
  | 17 => (10171926997 / 62500000000 : ℝ)
  | 18 => (81625230439 / 500000000000 : ℝ)
  | 19 => (163732396773 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch036Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((720 : ℝ) + (j.val : ℝ)) / 1600)
      (((720 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch036Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch036Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((720 : ℝ) + (j.val : ℝ)) / 1600)
    (((720 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch036Neg100WeightLower j.val) (hpThetaShiftOneBatch036Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch036Neg100WeightLower, hpThetaShiftOneBatch036Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch036Neg100_integral_bounds :
    (194564083187 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (99201074557 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (720 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch036Lower hpThetaJensenCellsBatch036Upper
    hpThetaShiftOneBatch036Neg100WeightLower hpThetaShiftOneBatch036Neg100WeightUpper hpThetaJensenCellsBatch036_bounds hpThetaShiftOneBatch036Neg100_weight_bounds
  have hl : (194564083187 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch036Lower j * hpThetaShiftOneBatch036Neg100WeightLower j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftOneBatch036Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftOneBatch036Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch036Lower j * hpThetaShiftOneBatch036Neg100WeightUpper j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftOneBatch036Neg100WeightUpper j) / 1600) ≤ (99201074557 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftOneBatch036Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (720 : ℝ) / 1600 = 36 / 80 by norm_num,
    show ((720 : ℝ) + 20) / 1600 = (36 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch036Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (37111431021 / 1000000000000 : ℝ)
  | 1 => (37948649109 / 1000000000000 : ℝ)
  | 2 => (38791888619 / 1000000000000 : ℝ)
  | 3 => (19820570167 / 500000000000 : ℝ)
  | 4 => (40496394423 / 1000000000000 : ℝ)
  | 5 => (41357640433 / 1000000000000 : ℝ)
  | 6 => (42224867283 / 1000000000000 : ℝ)
  | 7 => (8619612651 / 200000000000 : ℝ)
  | 8 => (43977215993 / 1000000000000 : ℝ)
  | 9 => (4486231249 / 100000000000 : ℝ)
  | 10 => (45753339087 / 1000000000000 : ℝ)
  | 11 => (5831285183 / 125000000000 : ℝ)
  | 12 => (47553124631 / 1000000000000 : ℝ)
  | 13 => (189304113 / 3906250000 : ℝ)
  | 14 => (49376450009 / 1000000000000 : ℝ)
  | 15 => (25148449423 / 500000000000 : ℝ)
  | 16 => (51223181711 / 1000000000000 : ℝ)
  | 17 => (52155280179 / 1000000000000 : ℝ)
  | 18 => (13273293779 / 250000000000 : ℝ)
  | 19 => (3377302917 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch036Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3794864911 / 100000000000 : ℝ)
  | 1 => (1939594431 / 50000000000 : ℝ)
  | 2 => (7928228067 / 200000000000 : ℝ)
  | 3 => (5062049303 / 125000000000 : ℝ)
  | 4 => (20678820217 / 500000000000 : ℝ)
  | 5 => (10556216821 / 250000000000 : ℝ)
  | 6 => (5387257907 / 125000000000 : ℝ)
  | 7 => (21988607997 / 500000000000 : ℝ)
  | 8 => (44862312491 / 1000000000000 : ℝ)
  | 9 => (2859583693 / 62500000000 : ℝ)
  | 10 => (9330056293 / 200000000000 : ℝ)
  | 11 => (5944140579 / 125000000000 : ℝ)
  | 12 => (48461852929 / 1000000000000 : ℝ)
  | 13 => (4937645001 / 100000000000 : ℝ)
  | 14 => (50296898847 / 1000000000000 : ℝ)
  | 15 => (3201448857 / 62500000000 : ℝ)
  | 16 => (2607764009 / 50000000000 : ℝ)
  | 17 => (53093175117 / 1000000000000 : ℝ)
  | 18 => (54036846673 / 1000000000000 : ℝ)
  | 19 => (13746568569 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch036Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((720 : ℝ) + (j.val : ℝ)) / 1600)
      (((720 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch036Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch036Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((720 : ℝ) + (j.val : ℝ)) / 1600)
    (((720 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch036Neg65WeightLower j.val) (hpThetaShiftOneBatch036Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch036Neg65WeightLower, hpThetaShiftOneBatch036Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch036Neg65_integral_bounds :
    (55860589879 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (57854732607 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (720 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch036Lower hpThetaJensenCellsBatch036Upper
    hpThetaShiftOneBatch036Neg65WeightLower hpThetaShiftOneBatch036Neg65WeightUpper hpThetaJensenCellsBatch036_bounds hpThetaShiftOneBatch036Neg65_weight_bounds
  have hl : (55860589879 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch036Lower j * hpThetaShiftOneBatch036Neg65WeightLower j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftOneBatch036Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftOneBatch036Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch036Lower j * hpThetaShiftOneBatch036Neg65WeightUpper j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftOneBatch036Neg65WeightUpper j) / 1600) ≤ (57854732607 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftOneBatch036Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (720 : ℝ) / 1600 = 36 / 80 by norm_num,
    show ((720 : ℝ) + 20) / 1600 = (36 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch036Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2544968471 / 62500000000 : ℝ)
  | 1 => (-40658596051 / 1000000000000 : ℝ)
  | 2 => (-8118894699 / 200000000000 : ℝ)
  | 3 => (-40527105101 / 1000000000000 : ℝ)
  | 4 => (-40456468099 / 1000000000000 : ℝ)
  | 5 => (-630977183 / 15625000000 : ℝ)
  | 6 => (-40305297161 / 1000000000000 : ℝ)
  | 7 => (-40224717661 / 1000000000000 : ℝ)
  | 8 => (-4014077843 / 100000000000 : ℝ)
  | 9 => (-1001336417 / 25000000000 : ℝ)
  | 10 => (-39962729627 / 1000000000000 : ℝ)
  | 11 => (-4983571811 / 125000000000 : ℝ)
  | 12 => (-248568553 / 6250000000 : ℝ)
  | 13 => (-39669888827 / 1000000000000 : ℝ)
  | 14 => (-39565312753 / 1000000000000 : ℝ)
  | 15 => (-9864304373 / 250000000000 : ℝ)
  | 16 => (-19672790141 / 500000000000 : ℝ)
  | 17 => (-39230378371 / 1000000000000 : ℝ)
  | 18 => (-39111589013 / 1000000000000 : ℝ)
  | 19 => (-1559567579 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch036Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-813171921 / 20000000000 : ℝ)
  | 1 => (-20297236747 / 500000000000 : ℝ)
  | 2 => (-405271051 / 10000000000 : ℝ)
  | 3 => (-20228234049 / 500000000000 : ℝ)
  | 4 => (-40382539711 / 1000000000000 : ℝ)
  | 5 => (-1007632429 / 25000000000 : ℝ)
  | 6 => (-2011235883 / 50000000000 : ℝ)
  | 7 => (-40140778429 / 1000000000000 : ℝ)
  | 8 => (-40053456679 / 1000000000000 : ℝ)
  | 9 => (-19981364813 / 500000000000 : ℝ)
  | 10 => (-39868574487 / 1000000000000 : ℝ)
  | 11 => (-39770968479 / 1000000000000 : ℝ)
  | 12 => (-19834944413 / 500000000000 : ℝ)
  | 13 => (-2472832047 / 62500000000 : ℝ)
  | 14 => (-39457217491 / 1000000000000 : ℝ)
  | 15 => (-39345580281 / 1000000000000 : ℝ)
  | 16 => (-3923037837 / 100000000000 : ℝ)
  | 17 => (-9777897253 / 250000000000 : ℝ)
  | 18 => (-19494594737 / 500000000000 : ℝ)
  | 19 => (-4857894629 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch036Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((720 : ℝ) + (j.val : ℝ)) / 1600)
      (((720 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch036Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch036Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((720 : ℝ) + (j.val : ℝ)) / 1600)
    (((720 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch036Neg40WeightLower j.val) (hpThetaShiftOneBatch036Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch036Neg40WeightLower, hpThetaShiftOneBatch036Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch036Neg40_integral_bounds :
    (-12540830831 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-19710832973 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (720 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch036Lower hpThetaJensenCellsBatch036Upper
    hpThetaShiftOneBatch036Neg40WeightLower hpThetaShiftOneBatch036Neg40WeightUpper hpThetaJensenCellsBatch036_bounds hpThetaShiftOneBatch036Neg40_weight_bounds
  have hl : (-12540830831 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch036Lower j * hpThetaShiftOneBatch036Neg40WeightLower j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftOneBatch036Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftOneBatch036Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch036Lower j * hpThetaShiftOneBatch036Neg40WeightUpper j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftOneBatch036Neg40WeightUpper j) / 1600) ≤ (-19710832973 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftOneBatch036Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (720 : ℝ) / 1600 = 36 / 80 by norm_num,
    show ((720 : ℝ) + 20) / 1600 = (36 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch036Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-14502901863 / 500000000000 : ℝ)
  | 1 => (-7315304957 / 250000000000 : ℝ)
  | 2 => (-1844814891 / 62500000000 : ℝ)
  | 3 => (-7443313149 / 250000000000 : ℝ)
  | 4 => (-30029856393 / 1000000000000 : ℝ)
  | 5 => (-605736863 / 20000000000 : ℝ)
  | 6 => (-7636051581 / 250000000000 : ℝ)
  | 7 => (-7700484833 / 250000000000 : ℝ)
  | 8 => (-15530017773 / 500000000000 : ℝ)
  | 9 => (-6263697659 / 200000000000 : ℝ)
  | 10 => (-31577290867 / 1000000000000 : ℝ)
  | 11 => (-31836436503 / 1000000000000 : ℝ)
  | 12 => (-6419183681 / 200000000000 : ℝ)
  | 13 => (-32355729729 / 1000000000000 : ℝ)
  | 14 => (-32615863589 / 1000000000000 : ℝ)
  | 15 => (-1027384783 / 31250000000 : ℝ)
  | 16 => (-8284267789 / 250000000000 : ℝ)
  | 17 => (-33398130873 / 1000000000000 : ℝ)
  | 18 => (-33659485149 / 1000000000000 : ℝ)
  | 19 => (-212007043 / 6250000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch036Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-7187699079 / 250000000000 : ℝ)
  | 1 => (-1160232149 / 40000000000 : ℝ)
  | 2 => (-29261219827 / 1000000000000 : ℝ)
  | 3 => (-5903407651 / 200000000000 : ℝ)
  | 4 => (-5954650519 / 200000000000 : ℝ)
  | 5 => (-3753732049 / 125000000000 : ℝ)
  | 6 => (-30286843149 / 1000000000000 : ℝ)
  | 7 => (-30544206323 / 1000000000000 : ℝ)
  | 8 => (-30801939331 / 1000000000000 : ℝ)
  | 9 => (-6212007109 / 200000000000 : ℝ)
  | 10 => (-15659244147 / 500000000000 : ℝ)
  | 11 => (-15788645433 / 500000000000 : ℝ)
  | 12 => (-15918218251 / 500000000000 : ℝ)
  | 13 => (-8023979601 / 250000000000 : ℝ)
  | 14 => (-505558277 / 15625000000 : ℝ)
  | 15 => (-8153965897 / 250000000000 : ℝ)
  | 16 => (-6575262611 / 200000000000 : ℝ)
  | 17 => (-6627414231 / 200000000000 : ℝ)
  | 18 => (-4174766359 / 125000000000 : ℝ)
  | 19 => (-8414871287 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch036Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((720 : ℝ) + (j.val : ℝ)) / 1600)
      (((720 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch036Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch036Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((720 : ℝ) + (j.val : ℝ)) / 1600)
    (((720 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch036Neg20WeightLower j.val) (hpThetaShiftOneBatch036Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch036Neg20WeightLower, hpThetaShiftOneBatch036Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch036Neg20_integral_bounds :
    (-78802577751 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (36 / 80 : ℝ) ((36 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-76950060303 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (720 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch036Lower hpThetaJensenCellsBatch036Upper
    hpThetaShiftOneBatch036Neg20WeightLower hpThetaShiftOneBatch036Neg20WeightUpper hpThetaJensenCellsBatch036_bounds hpThetaShiftOneBatch036Neg20_weight_bounds
  have hl : (-78802577751 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch036Lower j * hpThetaShiftOneBatch036Neg20WeightLower j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftOneBatch036Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftOneBatch036Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch036Lower j * hpThetaShiftOneBatch036Neg20WeightUpper j)
        (hpThetaJensenCellsBatch036Upper j * hpThetaShiftOneBatch036Neg20WeightUpper j) / 1600) ≤ (-76950060303 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch036Lower, hpThetaJensenCellsBatch036Upper,
      hpThetaShiftOneBatch036Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (720 : ℝ) / 1600 = 36 / 80 by norm_num,
    show ((720 : ℝ) + 20) / 1600 = (36 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch036Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch036Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch036Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch036Neg20_integral_bounds
end HodgeProofHP
