/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch064

/-! Exact signed weight and batch integral certificates, batch 64 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch064Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-44597979368129 / 1000000000000 : ℝ)
  | 1 => (-44949878125203 / 1000000000000 : ℝ)
  | 2 => (-45304089671721 / 1000000000000 : ℝ)
  | 3 => (-4566062650997 / 100000000000 : ℝ)
  | 4 => (-23009750598291 / 500000000000 : ℝ)
  | 5 => (-23190363171363 / 500000000000 : ℝ)
  | 6 => (-46744314614283 / 1000000000000 : ℝ)
  | 7 => (-47110278732039 / 1000000000000 : ℝ)
  | 8 => (-47478631471859 / 1000000000000 : ℝ)
  | 9 => (-47849385664881 / 1000000000000 : ℝ)
  | 10 => (-48222554197699 / 1000000000000 : ℝ)
  | 11 => (-379673046973 / 7812500000 : ℝ)
  | 12 => (-48976186107477 / 1000000000000 : ℝ)
  | 13 => (-49356675536573 / 1000000000000 : ℝ)
  | 14 => (-24869815705053 / 500000000000 : ℝ)
  | 15 => (-50125066894741 / 1000000000000 : ℝ)
  | 16 => (-50512995213719 / 1000000000000 : ℝ)
  | 17 => (-25451714823523 / 500000000000 : ℝ)
  | 18 => (-12824095882921 / 250000000000 : ℝ)
  | 19 => (-25845935130869 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch064Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2212419047619 / 50000000000 : ℝ)
  | 1 => (-696843427627 / 15625000000 : ℝ)
  | 2 => (-22474939062601 / 500000000000 : ℝ)
  | 3 => (-1132602241793 / 25000000000 : ℝ)
  | 4 => (-45660626509969 / 1000000000000 : ℝ)
  | 5 => (-46019501196581 / 1000000000000 : ℝ)
  | 6 => (-1855229053709 / 40000000000 : ℝ)
  | 7 => (-23372157307141 / 500000000000 : ℝ)
  | 8 => (-23555139366019 / 500000000000 : ℝ)
  | 9 => (-23739315735929 / 500000000000 : ℝ)
  | 10 => (-598117320811 / 12500000000 : ℝ)
  | 11 => (-24111277098849 / 500000000000 : ℝ)
  | 12 => (-48598150012543 / 1000000000000 : ℝ)
  | 13 => (-12244046526869 / 250000000000 : ℝ)
  | 14 => (-12339168884143 / 250000000000 : ℝ)
  | 15 => (-9947926282021 / 200000000000 : ℝ)
  | 16 => (-2506253344737 / 50000000000 : ℝ)
  | 17 => (-25256497606859 / 500000000000 : ℝ)
  | 18 => (-10180685929409 / 200000000000 : ℝ)
  | 19 => (-51296383531683 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch064Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1280 : ℝ) + (j.val : ℝ)) / 1600)
      (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch064Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch064Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1280 : ℝ) + (j.val : ℝ)) / 1600)
    (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch064Neg100WeightLower j.val) (hpThetaShiftOneBatch064Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch064Neg100WeightLower, hpThetaShiftOneBatch064Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch064Neg100_integral_bounds :
    (-117664552197 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-227679629643 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch064Lower hpThetaJensenCellsBatch064Upper
    hpThetaShiftOneBatch064Neg100WeightLower hpThetaShiftOneBatch064Neg100WeightUpper hpThetaJensenCellsBatch064_bounds hpThetaShiftOneBatch064Neg100_weight_bounds
  have hl : (-117664552197 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch064Lower j * hpThetaShiftOneBatch064Neg100WeightLower j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftOneBatch064Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftOneBatch064Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch064Lower j * hpThetaShiftOneBatch064Neg100WeightUpper j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftOneBatch064Neg100WeightUpper j) / 1600) ≤ (-227679629643 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftOneBatch064Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1280 : ℝ) / 1600 = 64 / 80 by norm_num,
    show ((1280 : ℝ) + 20) / 1600 = (64 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch064Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6134451321217 / 1000000000000 : ℝ)
  | 1 => (-3098544331559 / 500000000000 : ℝ)
  | 2 => (-6260210550873 / 1000000000000 : ℝ)
  | 3 => (-6323819904209 / 1000000000000 : ℝ)
  | 4 => (-6387919656509 / 1000000000000 : ℝ)
  | 5 => (-3226256377429 / 500000000000 : ℝ)
  | 6 => (-1629400540023 / 250000000000 : ℝ)
  | 7 => (-6583190846847 / 1000000000000 : ℝ)
  | 8 => (-1329856360721 / 200000000000 : ℝ)
  | 9 => (-3357939016373 / 500000000000 : ℝ)
  | 10 => (-3391491275299 / 500000000000 : ℝ)
  | 11 => (-6850598387479 / 1000000000000 : ℝ)
  | 12 => (-1383745717551 / 200000000000 : ℝ)
  | 13 => (-3493688104941 / 500000000000 : ℝ)
  | 14 => (-352827216323 / 50000000000 : ℝ)
  | 15 => (-178155900607 / 25000000000 : ℝ)
  | 16 => (-7196454404377 / 1000000000000 : ℝ)
  | 17 => (-7267202582073 / 1000000000000 : ℝ)
  | 18 => (-3669241843517 / 500000000000 : ℝ)
  | 19 => (-3705150431659 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch064Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6072295619047 / 1000000000000 : ℝ)
  | 1 => (-47925400947 / 7812500000 : ℝ)
  | 2 => (-6197088663117 / 1000000000000 : ℝ)
  | 3 => (-782526318859 / 125000000000 : ℝ)
  | 4 => (-395238744013 / 62500000000 : ℝ)
  | 5 => (-1596979914127 / 250000000000 : ℝ)
  | 6 => (-6452512754857 / 1000000000000 : ℝ)
  | 7 => (-6517602160091 / 1000000000000 : ℝ)
  | 8 => (-3291595423423 / 500000000000 : ℝ)
  | 9 => (-1662320450901 / 250000000000 : ℝ)
  | 10 => (-1343175606549 / 200000000000 : ℝ)
  | 11 => (-6782982550597 / 1000000000000 : ℝ)
  | 12 => (-3425299193739 / 500000000000 : ℝ)
  | 13 => (-3459364293877 / 500000000000 : ℝ)
  | 14 => (-6987376209881 / 1000000000000 : ℝ)
  | 15 => (-7056544326459 / 1000000000000 : ℝ)
  | 16 => (-7126236024279 / 1000000000000 : ℝ)
  | 17 => (-899556800547 / 125000000000 : ℝ)
  | 18 => (-908400322759 / 125000000000 : ℝ)
  | 19 => (-7338483687033 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch064Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1280 : ℝ) + (j.val : ℝ)) / 1600)
      (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch064Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch064Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1280 : ℝ) + (j.val : ℝ)) / 1600)
    (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch064Neg65WeightLower j.val) (hpThetaShiftOneBatch064Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch064Neg65WeightLower, hpThetaShiftOneBatch064Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch064Neg65_integral_bounds :
    (-206495663 / 6250000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-7973881611 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch064Lower hpThetaJensenCellsBatch064Upper
    hpThetaShiftOneBatch064Neg65WeightLower hpThetaShiftOneBatch064Neg65WeightUpper hpThetaJensenCellsBatch064_bounds hpThetaShiftOneBatch064Neg65_weight_bounds
  have hl : (-206495663 / 6250000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch064Lower j * hpThetaShiftOneBatch064Neg65WeightLower j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftOneBatch064Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftOneBatch064Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch064Lower j * hpThetaShiftOneBatch064Neg65WeightUpper j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftOneBatch064Neg65WeightUpper j) / 1600) ≤ (-7973881611 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftOneBatch064Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1280 : ℝ) / 1600 = 64 / 80 by norm_num,
    show ((1280 : ℝ) + 20) / 1600 = (64 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch064Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (315317756723 / 1000000000000 : ℝ)
  | 1 => (312139359279 / 1000000000000 : ℝ)
  | 2 => (308903951881 / 1000000000000 : ℝ)
  | 3 => (61122211409 / 200000000000 : ℝ)
  | 4 => (4722815541 / 15625000000 : ℝ)
  | 5 => (149425440901 / 500000000000 : ℝ)
  | 6 => (147691316539 / 500000000000 : ℝ)
  | 7 => (291854960259 / 1000000000000 : ℝ)
  | 8 => (288267372451 / 1000000000000 : ℝ)
  | 9 => (142309688021 / 500000000000 : ℝ)
  | 10 => (2809104747 / 10000000000 : ℝ)
  | 11 => (277140169357 / 1000000000000 : ℝ)
  | 12 => (273307958197 / 1000000000000 : ℝ)
  | 13 => (67353334163 / 250000000000 : ℝ)
  | 14 => (33181974673 / 125000000000 : ℝ)
  | 15 => (6535870757 / 25000000000 : ℝ)
  | 16 => (128674961219 / 500000000000 : ℝ)
  | 17 => (253200558157 / 1000000000000 : ℝ)
  | 18 => (15561638683 / 62500000000 : ℝ)
  | 19 => (122353191709 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch064Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (39804952381 / 125000000000 : ℝ)
  | 1 => (78829439181 / 250000000000 : ℝ)
  | 2 => (3901741991 / 12500000000 : ℝ)
  | 3 => (154451975941 / 500000000000 : ℝ)
  | 4 => (152805528523 / 500000000000 : ℝ)
  | 5 => (2418081557 / 8000000000 : ℝ)
  | 6 => (298850881803 / 1000000000000 : ℝ)
  | 7 => (295382633079 / 1000000000000 : ℝ)
  | 8 => (14592748013 / 50000000000 : ℝ)
  | 9 => (72066843113 / 250000000000 : ℝ)
  | 10 => (284619376043 / 1000000000000 : ℝ)
  | 11 => (280910474701 / 1000000000000 : ℝ)
  | 12 => (138570084679 / 500000000000 : ℝ)
  | 13 => (136653979099 / 500000000000 : ℝ)
  | 14 => (269413336653 / 1000000000000 : ℝ)
  | 15 => (53091159477 / 200000000000 : ℝ)
  | 16 => (261434830281 / 1000000000000 : ℝ)
  | 17 => (257349922439 / 1000000000000 : ℝ)
  | 18 => (126600279079 / 500000000000 : ℝ)
  | 19 => (248986218929 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch064Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1280 : ℝ) + (j.val : ℝ)) / 1600)
      (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch064Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch064Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1280 : ℝ) + (j.val : ℝ)) / 1600)
    (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch064Neg40WeightLower j.val) (hpThetaShiftOneBatch064Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch064Neg40WeightLower, hpThetaShiftOneBatch064Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch064Neg40_integral_bounds :
    (680239751 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (282645817 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch064Lower hpThetaJensenCellsBatch064Upper
    hpThetaShiftOneBatch064Neg40WeightLower hpThetaShiftOneBatch064Neg40WeightUpper hpThetaJensenCellsBatch064_bounds hpThetaShiftOneBatch064Neg40_weight_bounds
  have hl : (680239751 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch064Lower j * hpThetaShiftOneBatch064Neg40WeightLower j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftOneBatch064Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftOneBatch064Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch064Lower j * hpThetaShiftOneBatch064Neg40WeightUpper j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftOneBatch064Neg40WeightUpper j) / 1600) ≤ (282645817 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftOneBatch064Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1280 : ℝ) / 1600 = 64 / 80 by norm_num,
    show ((1280 : ℝ) + 20) / 1600 = (64 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch064Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4726247619 / 50000000000 : ℝ)
  | 1 => (19184555013 / 200000000000 : ℝ)
  | 2 => (48663340087 / 500000000000 : ℝ)
  | 3 => (98736666017 / 1000000000000 : ℝ)
  | 4 => (6259545671 / 62500000000 : ℝ)
  | 5 => (20314974461 / 200000000000 : ℝ)
  | 6 => (25750772131 / 250000000000 : ℝ)
  | 7 => (4177495081 / 40000000000 : ℝ)
  | 8 => (105877735263 / 1000000000000 : ℝ)
  | 9 => (53662080261 / 500000000000 : ℝ)
  | 10 => (10877664991 / 100000000000 : ℝ)
  | 11 => (110235200359 / 1000000000000 : ℝ)
  | 12 => (6981238039 / 62500000000 : ℝ)
  | 13 => (56585235641 / 500000000000 : ℝ)
  | 14 => (114647184731 / 1000000000000 : ℝ)
  | 15 => (29032486297 / 250000000000 : ℝ)
  | 16 => (11761874869 / 100000000000 : ℝ)
  | 17 => (11911359109 / 100000000000 : ℝ)
  | 18 => (6030723403 / 50000000000 : ℝ)
  | 19 => (24424275017 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch064Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (47961387533 / 500000000000 : ℝ)
  | 1 => (3893067207 / 40000000000 : ℝ)
  | 2 => (49368333009 / 500000000000 : ℝ)
  | 3 => (100152730737 / 1000000000000 : ℝ)
  | 4 => (50787436153 / 500000000000 : ℝ)
  | 5 => (4120123541 / 40000000000 : ℝ)
  | 6 => (52218688513 / 500000000000 : ℝ)
  | 7 => (3308679227 / 31250000000 : ℝ)
  | 8 => (107324160523 / 1000000000000 : ℝ)
  | 9 => (108776649911 / 1000000000000 : ℝ)
  | 10 => (2755880009 / 25000000000 : ℝ)
  | 11 => (893598469 / 8000000000 : ℝ)
  | 12 => (113170471283 / 1000000000000 : ℝ)
  | 13 => (28661796183 / 250000000000 : ℝ)
  | 14 => (116129945189 / 1000000000000 : ℝ)
  | 15 => (117618748691 / 1000000000000 : ℝ)
  | 16 => (119113591091 / 1000000000000 : ℝ)
  | 17 => (120614468061 / 1000000000000 : ℝ)
  | 18 => (61060687543 / 500000000000 : ℝ)
  | 19 => (30908576867 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch064Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1280 : ℝ) + (j.val : ℝ)) / 1600)
      (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch064Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch064Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1280 : ℝ) + (j.val : ℝ)) / 1600)
    (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch064Neg20WeightLower j.val) (hpThetaShiftOneBatch064Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch064Neg20WeightLower, hpThetaShiftOneBatch064Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch064Neg20_integral_bounds :
    (128637031 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (8357137 / 15625000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch064Lower hpThetaJensenCellsBatch064Upper
    hpThetaShiftOneBatch064Neg20WeightLower hpThetaShiftOneBatch064Neg20WeightUpper hpThetaJensenCellsBatch064_bounds hpThetaShiftOneBatch064Neg20_weight_bounds
  have hl : (128637031 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch064Lower j * hpThetaShiftOneBatch064Neg20WeightLower j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftOneBatch064Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftOneBatch064Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch064Lower j * hpThetaShiftOneBatch064Neg20WeightUpper j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftOneBatch064Neg20WeightUpper j) / 1600) ≤ (8357137 / 15625000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftOneBatch064Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1280 : ℝ) / 1600 = 64 / 80 by norm_num,
    show ((1280 : ℝ) + 20) / 1600 = (64 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch064Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch064Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch064Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch064Neg20_integral_bounds
end HodgeProofHP
