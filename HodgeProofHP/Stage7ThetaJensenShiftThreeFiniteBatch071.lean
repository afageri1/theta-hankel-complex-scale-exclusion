/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch071

/-! Exact signed weight and batch integral certificates, batch 71 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch071Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-124123956789 / 1000000000000 : ℝ)
  | 1 => (-31356794991 / 250000000000 : ℝ)
  | 2 => (-126742521167 / 1000000000000 : ℝ)
  | 3 => (-12807007991 / 100000000000 : ℝ)
  | 4 => (-64704978211 / 500000000000 : ℝ)
  | 5 => (-65381125827 / 500000000000 : ℝ)
  | 6 => (-132127067283 / 1000000000000 : ℝ)
  | 7 => (-133504505719 / 1000000000000 : ℝ)
  | 8 => (-26978934021 / 200000000000 : ℝ)
  | 9 => (-34074416081 / 250000000000 : ℝ)
  | 10 => (-68856796503 / 500000000000 : ℝ)
  | 11 => (-17392820191 / 125000000000 : ℝ)
  | 12 => (-140584676023 / 1000000000000 : ℝ)
  | 13 => (-7102002169 / 50000000000 : ℝ)
  | 14 => (-71754385627 / 500000000000 : ℝ)
  | 15 => (-72495484033 / 500000000000 : ℝ)
  | 16 => (-146486743013 / 1000000000000 : ℝ)
  | 17 => (-73998103033 / 500000000000 : ℝ)
  | 18 => (-149519467981 / 1000000000000 : ℝ)
  | 19 => (-151056640301 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch071Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-61416376421 / 500000000000 : ℝ)
  | 1 => (-31030989197 / 250000000000 : ℝ)
  | 2 => (-125427179963 / 1000000000000 : ℝ)
  | 3 => (-63371260583 / 500000000000 : ℝ)
  | 4 => (-128070079909 / 1000000000000 : ℝ)
  | 5 => (-129409956421 / 1000000000000 : ℝ)
  | 6 => (-130762251653 / 1000000000000 : ℝ)
  | 7 => (-66063533641 / 500000000000 : ℝ)
  | 8 => (-66752252859 / 500000000000 : ℝ)
  | 9 => (-16861833763 / 125000000000 : ℝ)
  | 10 => (-136297664323 / 1000000000000 : ℝ)
  | 11 => (-27542718601 / 200000000000 : ℝ)
  | 12 => (-139142561527 / 1000000000000 : ℝ)
  | 13 => (-70292338011 / 500000000000 : ℝ)
  | 14 => (-142040043379 / 1000000000000 : ℝ)
  | 15 => (-143508771253 / 1000000000000 : ℝ)
  | 16 => (-28998193613 / 200000000000 : ℝ)
  | 17 => (-36621685753 / 250000000000 : ℝ)
  | 18 => (-29599241213 / 200000000000 : ℝ)
  | 19 => (-7475973399 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch071Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1420 : ℝ) + (j.val : ℝ)) / 1600)
      (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch071Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch071Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1420 : ℝ) + (j.val : ℝ)) / 1600)
    (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch071Neg100WeightLower j.val) (hpThetaShiftThreeBatch071Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch071Neg100WeightLower, hpThetaShiftThreeBatch071Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch071Neg100_integral_bounds :
    (-49819201 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-374191 / 7812500000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch071Lower hpThetaJensenCellsBatch071Upper
    hpThetaShiftThreeBatch071Neg100WeightLower hpThetaShiftThreeBatch071Neg100WeightUpper hpThetaJensenCellsBatch071_bounds hpThetaShiftThreeBatch071Neg100_weight_bounds
  have hl : (-49819201 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch071Lower j * hpThetaShiftThreeBatch071Neg100WeightLower j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftThreeBatch071Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftThreeBatch071Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch071Lower j * hpThetaShiftThreeBatch071Neg100WeightUpper j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftThreeBatch071Neg100WeightUpper j) / 1600) ≤ (-374191 / 7812500000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftThreeBatch071Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1420 : ℝ) / 1600 = 71 / 80 by norm_num,
    show ((1420 : ℝ) + 20) / 1600 = (71 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch071Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1252455517 / 62500000000 : ℝ)
  | 1 => (-5074966987 / 250000000000 : ℝ)
  | 2 => (-4112651121 / 200000000000 : ℝ)
  | 3 => (-20829476913 / 1000000000000 : ℝ)
  | 4 => (-10549278871 / 500000000000 : ℝ)
  | 5 => (-21370524163 / 1000000000000 : ℝ)
  | 6 => (-5411350613 / 250000000000 : ℝ)
  | 7 => (-21923219089 / 1000000000000 : ℝ)
  | 8 => (-11102000379 / 500000000000 : ℝ)
  | 9 => (-1405485897 / 62500000000 : ℝ)
  | 10 => (-11387283487 / 500000000000 : ℝ)
  | 11 => (-11532202967 / 500000000000 : ℝ)
  | 12 => (-4671463751 / 200000000000 : ℝ)
  | 13 => (-11826666587 / 500000000000 : ℝ)
  | 14 => (-1197623857 / 50000000000 : ℝ)
  | 15 => (-24254778819 / 1000000000000 : ℝ)
  | 16 => (-12280133297 / 500000000000 : ℝ)
  | 17 => (-4973793813 / 200000000000 : ℝ)
  | 18 => (-5036183011 / 200000000000 : ℝ)
  | 19 => (-5099226721 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch071Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-19781491107 / 1000000000000 : ℝ)
  | 1 => (-20039288271 / 1000000000000 : ℝ)
  | 2 => (-20299867947 / 1000000000000 : ℝ)
  | 3 => (-5140813901 / 250000000000 : ℝ)
  | 4 => (-1301842307 / 62500000000 : ℝ)
  | 5 => (-21098557741 / 1000000000000 : ℝ)
  | 6 => (-10685262081 / 500000000000 : ℝ)
  | 7 => (-21645402451 / 1000000000000 : ℝ)
  | 8 => (-1370201193 / 62500000000 : ℝ)
  | 9 => (-22204000757 / 1000000000000 : ℝ)
  | 10 => (-22487774351 / 1000000000000 : ℝ)
  | 11 => (-22774566973 / 1000000000000 : ℝ)
  | 12 => (-23064405933 / 1000000000000 : ℝ)
  | 13 => (-11678659377 / 500000000000 : ℝ)
  | 14 => (-23653333173 / 1000000000000 : ℝ)
  | 15 => (-23952477139 / 1000000000000 : ℝ)
  | 16 => (-12127389409 / 500000000000 : ℝ)
  | 17 => (-24560266593 / 1000000000000 : ℝ)
  | 18 => (-3108621133 / 125000000000 : ℝ)
  | 19 => (-12590457527 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch071Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1420 : ℝ) + (j.val : ℝ)) / 1600)
      (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch071Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch071Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1420 : ℝ) + (j.val : ℝ)) / 1600)
    (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch071Neg70WeightLower j.val) (hpThetaShiftThreeBatch071Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch071Neg70WeightLower, hpThetaShiftThreeBatch071Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch071Neg70_integral_bounds :
    (-8221547 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-1577133 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch071Lower hpThetaJensenCellsBatch071Upper
    hpThetaShiftThreeBatch071Neg70WeightLower hpThetaShiftThreeBatch071Neg70WeightUpper hpThetaJensenCellsBatch071_bounds hpThetaShiftThreeBatch071Neg70_weight_bounds
  have hl : (-8221547 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch071Lower j * hpThetaShiftThreeBatch071Neg70WeightLower j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftThreeBatch071Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftThreeBatch071Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch071Lower j * hpThetaShiftThreeBatch071Neg70WeightUpper j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftThreeBatch071Neg70WeightUpper j) / 1600) ≤ (-1577133 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftThreeBatch071Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1420 : ℝ) / 1600 = 71 / 80 by norm_num,
    show ((1420 : ℝ) + 20) / 1600 = (71 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch071Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1334515441 / 1000000000000 : ℝ)
  | 1 => (132963471 / 100000000000 : ℝ)
  | 2 => (1324526309 / 1000000000000 : ℝ)
  | 3 => (1319186933 / 1000000000000 : ℝ)
  | 4 => (262722649 / 200000000000 : ℝ)
  | 5 => (81737617 / 62500000000 : ℝ)
  | 6 => (130174941 / 100000000000 : ℝ)
  | 7 => (1295452419 / 1000000000000 : ℝ)
  | 8 => (1288907427 / 1000000000000 : ℝ)
  | 9 => (51284437 / 40000000000 : ℝ)
  | 10 => (1275059369 / 1000000000000 : ℝ)
  | 11 => (633874591 / 500000000000 : ℝ)
  | 12 => (1260176751 / 1000000000000 : ℝ)
  | 13 => (626169213 / 500000000000 : ℝ)
  | 14 => (622115261 / 500000000000 : ℝ)
  | 15 => (617924659 / 500000000000 : ℝ)
  | 16 => (76699441 / 62500000000 : ℝ)
  | 17 => (1218251941 / 1000000000000 : ℝ)
  | 18 => (604514071 / 500000000000 : ℝ)
  | 19 => (119951579 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch071Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (669585887 / 500000000000 : ℝ)
  | 1 => (667257721 / 500000000000 : ℝ)
  | 2 => (1329634711 / 1000000000000 : ℝ)
  | 3 => (132452631 / 100000000000 : ℝ)
  | 4 => (659593467 / 500000000000 : ℝ)
  | 5 => (656806623 / 500000000000 : ℝ)
  | 6 => (1307801873 / 1000000000000 : ℝ)
  | 7 => (1301749411 / 1000000000000 : ℝ)
  | 8 => (64772621 / 50000000000 : ℝ)
  | 9 => (322226857 / 250000000000 : ℝ)
  | 10 => (641055463 / 500000000000 : ℝ)
  | 11 => (127505937 / 100000000000 : ℝ)
  | 12 => (1267749183 / 1000000000000 : ℝ)
  | 13 => (78761047 / 62500000000 : ℝ)
  | 14 => (1252338427 / 1000000000000 : ℝ)
  | 15 => (1244230523 / 1000000000000 : ℝ)
  | 16 => (1235849319 / 1000000000000 : ℝ)
  | 17 => (1227191057 / 1000000000000 : ℝ)
  | 18 => (609125971 / 500000000000 : ℝ)
  | 19 => (1209028143 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch071Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1420 : ℝ) + (j.val : ℝ)) / 1600)
      (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch071Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch071Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1420 : ℝ) + (j.val : ℝ)) / 1600)
    (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch071Neg45WeightLower j.val) (hpThetaShiftThreeBatch071Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch071Neg45WeightLower, hpThetaShiftThreeBatch071Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch071Neg45_integral_bounds :
    (454321 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (470179 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch071Lower hpThetaJensenCellsBatch071Upper
    hpThetaShiftThreeBatch071Neg45WeightLower hpThetaShiftThreeBatch071Neg45WeightUpper hpThetaJensenCellsBatch071_bounds hpThetaShiftThreeBatch071Neg45_weight_bounds
  have hl : (454321 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch071Lower j * hpThetaShiftThreeBatch071Neg45WeightLower j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftThreeBatch071Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftThreeBatch071Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch071Lower j * hpThetaShiftThreeBatch071Neg45WeightUpper j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftThreeBatch071Neg45WeightUpper j) / 1600) ≤ (470179 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftThreeBatch071Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1420 : ℝ) / 1600 = 71 / 80 by norm_num,
    show ((1420 : ℝ) + 20) / 1600 = (71 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch071Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (19618231 / 250000000000 : ℝ)
  | 1 => (16776909 / 200000000000 : ℝ)
  | 2 => (8935171 / 100000000000 : ℝ)
  | 3 => (47437357 / 500000000000 : ℝ)
  | 4 => (100453853 / 1000000000000 : ℝ)
  | 5 => (106089423 / 1000000000000 : ℝ)
  | 6 => (111781721 / 1000000000000 : ℝ)
  | 7 => (29382761 / 250000000000 : ℝ)
  | 8 => (61668843 / 500000000000 : ℝ)
  | 9 => (64600973 / 500000000000 : ℝ)
  | 10 => (135124119 / 1000000000000 : ℝ)
  | 11 => (141104503 / 1000000000000 : ℝ)
  | 12 => (147143393 / 1000000000000 : ℝ)
  | 13 => (299299 / 1953125000 : ℝ)
  | 14 => (79698941 / 500000000000 : ℝ)
  | 15 => (82807037 / 500000000000 : ℝ)
  | 16 => (171889959 / 1000000000000 : ℝ)
  | 17 => (35645167 / 200000000000 : ℝ)
  | 18 => (92310999 / 500000000000 : ℝ)
  | 19 => (23884843 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch071Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (41942273 / 500000000000 : ℝ)
  | 1 => (89351711 / 1000000000000 : ℝ)
  | 2 => (18974943 / 200000000000 : ℝ)
  | 3 => (50226927 / 500000000000 : ℝ)
  | 4 => (6630589 / 62500000000 : ℝ)
  | 5 => (55890861 / 500000000000 : ℝ)
  | 6 => (23506209 / 200000000000 : ℝ)
  | 7 => (123337687 / 1000000000000 : ℝ)
  | 8 => (129201947 / 1000000000000 : ℝ)
  | 9 => (3378103 / 25000000000 : ℝ)
  | 10 => (17638063 / 125000000000 : ℝ)
  | 11 => (73571697 / 500000000000 : ℝ)
  | 12 => (153241089 / 1000000000000 : ℝ)
  | 13 => (159397883 / 1000000000000 : ℝ)
  | 14 => (6624563 / 40000000000 : ℝ)
  | 15 => (4297249 / 25000000000 : ℝ)
  | 16 => (44556459 / 250000000000 : ℝ)
  | 17 => (184621999 / 1000000000000 : ℝ)
  | 18 => (38215749 / 200000000000 : ℝ)
  | 19 => (197596371 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch071Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1420 : ℝ) + (j.val : ℝ)) / 1600)
      (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch071Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch071Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1420 : ℝ) + (j.val : ℝ)) / 1600)
    (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch071Neg25WeightLower j.val) (hpThetaShiftThreeBatch071Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch071Neg25WeightLower, hpThetaShiftThreeBatch071Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch071Neg25_integral_bounds :
    (45849 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (12341 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch071Lower hpThetaJensenCellsBatch071Upper
    hpThetaShiftThreeBatch071Neg25WeightLower hpThetaShiftThreeBatch071Neg25WeightUpper hpThetaJensenCellsBatch071_bounds hpThetaShiftThreeBatch071Neg25_weight_bounds
  have hl : (45849 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch071Lower j * hpThetaShiftThreeBatch071Neg25WeightLower j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftThreeBatch071Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftThreeBatch071Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch071Lower j * hpThetaShiftThreeBatch071Neg25WeightUpper j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftThreeBatch071Neg25WeightUpper j) / 1600) ≤ (12341 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftThreeBatch071Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1420 : ℝ) / 1600 = 71 / 80 by norm_num,
    show ((1420 : ℝ) + 20) / 1600 = (71 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch071Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch071Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch071Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch071Neg25_integral_bounds
end HodgeProofHP
