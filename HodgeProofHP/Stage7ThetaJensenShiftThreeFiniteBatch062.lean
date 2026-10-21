/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch062

/-! Exact signed weight and batch integral certificates, batch 62 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch062Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-14657575939 / 1000000000000 : ℝ)
  | 1 => (-2971971263 / 200000000000 : ℝ)
  | 2 => (-376612867 / 25000000000 : ℝ)
  | 3 => (-3817893777 / 250000000000 : ℝ)
  | 4 => (-7740530941 / 500000000000 : ℝ)
  | 5 => (-15692999499 / 1000000000000 : ℝ)
  | 6 => (-3976853167 / 250000000000 : ℝ)
  | 7 => (-2015540789 / 125000000000 : ℝ)
  | 8 => (-16343765573 / 1000000000000 : ℝ)
  | 9 => (-1656575581 / 100000000000 : ℝ)
  | 10 => (-16790322601 / 1000000000000 : ℝ)
  | 11 => (-8508745873 / 500000000000 : ℝ)
  | 12 => (-1724728927 / 100000000000 : ℝ)
  | 13 => (-17479741419 / 1000000000000 : ℝ)
  | 14 => (-4428718667 / 250000000000 : ℝ)
  | 15 => (-448817893 / 25000000000 : ℝ)
  | 16 => (-9096645753 / 500000000000 : ℝ)
  | 17 => (-2304578649 / 125000000000 : ℝ)
  | 18 => (-18682756173 / 1000000000000 : ℝ)
  | 19 => (-9465850041 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch062Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2891529937 / 200000000000 : ℝ)
  | 1 => (-7328787969 / 500000000000 : ℝ)
  | 2 => (-7429928157 / 500000000000 : ℝ)
  | 3 => (-15064514679 / 1000000000000 : ℝ)
  | 4 => (-15271575107 / 1000000000000 : ℝ)
  | 5 => (-15481061881 / 1000000000000 : ℝ)
  | 6 => (-7846499749 / 500000000000 : ℝ)
  | 7 => (-15907412667 / 1000000000000 : ℝ)
  | 8 => (-16124326311 / 1000000000000 : ℝ)
  | 9 => (-4085941393 / 250000000000 : ℝ)
  | 10 => (-16565755809 / 1000000000000 : ℝ)
  | 11 => (-83951613 / 5000000000 : ℝ)
  | 12 => (-3403498349 / 200000000000 : ℝ)
  | 13 => (-17247289269 / 1000000000000 : ℝ)
  | 14 => (-8739870709 / 500000000000 : ℝ)
  | 15 => (-17714874667 / 1000000000000 : ℝ)
  | 16 => (-17952715719 / 1000000000000 : ℝ)
  | 17 => (-3638658301 / 200000000000 : ℝ)
  | 18 => (-18436629191 / 1000000000000 : ℝ)
  | 19 => (-4670689043 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch062Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1240 : ℝ) + (j.val : ℝ)) / 1600)
      (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch062Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch062Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1240 : ℝ) + (j.val : ℝ)) / 1600)
    (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch062Neg100WeightLower j.val) (hpThetaShiftThreeBatch062Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch062Neg100WeightLower, hpThetaShiftThreeBatch062Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch062Neg100_integral_bounds :
    (-19535373 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-150485261 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch062Lower hpThetaJensenCellsBatch062Upper
    hpThetaShiftThreeBatch062Neg100WeightLower hpThetaShiftThreeBatch062Neg100WeightUpper hpThetaJensenCellsBatch062_bounds hpThetaShiftThreeBatch062Neg100_weight_bounds
  have hl : (-19535373 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch062Lower j * hpThetaShiftThreeBatch062Neg100WeightLower j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftThreeBatch062Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftThreeBatch062Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch062Lower j * hpThetaShiftThreeBatch062Neg100WeightUpper j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftThreeBatch062Neg100WeightUpper j) / 1600) ≤ (-150485261 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftThreeBatch062Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1240 : ℝ) / 1600 = 62 / 80 by norm_num,
    show ((1240 : ℝ) + 20) / 1600 = (62 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch062Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-27768169 / 40000000000 : ℝ)
  | 1 => (-718857257 / 1000000000000 : ℝ)
  | 2 => (-148786371 / 200000000000 : ℝ)
  | 3 => (-24044791 / 31250000000 : ℝ)
  | 4 => (-31814679 / 40000000000 : ℝ)
  | 5 => (-205434561 / 250000000000 : ℝ)
  | 6 => (-848552573 / 1000000000000 : ℝ)
  | 7 => (-875815471 / 1000000000000 : ℝ)
  | 8 => (-903532501 / 1000000000000 : ℝ)
  | 9 => (-931709283 / 1000000000000 : ℝ)
  | 10 => (-960351493 / 1000000000000 : ℝ)
  | 11 => (-49473243 / 50000000000 : ℝ)
  | 12 => (-40762207 / 40000000000 : ℝ)
  | 13 => (-524564141 / 500000000000 : ℝ)
  | 14 => (-269922521 / 250000000000 : ℝ)
  | 15 => (-69421659 / 62500000000 : ℝ)
  | 16 => (-571151841 / 500000000000 : ℝ)
  | 17 => (-146795947 / 125000000000 : ℝ)
  | 18 => (-1206944367 / 1000000000000 : ℝ)
  | 19 => (-310010063 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch062Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-669967517 / 1000000000000 : ℝ)
  | 1 => (-10846941 / 15625000000 : ℝ)
  | 2 => (-89857157 / 125000000000 : ℝ)
  | 3 => (-371965927 / 500000000000 : ℝ)
  | 4 => (-769433311 / 1000000000000 : ℝ)
  | 5 => (-397683487 / 500000000000 : ℝ)
  | 6 => (-821738243 / 1000000000000 : ℝ)
  | 7 => (-212138143 / 250000000000 : ℝ)
  | 8 => (-87581547 / 100000000000 : ℝ)
  | 9 => (-361413 / 400000000 : ℝ)
  | 10 => (-465854641 / 500000000000 : ℝ)
  | 11 => (-240087873 / 250000000000 : ℝ)
  | 12 => (-989464859 / 1000000000000 : ℝ)
  | 13 => (-509527587 / 500000000000 : ℝ)
  | 14 => (-1049128281 / 1000000000000 : ℝ)
  | 15 => (-1079690083 / 1000000000000 : ℝ)
  | 16 => (-1110746543 / 1000000000000 : ℝ)
  | 17 => (-1142303681 / 1000000000000 : ℝ)
  | 18 => (-46974703 / 40000000000 : ℝ)
  | 19 => (-603472183 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch062Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1240 : ℝ) + (j.val : ℝ)) / 1600)
      (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch062Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch062Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1240 : ℝ) + (j.val : ℝ)) / 1600)
    (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch062Neg70WeightLower j.val) (hpThetaShiftThreeBatch062Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch062Neg70WeightLower, hpThetaShiftThreeBatch062Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch062Neg70_integral_bounds :
    (-22091 / 2500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-8364359 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch062Lower hpThetaJensenCellsBatch062Upper
    hpThetaShiftThreeBatch062Neg70WeightLower hpThetaShiftThreeBatch062Neg70WeightUpper hpThetaJensenCellsBatch062_bounds hpThetaShiftThreeBatch062Neg70_weight_bounds
  have hl : (-22091 / 2500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch062Lower j * hpThetaShiftThreeBatch062Neg70WeightLower j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftThreeBatch062Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftThreeBatch062Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch062Lower j * hpThetaShiftThreeBatch062Neg70WeightUpper j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftThreeBatch062Neg70WeightUpper j) / 1600) ≤ (-8364359 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftThreeBatch062Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1240 : ℝ) / 1600 = 62 / 80 by norm_num,
    show ((1240 : ℝ) + 20) / 1600 = (62 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch062Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (620214573 / 1000000000000 : ℝ)
  | 1 => (625897713 / 1000000000000 : ℝ)
  | 2 => (631602033 / 1000000000000 : ℝ)
  | 3 => (79665909 / 125000000000 : ℝ)
  | 4 => (643073163 / 1000000000000 : ℝ)
  | 5 => (129767887 / 200000000000 : ℝ)
  | 6 => (40914113 / 62500000000 : ℝ)
  | 7 => (132086399 / 200000000000 : ℝ)
  | 8 => (333128853 / 500000000000 : ℝ)
  | 9 => (336051321 / 500000000000 : ℝ)
  | 10 => (338983249 / 500000000000 : ℝ)
  | 11 => (341924481 / 500000000000 : ℝ)
  | 12 => (172437429 / 250000000000 : ℝ)
  | 13 => (139133687 / 200000000000 : ℝ)
  | 14 => (350802393 / 500000000000 : ℝ)
  | 15 => (707558431 / 1000000000000 : ℝ)
  | 16 => (713529023 / 1000000000000 : ℝ)
  | 17 => (71951621 / 100000000000 : ℝ)
  | 18 => (72551963 / 100000000000 : ℝ)
  | 19 => (365769459 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch062Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (312948857 / 500000000000 : ℝ)
  | 1 => (315801017 / 500000000000 : ℝ)
  | 2 => (637327273 / 1000000000000 : ℝ)
  | 3 => (160768291 / 250000000000 : ℝ)
  | 4 => (162209859 / 250000000000 : ℝ)
  | 5 => (654625809 / 1000000000000 : ℝ)
  | 6 => (165107999 / 250000000000 : ℝ)
  | 7 => (666257707 / 1000000000000 : ℝ)
  | 8 => (672102643 / 1000000000000 : ℝ)
  | 9 => (677966499 / 1000000000000 : ℝ)
  | 10 => (683848963 / 1000000000000 : ℝ)
  | 11 => (689749717 / 1000000000000 : ℝ)
  | 12 => (173917109 / 250000000000 : ℝ)
  | 13 => (701604787 / 1000000000000 : ℝ)
  | 14 => (22111201 / 31250000000 : ℝ)
  | 15 => (11148891 / 15625000000 : ℝ)
  | 16 => (719516211 / 1000000000000 : ℝ)
  | 17 => (725519631 / 1000000000000 : ℝ)
  | 18 => (731538919 / 1000000000000 : ℝ)
  | 19 => (737573697 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch062Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1240 : ℝ) + (j.val : ℝ)) / 1600)
      (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch062Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch062Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1240 : ℝ) + (j.val : ℝ)) / 1600)
    (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch062Neg45WeightLower j.val) (hpThetaShiftThreeBatch062Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch062Neg45WeightLower, hpThetaShiftThreeBatch062Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch062Neg45_integral_bounds :
    (1543997 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (398947 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch062Lower hpThetaJensenCellsBatch062Upper
    hpThetaShiftThreeBatch062Neg45WeightLower hpThetaShiftThreeBatch062Neg45WeightUpper hpThetaJensenCellsBatch062_bounds hpThetaShiftThreeBatch062Neg45_weight_bounds
  have hl : (1543997 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch062Lower j * hpThetaShiftThreeBatch062Neg45WeightLower j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftThreeBatch062Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftThreeBatch062Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch062Lower j * hpThetaShiftThreeBatch062Neg45WeightUpper j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftThreeBatch062Neg45WeightUpper j) / 1600) ≤ (398947 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftThreeBatch062Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1240 : ℝ) / 1600 = 62 / 80 by norm_num,
    show ((1240 : ℝ) + 20) / 1600 = (62 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch062Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-130303219 / 500000000000 : ℝ)
  | 1 => (-260918649 / 1000000000000 : ℝ)
  | 2 => (-261217889 / 1000000000000 : ℝ)
  | 3 => (-261503997 / 1000000000000 : ℝ)
  | 4 => (-52355363 / 200000000000 : ℝ)
  | 5 => (-262036181 / 1000000000000 : ℝ)
  | 6 => (-131140967 / 500000000000 : ℝ)
  | 7 => (-262513911 / 1000000000000 : ℝ)
  | 8 => (-65682987 / 250000000000 : ℝ)
  | 9 => (-6573397 / 25000000000 : ℝ)
  | 10 => (-131562771 / 500000000000 : ℝ)
  | 11 => (-8228149 / 31250000000 : ℝ)
  | 12 => (-263461389 / 1000000000000 : ℝ)
  | 13 => (-131803619 / 500000000000 : ℝ)
  | 14 => (-52747629 / 200000000000 : ℝ)
  | 15 => (-13192697 / 50000000000 : ℝ)
  | 16 => (-263954451 / 1000000000000 : ℝ)
  | 17 => (-264039507 / 1000000000000 : ℝ)
  | 18 => (-264108933 / 1000000000000 : ℝ)
  | 19 => (-66040639 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch062Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-65070353 / 250000000000 : ℝ)
  | 1 => (-260606437 / 1000000000000 : ℝ)
  | 2 => (-32614831 / 125000000000 : ℝ)
  | 3 => (-8163059 / 31250000000 : ℝ)
  | 4 => (-65375999 / 250000000000 : ℝ)
  | 5 => (-130888407 / 500000000000 : ℝ)
  | 6 => (-13101809 / 50000000000 : ℝ)
  | 7 => (-262281933 / 1000000000000 : ℝ)
  | 8 => (-26251391 / 100000000000 : ℝ)
  | 9 => (-262731947 / 1000000000000 : ℝ)
  | 10 => (-262935879 / 1000000000000 : ℝ)
  | 11 => (-263125541 / 1000000000000 : ℝ)
  | 12 => (-263300767 / 1000000000000 : ℝ)
  | 13 => (-65865347 / 250000000000 : ℝ)
  | 14 => (-263607237 / 1000000000000 : ℝ)
  | 15 => (-8241817 / 31250000000 : ℝ)
  | 16 => (-263853939 / 1000000000000 : ℝ)
  | 17 => (-5279089 / 20000000000 : ℝ)
  | 18 => (-132019753 / 500000000000 : ℝ)
  | 19 => (-66027233 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch062Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1240 : ℝ) + (j.val : ℝ)) / 1600)
      (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch062Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch062Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1240 : ℝ) + (j.val : ℝ)) / 1600)
    (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch062Neg25WeightLower j.val) (hpThetaShiftThreeBatch062Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch062Neg25WeightLower, hpThetaShiftThreeBatch062Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch062Neg25_integral_bounds :
    (-2472693 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-602863 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch062Lower hpThetaJensenCellsBatch062Upper
    hpThetaShiftThreeBatch062Neg25WeightLower hpThetaShiftThreeBatch062Neg25WeightUpper hpThetaJensenCellsBatch062_bounds hpThetaShiftThreeBatch062Neg25_weight_bounds
  have hl : (-2472693 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch062Lower j * hpThetaShiftThreeBatch062Neg25WeightLower j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftThreeBatch062Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftThreeBatch062Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch062Lower j * hpThetaShiftThreeBatch062Neg25WeightUpper j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftThreeBatch062Neg25WeightUpper j) / 1600) ≤ (-602863 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftThreeBatch062Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1240 : ℝ) / 1600 = 62 / 80 by norm_num,
    show ((1240 : ℝ) + 20) / 1600 = (62 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch062Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch062Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch062Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch062Neg25_integral_bounds
end HodgeProofHP
