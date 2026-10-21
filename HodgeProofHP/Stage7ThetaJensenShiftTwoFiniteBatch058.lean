/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch058

/-! Exact signed weight and batch integral certificates, batch 58 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch058Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-61519679707 / 200000000000 : ℝ)
  | 1 => (-311494424499 / 1000000000000 : ℝ)
  | 2 => (-315431051189 / 1000000000000 : ℝ)
  | 3 => (-63881726211 / 200000000000 : ℝ)
  | 4 => (-323427519091 / 1000000000000 : ℝ)
  | 5 => (-327488072853 / 1000000000000 : ℝ)
  | 6 => (-41448831559 / 125000000000 : ℝ)
  | 7 => (-335735620669 / 1000000000000 : ℝ)
  | 8 => (-339923342771 / 1000000000000 : ℝ)
  | 9 => (-344154186727 / 1000000000000 : ℝ)
  | 10 => (-557485637 / 1600000000 : ℝ)
  | 11 => (-352746725203 / 1000000000000 : ℝ)
  | 12 => (-357109168867 / 1000000000000 : ℝ)
  | 13 => (-361516232709 / 1000000000000 : ℝ)
  | 14 => (-365968298019 / 1000000000000 : ℝ)
  | 15 => (-92616437201 / 250000000000 : ℝ)
  | 16 => (-375008971801 / 1000000000000 : ℝ)
  | 17 => (-75919671299 / 200000000000 : ℝ)
  | 18 => (-76846859027 / 200000000000 : ℝ)
  | 19 => (-1555668731 / 4000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch058Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-303742623377 / 1000000000000 : ℝ)
  | 1 => (-153799199267 / 500000000000 : ℝ)
  | 2 => (-155747212249 / 500000000000 : ℝ)
  | 3 => (-78857762797 / 250000000000 : ℝ)
  | 4 => (-159704315527 / 500000000000 : ℝ)
  | 5 => (-32342751909 / 100000000000 : ℝ)
  | 6 => (-81872018213 / 250000000000 : ℝ)
  | 7 => (-331590652471 / 1000000000000 : ℝ)
  | 8 => (-83933905167 / 250000000000 : ℝ)
  | 9 => (-33992334277 / 100000000000 : ℝ)
  | 10 => (-172077093363 / 500000000000 : ℝ)
  | 11 => (-87107130781 / 250000000000 : ℝ)
  | 12 => (-176373362601 / 500000000000 : ℝ)
  | 13 => (-178554584433 / 500000000000 : ℝ)
  | 14 => (-90379058177 / 250000000000 : ℝ)
  | 15 => (-182984149009 / 500000000000 : ℝ)
  | 16 => (-370465748803 / 1000000000000 : ℝ)
  | 17 => (-1875044859 / 5000000000 : ℝ)
  | 18 => (-189799178247 / 500000000000 : ℝ)
  | 19 => (-192117147567 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch058Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1160 : ℝ) + (j.val : ℝ)) / 1600)
      (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch058Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch058Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1160 : ℝ) + (j.val : ℝ)) / 1600)
    (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch058Neg100WeightLower j.val) (hpThetaShiftTwoBatch058Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch058Neg100WeightLower, hpThetaShiftTwoBatch058Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch058Neg100_integral_bounds :
    (-5325818047 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-160721143 / 15625000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch058Lower hpThetaJensenCellsBatch058Upper
    hpThetaShiftTwoBatch058Neg100WeightLower hpThetaShiftTwoBatch058Neg100WeightUpper hpThetaJensenCellsBatch058_bounds hpThetaShiftTwoBatch058Neg100_weight_bounds
  have hl : (-5325818047 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch058Lower j * hpThetaShiftTwoBatch058Neg100WeightLower j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftTwoBatch058Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftTwoBatch058Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch058Lower j * hpThetaShiftTwoBatch058Neg100WeightUpper j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftTwoBatch058Neg100WeightUpper j) / 1600) ≤ (-160721143 / 15625000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftTwoBatch058Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1160 : ℝ) / 1600 = 58 / 80 by norm_num,
    show ((1160 : ℝ) + 20) / 1600 = (58 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch058Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1745438303 / 1000000000000 : ℝ)
  | 1 => (-1032158833 / 500000000000 : ℝ)
  | 2 => (-2388781281 / 1000000000000 : ℝ)
  | 3 => (-2718892369 / 1000000000000 : ℝ)
  | 4 => (-3054714689 / 1000000000000 : ℝ)
  | 5 => (-3396312537 / 1000000000000 : ℝ)
  | 6 => (-3743750757 / 1000000000000 : ℝ)
  | 7 => (-4097094739 / 1000000000000 : ℝ)
  | 8 => (-178256417 / 40000000000 : ℝ)
  | 9 => (-602720539 / 125000000000 : ℝ)
  | 10 => (-2596611727 / 500000000000 : ℝ)
  | 11 => (-557085547 / 100000000000 : ℝ)
  | 12 => (-2977364271 / 500000000000 : ℝ)
  | 13 => (-6344911423 / 1000000000000 : ℝ)
  | 14 => (-6741473441 / 1000000000000 : ℝ)
  | 15 => (-7144484497 / 1000000000000 : ℝ)
  | 16 => (-3777007539 / 500000000000 : ℝ)
  | 17 => (-7970136251 / 1000000000000 : ℝ)
  | 18 => (-4196459837 / 500000000000 : ℝ)
  | 19 => (-2205609399 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch058Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-179010063 / 125000000000 : ℝ)
  | 1 => (-872719151 / 500000000000 : ℝ)
  | 2 => (-412863533 / 200000000000 : ℝ)
  | 3 => (-14929883 / 6250000000 : ℝ)
  | 4 => (-169930773 / 62500000000 : ℝ)
  | 5 => (-47729917 / 15625000000 : ℝ)
  | 6 => (-424539067 / 125000000000 : ℝ)
  | 7 => (-935937689 / 250000000000 : ℝ)
  | 8 => (-2048547369 / 500000000000 : ℝ)
  | 9 => (-557051303 / 125000000000 : ℝ)
  | 10 => (-4821764311 / 1000000000000 : ℝ)
  | 11 => (-5193223453 / 1000000000000 : ℝ)
  | 12 => (-5570855469 / 1000000000000 : ℝ)
  | 13 => (-5954728541 / 1000000000000 : ℝ)
  | 14 => (-3172455711 / 500000000000 : ℝ)
  | 15 => (-42134209 / 6250000000 : ℝ)
  | 16 => (-446530281 / 62500000000 : ℝ)
  | 17 => (-7554015077 / 1000000000000 : ℝ)
  | 18 => (-6376109 / 800000000 : ℝ)
  | 19 => (-8392919673 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch058Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1160 : ℝ) + (j.val : ℝ)) / 1600)
      (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch058Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch058Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1160 : ℝ) + (j.val : ℝ)) / 1600)
    (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch058Neg65WeightLower j.val) (hpThetaShiftTwoBatch058Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch058Neg65WeightLower, hpThetaShiftTwoBatch058Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch058Neg65_integral_bounds :
    (-76198109 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-27584663 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch058Lower hpThetaJensenCellsBatch058Upper
    hpThetaShiftTwoBatch058Neg65WeightLower hpThetaShiftTwoBatch058Neg65WeightUpper hpThetaJensenCellsBatch058_bounds hpThetaShiftTwoBatch058Neg65_weight_bounds
  have hl : (-76198109 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch058Lower j * hpThetaShiftTwoBatch058Neg65WeightLower j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftTwoBatch058Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftTwoBatch058Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch058Lower j * hpThetaShiftTwoBatch058Neg65WeightUpper j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftTwoBatch058Neg65WeightUpper j) / 1600) ≤ (-27584663 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftTwoBatch058Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1160 : ℝ) / 1600 = 58 / 80 by norm_num,
    show ((1160 : ℝ) + 20) / 1600 = (58 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch058Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (738401713 / 50000000000 : ℝ)
  | 1 => (7431848387 / 500000000000 : ℝ)
  | 2 => (46747857 / 3125000000 : ℝ)
  | 3 => (1881859741 / 125000000000 : ℝ)
  | 4 => (3787594749 / 250000000000 : ℝ)
  | 5 => (3811452121 / 250000000000 : ℝ)
  | 6 => (7670578659 / 500000000000 : ℝ)
  | 7 => (7718208153 / 500000000000 : ℝ)
  | 8 => (15531576137 / 1000000000000 : ℝ)
  | 9 => (15626627381 / 1000000000000 : ℝ)
  | 10 => (1572156049 / 100000000000 : ℝ)
  | 11 => (494261431 / 31250000000 : ℝ)
  | 12 => (1988879187 / 125000000000 : ℝ)
  | 13 => (4001388421 / 250000000000 : ℝ)
  | 14 => (8049958159 / 500000000000 : ℝ)
  | 15 => (16194111233 / 1000000000000 : ℝ)
  | 16 => (8144064069 / 500000000000 : ℝ)
  | 17 => (16381956617 / 1000000000000 : ℝ)
  | 18 => (4118896531 / 250000000000 : ℝ)
  | 19 => (517781437 / 31250000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch058Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (594547871 / 40000000000 : ℝ)
  | 1 => (14959314241 / 1000000000000 : ℝ)
  | 2 => (15054877929 / 1000000000000 : ℝ)
  | 3 => (15150378997 / 1000000000000 : ℝ)
  | 4 => (3049161697 / 200000000000 : ℝ)
  | 5 => (15341157319 / 1000000000000 : ℝ)
  | 6 => (15436416307 / 1000000000000 : ℝ)
  | 7 => (7765788069 / 500000000000 : ℝ)
  | 8 => (7813313691 / 500000000000 : ℝ)
  | 9 => (15721560491 / 1000000000000 : ℝ)
  | 10 => (15816365793 / 1000000000000 : ℝ)
  | 11 => (15911033497 / 1000000000000 : ℝ)
  | 12 => (3201110737 / 200000000000 : ℝ)
  | 13 => (16099916319 / 1000000000000 : ℝ)
  | 14 => (8097055617 / 500000000000 : ℝ)
  | 15 => (16288128139 / 1000000000000 : ℝ)
  | 16 => (8190978309 / 500000000000 : ℝ)
  | 17 => (131804689 / 8000000000 : ℝ)
  | 18 => (3313801197 / 200000000000 : ℝ)
  | 19 => (3332441079 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch058Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1160 : ℝ) + (j.val : ℝ)) / 1600)
      (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch058Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch058Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1160 : ℝ) + (j.val : ℝ)) / 1600)
    (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch058Neg45WeightLower j.val) (hpThetaShiftTwoBatch058Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch058Neg45WeightLower, hpThetaShiftTwoBatch058Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch058Neg45_integral_bounds :
    (471706589 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (9707799 / 20000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch058Lower hpThetaJensenCellsBatch058Upper
    hpThetaShiftTwoBatch058Neg45WeightLower hpThetaShiftTwoBatch058Neg45WeightUpper hpThetaJensenCellsBatch058_bounds hpThetaShiftTwoBatch058Neg45_weight_bounds
  have hl : (471706589 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch058Lower j * hpThetaShiftTwoBatch058Neg45WeightLower j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftTwoBatch058Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftTwoBatch058Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch058Lower j * hpThetaShiftTwoBatch058Neg45WeightUpper j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftTwoBatch058Neg45WeightUpper j) / 1600) ≤ (9707799 / 20000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftTwoBatch058Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1160 : ℝ) / 1600 = 58 / 80 by norm_num,
    show ((1160 : ℝ) + 20) / 1600 = (58 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch058Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1639408227 / 500000000000 : ℝ)
  | 1 => (-814976221 / 250000000000 : ℝ)
  | 2 => (-1620325271 / 500000000000 : ℝ)
  | 3 => (-3221051269 / 1000000000000 : ℝ)
  | 4 => (-1600552453 / 500000000000 : ℝ)
  | 5 => (-3180809287 / 1000000000000 : ℝ)
  | 6 => (-632032449 / 200000000000 : ℝ)
  | 7 => (-3139161609 / 1000000000000 : ℝ)
  | 8 => (-1558902603 / 500000000000 : ℝ)
  | 9 => (-3096090857 / 1000000000000 : ℝ)
  | 10 => (-1537008191 / 500000000000 : ℝ)
  | 11 => (-1525789799 / 500000000000 : ℝ)
  | 12 => (-1514389159 / 500000000000 : ℝ)
  | 13 => (-187850647 / 62500000000 : ℝ)
  | 14 => (-2982073509 / 1000000000000 : ℝ)
  | 15 => (-369770699 / 125000000000 : ℝ)
  | 16 => (-586776881 / 200000000000 : ℝ)
  | 17 => (-1454613873 / 500000000000 : ℝ)
  | 18 => (-2884193413 / 1000000000000 : ℝ)
  | 19 => (-2858779199 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch058Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3259904883 / 1000000000000 : ℝ)
  | 1 => (-3240650541 / 1000000000000 : ℝ)
  | 2 => (-805262817 / 250000000000 : ℝ)
  | 3 => (-640220981 / 200000000000 : ℝ)
  | 4 => (-1590404643 / 500000000000 : ℝ)
  | 5 => (-790040561 / 250000000000 : ℝ)
  | 6 => (-392395201 / 125000000000 : ℝ)
  | 7 => (-623561041 / 200000000000 : ℝ)
  | 8 => (-387011357 / 125000000000 : ℝ)
  | 9 => (-3074016381 / 1000000000000 : ℝ)
  | 10 => (-3051579597 / 1000000000000 : ℝ)
  | 11 => (-3028778317 / 1000000000000 : ℝ)
  | 12 => (-3005610351 / 1000000000000 : ℝ)
  | 13 => (-745518377 / 250000000000 : ℝ)
  | 14 => (-2958165591 / 1000000000000 : ℝ)
  | 15 => (-733471101 / 250000000000 : ℝ)
  | 16 => (-581845549 / 200000000000 : ℝ)
  | 17 => (-721048353 / 250000000000 : ℝ)
  | 18 => (-1429389599 / 500000000000 : ℝ)
  | 19 => (-177061431 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch058Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1160 : ℝ) + (j.val : ℝ)) / 1600)
      (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch058Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch058Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1160 : ℝ) + (j.val : ℝ)) / 1600)
    (((1160 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch058Neg25WeightLower j.val) (hpThetaShiftTwoBatch058Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch058Neg25WeightLower, hpThetaShiftTwoBatch058Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch058Neg25_integral_bounds :
    (-95372783 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (58 / 80 : ℝ) ((58 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-23144827 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1160 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch058Lower hpThetaJensenCellsBatch058Upper
    hpThetaShiftTwoBatch058Neg25WeightLower hpThetaShiftTwoBatch058Neg25WeightUpper hpThetaJensenCellsBatch058_bounds hpThetaShiftTwoBatch058Neg25_weight_bounds
  have hl : (-95372783 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch058Lower j * hpThetaShiftTwoBatch058Neg25WeightLower j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftTwoBatch058Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftTwoBatch058Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch058Lower j * hpThetaShiftTwoBatch058Neg25WeightUpper j)
        (hpThetaJensenCellsBatch058Upper j * hpThetaShiftTwoBatch058Neg25WeightUpper j) / 1600) ≤ (-23144827 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch058Lower, hpThetaJensenCellsBatch058Upper,
      hpThetaShiftTwoBatch058Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1160 : ℝ) / 1600 = 58 / 80 by norm_num,
    show ((1160 : ℝ) + 20) / 1600 = (58 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch058Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch058Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch058Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch058Neg25_integral_bounds
end HodgeProofHP
