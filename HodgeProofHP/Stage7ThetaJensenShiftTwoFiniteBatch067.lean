/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch067

/-! Exact signed weight and batch integral certificates, batch 67 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch067Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-533364546139 / 250000000000 : ℝ)
  | 1 => (-2153532560809 / 1000000000000 : ℝ)
  | 2 => (-543442479621 / 250000000000 : ℝ)
  | 3 => (-438834278641 / 200000000000 : ℝ)
  | 4 => (-2214738127311 / 1000000000000 : ℝ)
  | 5 => (-447094253979 / 200000000000 : ℝ)
  | 6 => (-2256371976833 / 1000000000000 : ℝ)
  | 7 => (-1138720705411 / 500000000000 : ℝ)
  | 8 => (-2298680741407 / 1000000000000 : ℝ)
  | 9 => (-1160045572511 / 500000000000 : ℝ)
  | 10 => (-1170836902509 / 500000000000 : ℝ)
  | 11 => (-1181714955851 / 500000000000 : ℝ)
  | 12 => (-477072132473 / 200000000000 : ℝ)
  | 13 => (-601866815331 / 250000000000 : ℝ)
  | 14 => (-607437729987 / 250000000000 : ℝ)
  | 15 => (-2452212856699 / 1000000000000 : ℝ)
  | 16 => (-618713574291 / 250000000000 : ℝ)
  | 17 => (-2497676474091 / 1000000000000 : ℝ)
  | 18 => (-1260340313711 / 500000000000 : ℝ)
  | 19 => (-2543868004329 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch067Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2113545660787 / 1000000000000 : ℝ)
  | 1 => (-426691636911 / 200000000000 : ℝ)
  | 2 => (-269191570101 / 125000000000 : ℝ)
  | 3 => (-2173769918483 / 1000000000000 : ℝ)
  | 4 => (-548542848301 / 250000000000 : ℝ)
  | 5 => (-221473812731 / 100000000000 : ℝ)
  | 6 => (-1117735634947 / 500000000000 : ℝ)
  | 7 => (-17627906069 / 7812500000 : ℝ)
  | 8 => (-2277441410821 / 1000000000000 : ℝ)
  | 9 => (-1149340370703 / 500000000000 : ℝ)
  | 10 => (-2320091145021 / 1000000000000 : ℝ)
  | 11 => (-2341673805017 / 1000000000000 : ℝ)
  | 12 => (-2363429911701 / 1000000000000 : ℝ)
  | 13 => (-596340165591 / 250000000000 : ℝ)
  | 14 => (-2407467261323 / 1000000000000 : ℝ)
  | 15 => (-2429750919947 / 1000000000000 : ℝ)
  | 16 => (-1226106428349 / 500000000000 : ℝ)
  | 17 => (-2474854297163 / 1000000000000 : ℝ)
  | 18 => (-249767647409 / 100000000000 : ℝ)
  | 19 => (-2520680627421 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch067Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1340 : ℝ) + (j.val : ℝ)) / 1600)
      (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch067Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch067Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1340 : ℝ) + (j.val : ℝ)) / 1600)
    (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch067Neg100WeightLower j.val) (hpThetaShiftTwoBatch067Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch067Neg100WeightLower, hpThetaShiftTwoBatch067Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch067Neg100_integral_bounds :
    (-3995498973 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-3853981669 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch067Lower hpThetaJensenCellsBatch067Upper
    hpThetaShiftTwoBatch067Neg100WeightLower hpThetaShiftTwoBatch067Neg100WeightUpper hpThetaJensenCellsBatch067_bounds hpThetaShiftTwoBatch067Neg100_weight_bounds
  have hl : (-3995498973 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch067Lower j * hpThetaShiftTwoBatch067Neg100WeightLower j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftTwoBatch067Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftTwoBatch067Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch067Lower j * hpThetaShiftTwoBatch067Neg100WeightUpper j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftTwoBatch067Neg100WeightUpper j) / 1600) ≤ (-3853981669 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftTwoBatch067Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1340 : ℝ) / 1600 = 67 / 80 by norm_num,
    show ((1340 : ℝ) + 20) / 1600 = (67 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch067Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-238404209631 / 1000000000000 : ℝ)
  | 1 => (-241440504781 / 1000000000000 : ℝ)
  | 2 => (-244506690317 / 1000000000000 : ℝ)
  | 3 => (-123801501983 / 500000000000 : ℝ)
  | 4 => (-250729685001 / 1000000000000 : ℝ)
  | 5 => (-31735871781 / 125000000000 : ℝ)
  | 6 => (-128537557047 / 500000000000 : ℝ)
  | 7 => (-130147174249 / 500000000000 : ℝ)
  | 8 => (-131772461497 / 500000000000 : ℝ)
  | 9 => (-266827084703 / 1000000000000 : ℝ)
  | 10 => (-270141082343 / 1000000000000 : ℝ)
  | 11 => (-273487166231 / 1000000000000 : ℝ)
  | 12 => (-276865588299 / 1000000000000 : ℝ)
  | 13 => (-140138301049 / 500000000000 : ℝ)
  | 14 => (-70930115701 / 250000000000 : ℝ)
  | 15 => (-57439485447 / 200000000000 : ℝ)
  | 16 => (-290707753851 / 1000000000000 : ℝ)
  | 17 => (-294251702767 / 1000000000000 : ℝ)
  | 18 => (-297829535759 / 1000000000000 : ℝ)
  | 19 => (-150720758139 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch067Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-235397568673 / 1000000000000 : ℝ)
  | 1 => (-23840420963 / 100000000000 : ℝ)
  | 2 => (-12072025239 / 50000000000 : ℝ)
  | 3 => (-61126672579 / 250000000000 : ℝ)
  | 4 => (-49520600793 / 200000000000 : ℝ)
  | 5 => (-50145937 / 200000000 : ℝ)
  | 6 => (-253886974247 / 1000000000000 : ℝ)
  | 7 => (-257075114093 / 1000000000000 : ℝ)
  | 8 => (-260294348497 / 1000000000000 : ℝ)
  | 9 => (-263544922993 / 1000000000000 : ℝ)
  | 10 => (-133413542351 / 500000000000 : ℝ)
  | 11 => (-135070541171 / 500000000000 : ℝ)
  | 12 => (-27348716623 / 100000000000 : ℝ)
  | 13 => (-138432794149 / 500000000000 : ℝ)
  | 14 => (-280276602097 / 1000000000000 : ℝ)
  | 15 => (-283720462803 / 1000000000000 : ℝ)
  | 16 => (-143598713617 / 500000000000 : ℝ)
  | 17 => (-5814155077 / 20000000000 : ℝ)
  | 18 => (-147125851383 / 500000000000 : ℝ)
  | 19 => (-148914767879 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch067Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1340 : ℝ) + (j.val : ℝ)) / 1600)
      (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch067Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch067Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1340 : ℝ) + (j.val : ℝ)) / 1600)
    (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch067Neg65WeightLower j.val) (hpThetaShiftTwoBatch067Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch067Neg65WeightLower, hpThetaShiftTwoBatch067Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch067Neg65_integral_bounds :
    (-114925563 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-110511333 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch067Lower hpThetaJensenCellsBatch067Upper
    hpThetaShiftTwoBatch067Neg65WeightLower hpThetaShiftTwoBatch067Neg65WeightUpper hpThetaJensenCellsBatch067_bounds hpThetaShiftTwoBatch067Neg65_weight_bounds
  have hl : (-114925563 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch067Lower j * hpThetaShiftTwoBatch067Neg65WeightLower j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftTwoBatch067Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftTwoBatch067Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch067Lower j * hpThetaShiftTwoBatch067Neg65WeightUpper j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftTwoBatch067Neg65WeightUpper j) / 1600) ≤ (-110511333 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftTwoBatch067Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1340 : ℝ) / 1600 = 67 / 80 by norm_num,
    show ((1340 : ℝ) + 20) / 1600 = (67 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch067Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (16229580107 / 1000000000000 : ℝ)
  | 1 => (16014331031 / 1000000000000 : ℝ)
  | 2 => (3158884827 / 200000000000 : ℝ)
  | 3 => (15569808631 / 1000000000000 : ℝ)
  | 4 => (7670216669 / 500000000000 : ℝ)
  | 5 => (15106246677 / 1000000000000 : ℝ)
  | 6 => (7433598337 / 500000000000 : ℝ)
  | 7 => (14623230953 / 1000000000000 : ℝ)
  | 8 => (14374296733 / 1000000000000 : ℝ)
  | 9 => (1412034083 / 100000000000 : ℝ)
  | 10 => (13861309653 / 1000000000000 : ℝ)
  | 11 => (6798574599 / 500000000000 : ℝ)
  | 12 => (3331951263 / 250000000000 : ℝ)
  | 13 => (2610644477 / 200000000000 : ℝ)
  | 14 => (12773345951 / 1000000000000 : ℝ)
  | 15 => (6244060041 / 500000000000 : ℝ)
  | 16 => (1219748869 / 100000000000 : ℝ)
  | 17 => (11901395263 / 1000000000000 : ℝ)
  | 18 => (11599782859 / 1000000000000 : ℝ)
  | 19 => (1129259411 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch067Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (16440221761 / 1000000000000 : ℝ)
  | 1 => (4057395027 / 250000000000 : ℝ)
  | 2 => (2001791379 / 125000000000 : ℝ)
  | 3 => (1974303017 / 125000000000 : ℝ)
  | 4 => (1946226079 / 125000000000 : ℝ)
  | 5 => (15340433339 / 1000000000000 : ℝ)
  | 6 => (7553123339 / 500000000000 : ℝ)
  | 7 => (594687867 / 40000000000 : ℝ)
  | 8 => (7311615477 / 500000000000 : ℝ)
  | 9 => (7187148367 / 500000000000 : ℝ)
  | 10 => (14120340831 / 1000000000000 : ℝ)
  | 11 => (6930654827 / 500000000000 : ℝ)
  | 12 => (13597149199 / 1000000000000 : ℝ)
  | 13 => (13327805053 / 1000000000000 : ℝ)
  | 14 => (6526611193 / 500000000000 : ℝ)
  | 15 => (399167061 / 31250000000 : ℝ)
  | 16 => (12488120083 / 1000000000000 : ℝ)
  | 17 => (12197488691 / 1000000000000 : ℝ)
  | 18 => (185959301 / 15625000000 : ℝ)
  | 19 => (579989143 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch067Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1340 : ℝ) + (j.val : ℝ)) / 1600)
      (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch067Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch067Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1340 : ℝ) + (j.val : ℝ)) / 1600)
    (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch067Neg45WeightLower j.val) (hpThetaShiftTwoBatch067Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch067Neg45WeightLower, hpThetaShiftTwoBatch067Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch067Neg45_integral_bounds :
    (11787003 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (24651401 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch067Lower hpThetaJensenCellsBatch067Upper
    hpThetaShiftTwoBatch067Neg45WeightLower hpThetaShiftTwoBatch067Neg45WeightUpper hpThetaJensenCellsBatch067_bounds hpThetaShiftTwoBatch067Neg45_weight_bounds
  have hl : (11787003 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch067Lower j * hpThetaShiftTwoBatch067Neg45WeightLower j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftTwoBatch067Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftTwoBatch067Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch067Lower j * hpThetaShiftTwoBatch067Neg45WeightUpper j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftTwoBatch067Neg45WeightUpper j) / 1600) ≤ (24651401 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftTwoBatch067Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1340 : ℝ) / 1600 = 67 / 80 by norm_num,
    show ((1340 : ℝ) + 20) / 1600 = (67 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch067Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (7739008543 / 1000000000000 : ℝ)
  | 1 => (3927076769 / 500000000000 : ℝ)
  | 2 => (7969998303 / 1000000000000 : ℝ)
  | 3 => (8086543933 / 1000000000000 : ℝ)
  | 4 => (512736969 / 62500000000 : ℝ)
  | 5 => (832174207 / 100000000000 : ℝ)
  | 6 => (1688079333 / 200000000000 : ℝ)
  | 7 => (85597563 / 10000000000 : ℝ)
  | 8 => (8679821967 / 1000000000000 : ℝ)
  | 9 => (8800594633 / 1000000000000 : ℝ)
  | 10 => (4461037623 / 500000000000 : ℝ)
  | 11 => (9044264731 / 1000000000000 : ℝ)
  | 12 => (2291790997 / 250000000000 : ℝ)
  | 13 => (9290773897 / 1000000000000 : ℝ)
  | 14 => (4707547657 / 500000000000 : ℝ)
  | 15 => (9540129073 / 1000000000000 : ℝ)
  | 16 => (9665875983 / 1000000000000 : ℝ)
  | 17 => (9792336829 / 1000000000000 : ℝ)
  | 18 => (9919512373 / 1000000000000 : ℝ)
  | 19 => (1255925419 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch067Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (7854153539 / 1000000000000 : ℝ)
  | 1 => (249062447 / 31250000000 : ℝ)
  | 2 => (4043271967 / 500000000000 : ℝ)
  | 3 => (1640758301 / 200000000000 : ℝ)
  | 4 => (8321742071 / 1000000000000 : ℝ)
  | 5 => (4220198333 / 500000000000 : ℝ)
  | 6 => (8559756301 / 1000000000000 : ℝ)
  | 7 => (542488873 / 62500000000 : ℝ)
  | 8 => (4400297317 / 500000000000 : ℝ)
  | 9 => (8922075247 / 1000000000000 : ℝ)
  | 10 => (2261066183 / 250000000000 : ℝ)
  | 11 => (9167163989 / 1000000000000 : ℝ)
  | 12 => (4645386949 / 500000000000 : ℝ)
  | 13 => (1883019063 / 200000000000 : ℝ)
  | 14 => (4770064537 / 500000000000 : ℝ)
  | 15 => (604117249 / 62500000000 : ℝ)
  | 16 => (979233683 / 100000000000 : ℝ)
  | 17 => (4959756187 / 500000000000 : ℝ)
  | 18 => (10047403353 / 1000000000000 : ℝ)
  | 19 => (10176010481 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch067Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1340 : ℝ) + (j.val : ℝ)) / 1600)
      (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch067Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch067Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1340 : ℝ) + (j.val : ℝ)) / 1600)
    (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch067Neg25WeightLower j.val) (hpThetaShiftTwoBatch067Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch067Neg25WeightLower, hpThetaShiftTwoBatch067Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch067Neg25_integral_bounds :
    (368737 / 25000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (119993 / 7812500000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch067Lower hpThetaJensenCellsBatch067Upper
    hpThetaShiftTwoBatch067Neg25WeightLower hpThetaShiftTwoBatch067Neg25WeightUpper hpThetaJensenCellsBatch067_bounds hpThetaShiftTwoBatch067Neg25_weight_bounds
  have hl : (368737 / 25000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch067Lower j * hpThetaShiftTwoBatch067Neg25WeightLower j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftTwoBatch067Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftTwoBatch067Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch067Lower j * hpThetaShiftTwoBatch067Neg25WeightUpper j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftTwoBatch067Neg25WeightUpper j) / 1600) ≤ (119993 / 7812500000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftTwoBatch067Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1340 : ℝ) / 1600 = 67 / 80 by norm_num,
    show ((1340 : ℝ) + 20) / 1600 = (67 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch067Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch067Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch067Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch067Neg25_integral_bounds
end HodgeProofHP
