/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch075

/-! Exact signed weight and batch integral certificates, batch 75 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch075Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4193081035439 / 500000000000 : ℝ)
  | 1 => (-528265655951 / 62500000000 : ℝ)
  | 2 => (-2129698789089 / 250000000000 : ℝ)
  | 3 => (-4292899394037 / 500000000000 : ℝ)
  | 4 => (-4326632069089 / 500000000000 : ℝ)
  | 5 => (-4360596984283 / 500000000000 : ℝ)
  | 6 => (-8789591055287 / 1000000000000 : ℝ)
  | 7 => (-4429229094303 / 500000000000 : ℝ)
  | 8 => (-446389908653 / 50000000000 : ℝ)
  | 9 => (-4498806913761 / 500000000000 : ℝ)
  | 10 => (-566744249079 / 62500000000 : ℝ)
  | 11 => (-1827736698803 / 200000000000 : ℝ)
  | 12 => (-4604971608013 / 500000000000 : ℝ)
  | 13 => (-9281690028131 / 1000000000000 : ℝ)
  | 14 => (-2338481705453 / 250000000000 : ℝ)
  | 15 => (-9426656503257 / 1000000000000 : ℝ)
  | 16 => (-9499881993427 / 1000000000000 : ℝ)
  | 17 => (-4786803114059 / 500000000000 : ℝ)
  | 18 => (-4823916079011 / 500000000000 : ℝ)
  | 19 => (-1944512549759 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch075Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8320527163537 / 1000000000000 : ℝ)
  | 1 => (-8386162070877 / 1000000000000 : ℝ)
  | 2 => (-1690450099043 / 200000000000 : ℝ)
  | 3 => (-1703759031271 / 200000000000 : ℝ)
  | 4 => (-8585798788073 / 1000000000000 : ℝ)
  | 5 => (-8653264138177 / 1000000000000 : ℝ)
  | 6 => (-1744238793713 / 200000000000 : ℝ)
  | 7 => (-4394795527643 / 500000000000 : ℝ)
  | 8 => (-1771691637721 / 200000000000 : ℝ)
  | 9 => (-8927798173059 / 1000000000000 : ℝ)
  | 10 => (-8997613827521 / 1000000000000 : ℝ)
  | 11 => (-9067907985263 / 1000000000000 : ℝ)
  | 12 => (-4569341747007 / 500000000000 : ℝ)
  | 13 => (-368397728641 / 40000000000 : ℝ)
  | 14 => (-928169002813 / 100000000000 : ℝ)
  | 15 => (-9353926821811 / 1000000000000 : ℝ)
  | 16 => (-1178332062907 / 125000000000 : ℝ)
  | 17 => (-4749940996713 / 500000000000 : ℝ)
  | 18 => (-9573606228117 / 1000000000000 : ℝ)
  | 19 => (-9647832158021 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch075Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1500 : ℝ) + (j.val : ℝ)) / 1600)
      (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch075Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch075Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1500 : ℝ) + (j.val : ℝ)) / 1600)
    (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch075Neg100WeightLower j.val) (hpThetaShiftTwoBatch075Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch075Neg100WeightLower, hpThetaShiftTwoBatch075Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch075Neg100_integral_bounds :
    (-289011263 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-555763509 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch075Lower hpThetaJensenCellsBatch075Upper
    hpThetaShiftTwoBatch075Neg100WeightLower hpThetaShiftTwoBatch075Neg100WeightUpper hpThetaJensenCellsBatch075_bounds hpThetaShiftTwoBatch075Neg100_weight_bounds
  have hl : (-289011263 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch075Lower j * hpThetaShiftTwoBatch075Neg100WeightLower j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftTwoBatch075Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftTwoBatch075Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch075Lower j * hpThetaShiftTwoBatch075Neg100WeightUpper j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftTwoBatch075Neg100WeightUpper j) / 1600) ≤ (-555763509 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftTwoBatch075Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1500 : ℝ) / 1600 = 75 / 80 by norm_num,
    show ((1500 : ℝ) + 20) / 1600 = (75 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch075Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-655892408481 / 500000000000 : ℝ)
  | 1 => (-66195398339 / 50000000000 : ℝ)
  | 2 => (-1336125168931 / 1000000000000 : ℝ)
  | 3 => (-337109259607 / 250000000000 : ℝ)
  | 4 => (-68042209683 / 50000000000 : ℝ)
  | 5 => (-686673628199 / 500000000000 : ℝ)
  | 6 => (-692973425909 / 500000000000 : ℝ)
  | 7 => (-699321804257 / 500000000000 : ℝ)
  | 8 => (-1411438158509 / 1000000000000 : ℝ)
  | 9 => (-1424331137279 / 1000000000000 : ℝ)
  | 10 => (-17966539797 / 12500000000 : ℝ)
  | 11 => (-1450414940371 / 1000000000000 : ℝ)
  | 12 => (-1463607053023 / 1000000000000 : ℝ)
  | 13 => (-1476900171141 / 1000000000000 : ℝ)
  | 14 => (-1490294947673 / 1000000000000 : ℝ)
  | 15 => (-751896019557 / 500000000000 : ℝ)
  | 16 => (-303478421103 / 200000000000 : ℝ)
  | 17 => (-3062191621 / 2000000000 : ℝ)
  | 18 => (-193112977661 / 125000000000 : ℝ)
  | 19 => (-1558816808699 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch075Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-162469388477 / 125000000000 : ℝ)
  | 1 => (-1311784816961 / 1000000000000 : ℝ)
  | 2 => (-1323907966779 / 1000000000000 : ℝ)
  | 3 => (-133612516893 / 100000000000 : ℝ)
  | 4 => (-1348437038427 / 1000000000000 : ℝ)
  | 5 => (-1360844193659 / 1000000000000 : ℝ)
  | 6 => (-1373347256397 / 1000000000000 : ℝ)
  | 7 => (-1385946851817 / 1000000000000 : ℝ)
  | 8 => (-1398643608513 / 1000000000000 : ℝ)
  | 9 => (-352859539627 / 250000000000 : ℝ)
  | 10 => (-712165568639 / 500000000000 : ℝ)
  | 11 => (-1437323183759 / 1000000000000 : ℝ)
  | 12 => (-145041494037 / 100000000000 : ℝ)
  | 13 => (-731803526511 / 500000000000 : ℝ)
  | 14 => (-73845008557 / 50000000000 : ℝ)
  | 15 => (-186286868459 / 125000000000 : ℝ)
  | 16 => (-1503792039113 / 1000000000000 : ℝ)
  | 17 => (-758696052757 / 500000000000 : ℝ)
  | 18 => (-1531095810499 / 1000000000000 : ℝ)
  | 19 => (-1544903821287 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch075Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1500 : ℝ) + (j.val : ℝ)) / 1600)
      (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch075Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch075Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1500 : ℝ) + (j.val : ℝ)) / 1600)
    (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch075Neg65WeightLower j.val) (hpThetaShiftTwoBatch075Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch075Neg65WeightLower, hpThetaShiftTwoBatch075Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch075Neg65_integral_bounds :
    (-91495063 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-43928477 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch075Lower hpThetaJensenCellsBatch075Upper
    hpThetaShiftTwoBatch075Neg65WeightLower hpThetaShiftTwoBatch075Neg65WeightUpper hpThetaJensenCellsBatch075_bounds hpThetaShiftTwoBatch075Neg65_weight_bounds
  have hl : (-91495063 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch075Lower j * hpThetaShiftTwoBatch075Neg65WeightLower j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftTwoBatch075Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftTwoBatch075Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch075Lower j * hpThetaShiftTwoBatch075Neg65WeightUpper j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftTwoBatch075Neg65WeightUpper j) / 1600) ≤ (-43928477 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftTwoBatch075Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1500 : ℝ) / 1600 = 75 / 80 by norm_num,
    show ((1500 : ℝ) + 20) / 1600 = (75 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch075Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-61987118823 / 500000000000 : ℝ)
  | 1 => (-125914857699 / 1000000000000 : ℝ)
  | 2 => (-3196878247 / 25000000000 : ℝ)
  | 3 => (-25971041103 / 200000000000 : ℝ)
  | 4 => (-16481904607 / 125000000000 : ℝ)
  | 5 => (-133875377083 / 1000000000000 : ℝ)
  | 6 => (-135915780311 / 1000000000000 : ℝ)
  | 7 => (-137976601593 / 1000000000000 : ℝ)
  | 8 => (-35014499231 / 250000000000 : ℝ)
  | 9 => (-142160123249 / 1000000000000 : ℝ)
  | 10 => (-72141569231 / 500000000000 : ℝ)
  | 11 => (-18303400177 / 125000000000 : ℝ)
  | 12 => (-37148117981 / 250000000000 : ℝ)
  | 13 => (-150779110767 / 1000000000000 : ℝ)
  | 14 => (-76493639847 / 500000000000 : ℝ)
  | 15 => (-19402142679 / 125000000000 : ℝ)
  | 16 => (-157468859687 / 1000000000000 : ℝ)
  | 17 => (-3194851983 / 20000000000 : ℝ)
  | 18 => (-324077051 / 2000000000 : ℝ)
  | 19 => (-82178402707 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch075Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-61026559657 / 500000000000 : ℝ)
  | 1 => (-24794847529 / 200000000000 : ℝ)
  | 2 => (-62957428849 / 500000000000 : ℝ)
  | 3 => (-127875129879 / 1000000000000 : ℝ)
  | 4 => (-64927602757 / 500000000000 : ℝ)
  | 5 => (-26371047371 / 200000000000 : ℝ)
  | 6 => (-66937688541 / 500000000000 : ℝ)
  | 7 => (-13591578031 / 100000000000 : ℝ)
  | 8 => (-17247075199 / 125000000000 : ℝ)
  | 9 => (-140057996923 / 1000000000000 : ℝ)
  | 10 => (-8885007703 / 62500000000 : ℝ)
  | 11 => (-144283138461 / 1000000000000 : ℝ)
  | 12 => (-29285440283 / 200000000000 : ℝ)
  | 13 => (-148592471923 / 1000000000000 : ℝ)
  | 14 => (-75389555383 / 500000000000 : ℝ)
  | 15 => (-152987279693 / 1000000000000 : ℝ)
  | 16 => (-155217141431 / 1000000000000 : ℝ)
  | 17 => (-78734429843 / 500000000000 : ℝ)
  | 18 => (-159742599149 / 1000000000000 : ℝ)
  | 19 => (-162038525499 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch075Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1500 : ℝ) + (j.val : ℝ)) / 1600)
      (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch075Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch075Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1500 : ℝ) + (j.val : ℝ)) / 1600)
    (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch075Neg45WeightLower j.val) (hpThetaShiftTwoBatch075Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch075Neg45WeightLower, hpThetaShiftTwoBatch075Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch075Neg45_integral_bounds :
    (-4564907 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-8715981 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch075Lower hpThetaJensenCellsBatch075Upper
    hpThetaShiftTwoBatch075Neg45WeightLower hpThetaShiftTwoBatch075Neg45WeightUpper hpThetaJensenCellsBatch075_bounds hpThetaShiftTwoBatch075Neg45_weight_bounds
  have hl : (-4564907 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch075Lower j * hpThetaShiftTwoBatch075Neg45WeightLower j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftTwoBatch075Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftTwoBatch075Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch075Lower j * hpThetaShiftTwoBatch075Neg45WeightUpper j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftTwoBatch075Neg45WeightUpper j) / 1600) ≤ (-8715981 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftTwoBatch075Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1500 : ℝ) / 1600 = 75 / 80 by norm_num,
    show ((1500 : ℝ) + 20) / 1600 = (75 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch075Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (8758033801 / 250000000000 : ℝ)
  | 1 => (2203248873 / 62500000000 : ℝ)
  | 2 => (8868061021 / 250000000000 : ℝ)
  | 3 => (17846457647 / 500000000000 : ℝ)
  | 4 => (35913989261 / 1000000000000 : ℝ)
  | 5 => (36135459569 / 1000000000000 : ℝ)
  | 6 => (36357319719 / 1000000000000 : ℝ)
  | 7 => (9144890783 / 250000000000 : ℝ)
  | 8 => (9200545787 / 250000000000 : ℝ)
  | 9 => (37025173023 / 1000000000000 : ℝ)
  | 10 => (37248525931 / 1000000000000 : ℝ)
  | 11 => (37472234961 / 1000000000000 : ℝ)
  | 12 => (37696293121 / 1000000000000 : ℝ)
  | 13 => (37920693331 / 1000000000000 : ℝ)
  | 14 => (38145428427 / 1000000000000 : ℝ)
  | 15 => (959262279 / 25000000000 : ℝ)
  | 16 => (7719174839 / 200000000000 : ℝ)
  | 17 => (9705392527 / 250000000000 : ℝ)
  | 18 => (39047571389 / 1000000000000 : ℝ)
  | 19 => (39273870441 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch075Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (35251981969 / 1000000000000 : ℝ)
  | 1 => (7094448817 / 200000000000 : ℝ)
  | 2 => (7138583059 / 200000000000 : ℝ)
  | 3 => (17956994631 / 500000000000 : ℝ)
  | 4 => (3613545957 / 100000000000 : ℝ)
  | 5 => (908932993 / 25000000000 : ℝ)
  | 6 => (36579563133 / 1000000000000 : ℝ)
  | 7 => (36802183149 / 1000000000000 : ℝ)
  | 8 => (1157036657 / 31250000000 : ℝ)
  | 9 => (9312131483 / 250000000000 : ℝ)
  | 10 => (18736117481 / 500000000000 : ℝ)
  | 11 => (18848146561 / 500000000000 : ℝ)
  | 12 => (9480173333 / 250000000000 : ℝ)
  | 13 => (9536357107 / 250000000000 : ℝ)
  | 14 => (38370491161 / 1000000000000 : ℝ)
  | 15 => (9648968549 / 250000000000 : ℝ)
  | 16 => (38821570109 / 1000000000000 : ℝ)
  | 17 => (3904757139 / 100000000000 : ℝ)
  | 18 => (19636935221 / 500000000000 : ℝ)
  | 19 => (39500459577 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch075Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1500 : ℝ) + (j.val : ℝ)) / 1600)
      (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch075Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch075Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1500 : ℝ) + (j.val : ℝ)) / 1600)
    (((1500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch075Neg25WeightLower j.val) (hpThetaShiftTwoBatch075Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch075Neg25WeightLower, hpThetaShiftTwoBatch075Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch075Neg25_integral_bounds :
    (2304267 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (75 / 80 : ℝ) ((75 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (2392307 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch075Lower hpThetaJensenCellsBatch075Upper
    hpThetaShiftTwoBatch075Neg25WeightLower hpThetaShiftTwoBatch075Neg25WeightUpper hpThetaJensenCellsBatch075_bounds hpThetaShiftTwoBatch075Neg25_weight_bounds
  have hl : (2304267 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch075Lower j * hpThetaShiftTwoBatch075Neg25WeightLower j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftTwoBatch075Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftTwoBatch075Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch075Lower j * hpThetaShiftTwoBatch075Neg25WeightUpper j)
        (hpThetaJensenCellsBatch075Upper j * hpThetaShiftTwoBatch075Neg25WeightUpper j) / 1600) ≤ (2392307 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch075Lower, hpThetaJensenCellsBatch075Upper,
      hpThetaShiftTwoBatch075Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1500 : ℝ) / 1600 = 75 / 80 by norm_num,
    show ((1500 : ℝ) + 20) / 1600 = (75 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch075Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch075Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch075Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch075Neg25_integral_bounds
end HodgeProofHP
