/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch065

/-! Exact signed weight and batch integral certificates, batch 65 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch065Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-362971274723 / 250000000000 : ℝ)
  | 1 => (-1466298255129 / 1000000000000 : ℝ)
  | 2 => (-1480834112051 / 1000000000000 : ℝ)
  | 3 => (-1495493562273 / 1000000000000 : ℝ)
  | 4 => (-377569375977 / 250000000000 : ℝ)
  | 5 => (-381296710147 / 250000000000 : ℝ)
  | 6 => (-1540222481503 / 1000000000000 : ℝ)
  | 7 => (-77769267071 / 50000000000 : ℝ)
  | 8 => (-392669085179 / 250000000000 : ℝ)
  | 9 => (-793048202703 / 500000000000 : ℝ)
  | 10 => (-800823233587 / 500000000000 : ℝ)
  | 11 => (-323465492679 / 200000000000 : ℝ)
  | 12 => (-408285084293 / 250000000000 : ℝ)
  | 13 => (-1649086037361 / 1000000000000 : ℝ)
  | 14 => (-1665165518601 / 1000000000000 : ℝ)
  | 15 => (-840689870671 / 500000000000 : ℝ)
  | 16 => (-848864835939 / 500000000000 : ℝ)
  | 17 => (-428554070593 / 250000000000 : ℝ)
  | 18 => (-173084055089 / 100000000000 : ℝ)
  | 19 => (-436900865357 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch065Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-44924804881 / 31250000000 : ℝ)
  | 1 => (-1451885098891 / 1000000000000 : ℝ)
  | 2 => (-183287281891 / 125000000000 : ℝ)
  | 3 => (-29616682241 / 20000000000 : ℝ)
  | 4 => (-46734173821 / 31250000000 : ℝ)
  | 5 => (-1510277503907 / 1000000000000 : ℝ)
  | 6 => (-1525186840587 / 1000000000000 : ℝ)
  | 7 => (-770111240751 / 500000000000 : ℝ)
  | 8 => (-1555385341419 / 1000000000000 : ℝ)
  | 9 => (-314135268143 / 200000000000 : ℝ)
  | 10 => (-317219281081 / 200000000000 : ℝ)
  | 11 => (-1601646467173 / 1000000000000 : ℝ)
  | 12 => (-808663731697 / 500000000000 : ℝ)
  | 13 => (-1633140337171 / 1000000000000 : ℝ)
  | 14 => (-20613575467 / 12500000000 : ℝ)
  | 15 => (-8325827593 / 5000000000 : ℝ)
  | 16 => (-1681379741341 / 1000000000000 : ℝ)
  | 17 => (-1697729671877 / 1000000000000 : ℝ)
  | 18 => (-1714216282371 / 1000000000000 : ℝ)
  | 19 => (-1730840550889 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch065Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1300 : ℝ) + (j.val : ℝ)) / 1600)
      (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch065Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch065Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1300 : ℝ) + (j.val : ℝ)) / 1600)
    (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch065Neg100WeightLower j.val) (hpThetaShiftTwoBatch065Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch065Neg100WeightLower, hpThetaShiftTwoBatch065Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch065Neg100_integral_bounds :
    (-1389096537 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-670303 / 125000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch065Lower hpThetaJensenCellsBatch065Upper
    hpThetaShiftTwoBatch065Neg100WeightLower hpThetaShiftTwoBatch065Neg100WeightUpper hpThetaJensenCellsBatch065_bounds hpThetaShiftTwoBatch065Neg100_weight_bounds
  have hl : (-1389096537 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch065Lower j * hpThetaShiftTwoBatch065Neg100WeightLower j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftTwoBatch065Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftTwoBatch065Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch065Lower j * hpThetaShiftTwoBatch065Neg100WeightUpper j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftTwoBatch065Neg100WeightUpper j) / 1600) ≤ (-670303 / 125000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftTwoBatch065Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1300 : ℝ) / 1600 = 65 / 80 by norm_num,
    show ((1300 : ℝ) + 20) / 1600 = (65 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch065Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-34728873589 / 250000000000 : ℝ)
  | 1 => (-28186868819 / 200000000000 : ℝ)
  | 2 => (-71487376251 / 500000000000 : ℝ)
  | 3 => (-36259225453 / 250000000000 : ℝ)
  | 4 => (-147120975507 / 1000000000000 : ℝ)
  | 5 => (-74613579161 / 500000000000 : ℝ)
  | 6 => (-121084509 / 800000000 : ℝ)
  | 7 => (-153506596551 / 1000000000000 : ℝ)
  | 8 => (-155680227757 / 1000000000000 : ℝ)
  | 9 => (-39469179921 / 250000000000 : ℝ)
  | 10 => (-160096263429 / 1000000000000 : ℝ)
  | 11 => (-162339051389 / 1000000000000 : ℝ)
  | 12 => (-8230263863 / 50000000000 : ℝ)
  | 13 => (-83447568023 / 500000000000 : ℝ)
  | 14 => (-169208824067 / 1000000000000 : ℝ)
  | 15 => (-85773269483 / 500000000000 : ℝ)
  | 16 => (-173908479717 / 1000000000000 : ℝ)
  | 17 => (-17629484663 / 100000000000 : ℝ)
  | 18 => (-2233823017 / 12500000000 : ℝ)
  | 19 => (-36228333383 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch065Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-27383604457 / 200000000000 : ℝ)
  | 1 => (-27783098871 / 200000000000 : ℝ)
  | 2 => (-70467172047 / 500000000000 : ℝ)
  | 3 => (-142974752501 / 1000000000000 : ℝ)
  | 4 => (-145036901811 / 1000000000000 : ℝ)
  | 5 => (-73560487753 / 500000000000 : ℝ)
  | 6 => (-149227158321 / 1000000000000 : ℝ)
  | 7 => (-151355636249 / 1000000000000 : ℝ)
  | 8 => (-3070131931 / 20000000000 : ℝ)
  | 9 => (-38920056939 / 250000000000 : ℝ)
  | 10 => (-157876719683 / 1000000000000 : ℝ)
  | 11 => (-40024065857 / 250000000000 : ℝ)
  | 12 => (-40584762847 / 250000000000 : ℝ)
  | 13 => (-164605277259 / 1000000000000 : ℝ)
  | 14 => (-33379027209 / 200000000000 : ℝ)
  | 15 => (-84604412033 / 500000000000 : ℝ)
  | 16 => (-34309307793 / 200000000000 : ℝ)
  | 17 => (-43477119929 / 250000000000 : ℝ)
  | 18 => (-176294846629 / 1000000000000 : ℝ)
  | 19 => (-178705841359 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch065Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1300 : ℝ) + (j.val : ℝ)) / 1600)
      (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch065Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch065Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1300 : ℝ) + (j.val : ℝ)) / 1600)
    (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch065Neg65WeightLower j.val) (hpThetaShiftTwoBatch065Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch065Neg65WeightLower, hpThetaShiftTwoBatch065Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch065Neg65_integral_bounds :
    (-553489227 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-132977431 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch065Lower hpThetaJensenCellsBatch065Upper
    hpThetaShiftTwoBatch065Neg65WeightLower hpThetaShiftTwoBatch065Neg65WeightUpper hpThetaJensenCellsBatch065_bounds hpThetaShiftTwoBatch065Neg65_weight_bounds
  have hl : (-553489227 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch065Lower j * hpThetaShiftTwoBatch065Neg65WeightLower j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftTwoBatch065Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftTwoBatch065Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch065Lower j * hpThetaShiftTwoBatch065Neg65WeightUpper j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftTwoBatch065Neg65WeightUpper j) / 1600) ≤ (-132977431 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftTwoBatch065Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1300 : ℝ) / 1600 = 65 / 80 by norm_num,
    show ((1300 : ℝ) + 20) / 1600 = (65 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch065Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (21557042379 / 1000000000000 : ℝ)
  | 1 => (5372675733 / 250000000000 : ℝ)
  | 2 => (4284287967 / 200000000000 : ℝ)
  | 3 => (4269843251 / 200000000000 : ℝ)
  | 4 => (21273995053 / 1000000000000 : ℝ)
  | 5 => (21195738777 / 1000000000000 : ℝ)
  | 6 => (10557204831 / 500000000000 : ℝ)
  | 7 => (2102996963 / 100000000000 : ℝ)
  | 8 => (5235595071 / 250000000000 : ℝ)
  | 9 => (651612591 / 31250000000 : ℝ)
  | 10 => (5189399619 / 250000000000 : ℝ)
  | 11 => (1033016381 / 50000000000 : ℝ)
  | 12 => (10279875331 / 500000000000 : ℝ)
  | 13 => (20455827591 / 1000000000000 : ℝ)
  | 14 => (20348518071 / 1000000000000 : ℝ)
  | 15 => (20237781433 / 1000000000000 : ℝ)
  | 16 => (804943067 / 40000000000 : ℝ)
  | 17 => (10002931231 / 500000000000 : ℝ)
  | 18 => (31069683 / 1562500000 : ℝ)
  | 19 => (246996733 / 12500000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch065Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (216204947 / 10000000000 : ℝ)
  | 1 => (1077852119 / 50000000000 : ℝ)
  | 2 => (21490702933 / 1000000000000 : ℝ)
  | 3 => (5355359959 / 250000000000 : ℝ)
  | 4 => (5212211 / 244140625 : ℝ)
  | 5 => (10636997527 / 500000000000 : ℝ)
  | 6 => (10597869389 / 500000000000 : ℝ)
  | 7 => (21114409663 / 1000000000000 : ℝ)
  | 8 => (21029969631 / 1000000000000 : ℝ)
  | 9 => (4188476057 / 200000000000 : ℝ)
  | 10 => (20851602913 / 1000000000000 : ℝ)
  | 11 => (20757598477 / 1000000000000 : ℝ)
  | 12 => (20660327621 / 1000000000000 : ℝ)
  | 13 => (20559750663 / 1000000000000 : ℝ)
  | 14 => (2556978449 / 125000000000 : ℝ)
  | 15 => (2543564759 / 125000000000 : ℝ)
  | 16 => (10118890717 / 500000000000 : ℝ)
  | 17 => (5030894169 / 250000000000 : ℝ)
  | 18 => (20005862463 / 1000000000000 : ℝ)
  | 19 => (19884597121 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch065Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1300 : ℝ) + (j.val : ℝ)) / 1600)
      (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch065Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch065Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1300 : ℝ) + (j.val : ℝ)) / 1600)
    (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch065Neg45WeightLower j.val) (hpThetaShiftTwoBatch065Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch065Neg45WeightLower, hpThetaShiftTwoBatch065Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch065Neg45_integral_bounds :
    (8872953 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (36577329 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch065Lower hpThetaJensenCellsBatch065Upper
    hpThetaShiftTwoBatch065Neg45WeightLower hpThetaShiftTwoBatch065Neg45WeightUpper hpThetaJensenCellsBatch065_bounds hpThetaShiftTwoBatch065Neg45_weight_bounds
  have hl : (8872953 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch065Lower j * hpThetaShiftTwoBatch065Neg45WeightLower j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftTwoBatch065Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftTwoBatch065Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch065Lower j * hpThetaShiftTwoBatch065Neg45WeightUpper j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftTwoBatch065Neg45WeightUpper j) / 1600) ≤ (36577329 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftTwoBatch065Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1300 : ℝ) / 1600 = 65 / 80 by norm_num,
    show ((1300 : ℝ) + 20) / 1600 = (65 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch065Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (738427763 / 200000000000 : ℝ)
  | 1 => (3780400853 / 1000000000000 : ℝ)
  | 2 => (3869304443 / 1000000000000 : ℝ)
  | 3 => (15464263 / 3906250000 : ℝ)
  | 4 => (4049043239 / 1000000000000 : ℝ)
  | 5 => (2069940949 / 500000000000 : ℝ)
  | 6 => (264460563 / 62500000000 : ℝ)
  | 7 => (2161753133 / 500000000000 : ℝ)
  | 8 => (88325907 / 20000000000 : ℝ)
  | 9 => (563717241 / 125000000000 : ℝ)
  | 10 => (2301917827 / 500000000000 : ℝ)
  | 11 => (4698590167 / 1000000000000 : ℝ)
  | 12 => (958800619 / 200000000000 : ℝ)
  | 13 => (97801521 / 20000000000 : ℝ)
  | 14 => (4986810629 / 1000000000000 : ℝ)
  | 15 => (1016841683 / 200000000000 : ℝ)
  | 16 => (5182270979 / 1000000000000 : ℝ)
  | 17 => (2640499937 / 500000000000 : ℝ)
  | 18 => (5380396639 / 1000000000000 : ℝ)
  | 19 => (5480462797 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch065Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1890200427 / 500000000000 : ℝ)
  | 1 => (967326111 / 250000000000 : ℝ)
  | 2 => (3958851329 / 1000000000000 : ℝ)
  | 3 => (101226081 / 25000000000 : ℝ)
  | 4 => (4139881899 / 1000000000000 : ℝ)
  | 5 => (4231369009 / 1000000000000 : ℝ)
  | 6 => (4323506267 / 1000000000000 : ℝ)
  | 7 => (4416295351 / 1000000000000 : ℝ)
  | 8 => (4509737929 / 1000000000000 : ℝ)
  | 9 => (920767131 / 200000000000 : ℝ)
  | 10 => (587323771 / 125000000000 : ℝ)
  | 11 => (599250387 / 125000000000 : ℝ)
  | 12 => (4890076051 / 1000000000000 : ℝ)
  | 13 => (498681063 / 100000000000 : ℝ)
  | 14 => (158881513 / 31250000000 : ℝ)
  | 15 => (259113549 / 50000000000 : ℝ)
  | 16 => (42247999 / 8000000000 : ℝ)
  | 17 => (33627479 / 6250000000 : ℝ)
  | 18 => (2740231399 / 500000000000 : ℝ)
  | 19 => (279059993 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch065Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1300 : ℝ) + (j.val : ℝ)) / 1600)
      (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch065Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch065Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1300 : ℝ) + (j.val : ℝ)) / 1600)
    (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch065Neg25WeightLower j.val) (hpThetaShiftTwoBatch065Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch065Neg25WeightLower, hpThetaShiftTwoBatch065Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch065Neg25_integral_bounds :
    (15400323 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (8065883 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch065Lower hpThetaJensenCellsBatch065Upper
    hpThetaShiftTwoBatch065Neg25WeightLower hpThetaShiftTwoBatch065Neg25WeightUpper hpThetaJensenCellsBatch065_bounds hpThetaShiftTwoBatch065Neg25_weight_bounds
  have hl : (15400323 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch065Lower j * hpThetaShiftTwoBatch065Neg25WeightLower j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftTwoBatch065Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftTwoBatch065Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch065Lower j * hpThetaShiftTwoBatch065Neg25WeightUpper j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftTwoBatch065Neg25WeightUpper j) / 1600) ≤ (8065883 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftTwoBatch065Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1300 : ℝ) / 1600 = 65 / 80 by norm_num,
    show ((1300 : ℝ) + 20) / 1600 = (65 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch065Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch065Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch065Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch065Neg25_integral_bounds
end HodgeProofHP
