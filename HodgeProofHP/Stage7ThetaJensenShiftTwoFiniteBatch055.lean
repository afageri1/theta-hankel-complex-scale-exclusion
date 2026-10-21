/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch055

/-! Exact signed weight and batch integral certificates, batch 55 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch055Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8513321567 / 62500000000 : ℝ)
  | 1 => (-1079924409 / 7812500000 : ℝ)
  | 2 => (-140271084511 / 1000000000000 : ℝ)
  | 3 => (-2223994537 / 15625000000 : ℝ)
  | 4 => (-144424248507 / 1000000000000 : ℝ)
  | 5 => (-146537107279 / 1000000000000 : ℝ)
  | 6 => (-148674456823 / 1000000000000 : ℝ)
  | 7 => (-37709132267 / 250000000000 : ℝ)
  | 8 => (-153023557753 / 1000000000000 : ℝ)
  | 9 => (-155235778433 / 1000000000000 : ℝ)
  | 10 => (-157473428491 / 1000000000000 : ℝ)
  | 11 => (-9983546697 / 62500000000 : ℝ)
  | 12 => (-81012987747 / 500000000000 : ℝ)
  | 13 => (-20542669557 / 125000000000 : ℝ)
  | 14 => (-20835391857 / 125000000000 : ℝ)
  | 15 => (-169051557399 / 1000000000000 : ℝ)
  | 16 => (-10715429543 / 62500000000 : ℝ)
  | 17 => (-86934665619 / 500000000000 : ℝ)
  | 18 => (-176319185489 / 1000000000000 : ℝ)
  | 19 => (-35759337963 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch055Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-67109661799 / 500000000000 : ℝ)
  | 1 => (-136213145071 / 1000000000000 : ℝ)
  | 2 => (-138230324351 / 1000000000000 : ℝ)
  | 3 => (-14027108451 / 100000000000 : ℝ)
  | 4 => (-142335650367 / 1000000000000 : ℝ)
  | 5 => (-72212124253 / 500000000000 : ℝ)
  | 6 => (-73268553639 / 500000000000 : ℝ)
  | 7 => (-74337228411 / 500000000000 : ℝ)
  | 8 => (-150836529067 / 1000000000000 : ℝ)
  | 9 => (-19127944719 / 125000000000 : ℝ)
  | 10 => (-1212779519 / 7812500000 : ℝ)
  | 11 => (-15747342849 / 100000000000 : ℝ)
  | 12 => (-159736747151 / 1000000000000 : ℝ)
  | 13 => (-162025975493 / 1000000000000 : ℝ)
  | 14 => (-32868271291 / 200000000000 : ℝ)
  | 15 => (-33336626971 / 200000000000 : ℝ)
  | 16 => (-84525778699 / 500000000000 : ℝ)
  | 17 => (-171446872687 / 1000000000000 : ℝ)
  | 18 => (-173869331237 / 1000000000000 : ℝ)
  | 19 => (-11019949093 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch055Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1100 : ℝ) + (j.val : ℝ)) / 1600)
      (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch055Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch055Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1100 : ℝ) + (j.val : ℝ)) / 1600)
    (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch055Neg100WeightLower j.val) (hpThetaShiftTwoBatch055Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch055Neg100WeightLower, hpThetaShiftTwoBatch055Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch055Neg100_integral_bounds :
    (-10709569029 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-10334174491 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch055Lower hpThetaJensenCellsBatch055Upper
    hpThetaShiftTwoBatch055Neg100WeightLower hpThetaShiftTwoBatch055Neg100WeightUpper hpThetaJensenCellsBatch055_bounds hpThetaShiftTwoBatch055Neg100_weight_bounds
  have hl : (-10709569029 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch055Lower j * hpThetaShiftTwoBatch055Neg100WeightLower j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftTwoBatch055Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftTwoBatch055Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch055Lower j * hpThetaShiftTwoBatch055Neg100WeightUpper j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftTwoBatch055Neg100WeightUpper j) / 1600) ≤ (-10334174491 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftTwoBatch055Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1100 : ℝ) / 1600 = 55 / 80 by norm_num,
    show ((1100 : ℝ) + 20) / 1600 = (55 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch055Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (9264855759 / 1000000000000 : ℝ)
  | 1 => (9183668227 / 1000000000000 : ℝ)
  | 2 => (9099830759 / 1000000000000 : ℝ)
  | 3 => (9013306511 / 1000000000000 : ℝ)
  | 4 => (8924058287 / 1000000000000 : ℝ)
  | 5 => (8832048531 / 1000000000000 : ℝ)
  | 6 => (273038729 / 31250000000 : ℝ)
  | 7 => (8639592399 / 1000000000000 : ℝ)
  | 8 => (4269534551 / 500000000000 : ℝ)
  | 9 => (337425217 / 40000000000 : ℝ)
  | 10 => (1665847397 / 200000000000 : ℝ)
  | 11 => (8219849029 / 1000000000000 : ℝ)
  | 12 => (1013428303 / 125000000000 : ℝ)
  | 13 => (3995964331 / 500000000000 : ℝ)
  | 14 => (157466297 / 20000000000 : ℝ)
  | 15 => (7751543713 / 1000000000000 : ℝ)
  | 16 => (762657359 / 100000000000 : ℝ)
  | 17 => (1874590607 / 250000000000 : ℝ)
  | 18 => (1473373557 / 200000000000 : ℝ)
  | 19 => (361602341 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch055Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1868685969 / 200000000000 : ℝ)
  | 1 => (115810697 / 12500000000 : ℝ)
  | 2 => (2295917057 / 250000000000 : ℝ)
  | 3 => (227495769 / 25000000000 : ℝ)
  | 4 => (563331657 / 62500000000 : ℝ)
  | 5 => (557753643 / 62500000000 : ℝ)
  | 6 => (2208012133 / 250000000000 : ℝ)
  | 7 => (8737239329 / 1000000000000 : ℝ)
  | 8 => (21598981 / 2500000000 : ℝ)
  | 9 => (8539069103 / 1000000000000 : ℝ)
  | 10 => (4217815213 / 500000000000 : ℝ)
  | 11 => (4164618493 / 500000000000 : ℝ)
  | 12 => (821984903 / 100000000000 : ℝ)
  | 13 => (324297057 / 40000000000 : ℝ)
  | 14 => (7991928663 / 1000000000000 : ℝ)
  | 15 => (7873314851 / 1000000000000 : ℝ)
  | 16 => (3875771857 / 500000000000 : ℝ)
  | 17 => (7626573591 / 1000000000000 : ℝ)
  | 18 => (7498362429 / 1000000000000 : ℝ)
  | 19 => (3683433893 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch055Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1100 : ℝ) + (j.val : ℝ)) / 1600)
      (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch055Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch055Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1100 : ℝ) + (j.val : ℝ)) / 1600)
    (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch055Neg65WeightLower j.val) (hpThetaShiftTwoBatch055Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch055Neg65WeightLower, hpThetaShiftTwoBatch055Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch055Neg65_integral_bounds :
    (281831549 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (29149157 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch055Lower hpThetaJensenCellsBatch055Upper
    hpThetaShiftTwoBatch055Neg65WeightLower hpThetaShiftTwoBatch055Neg65WeightUpper hpThetaJensenCellsBatch055_bounds hpThetaShiftTwoBatch055Neg65_weight_bounds
  have hl : (281831549 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch055Lower j * hpThetaShiftTwoBatch055Neg65WeightLower j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftTwoBatch055Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftTwoBatch055Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch055Lower j * hpThetaShiftTwoBatch055Neg65WeightUpper j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftTwoBatch055Neg65WeightUpper j) / 1600) ≤ (29149157 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftTwoBatch055Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1100 : ℝ) / 1600 = 55 / 80 by norm_num,
    show ((1100 : ℝ) + 20) / 1600 = (55 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch055Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (575902311 / 62500000000 : ℝ)
  | 1 => (9300643983 / 1000000000000 : ℝ)
  | 2 => (4693576133 / 500000000000 : ℝ)
  | 3 => (9473958457 / 1000000000000 : ℝ)
  | 4 => (119513239 / 12500000000 : ℝ)
  | 5 => (2412112687 / 250000000000 : ℝ)
  | 6 => (1217016221 / 125000000000 : ℝ)
  | 7 => (1964818507 / 200000000000 : ℝ)
  | 8 => (1239041917 / 125000000000 : ℝ)
  | 9 => (625053399 / 62500000000 : ℝ)
  | 10 => (10089645823 / 1000000000000 : ℝ)
  | 11 => (5089352861 / 500000000000 : ℝ)
  | 12 => (10268030079 / 1000000000000 : ℝ)
  | 13 => (5178807409 / 500000000000 : ℝ)
  | 14 => (10447455787 / 1000000000000 : ℝ)
  | 15 => (10537548761 / 1000000000000 : ℝ)
  | 16 => (5313944719 / 500000000000 : ℝ)
  | 17 => (10718473439 / 1000000000000 : ℝ)
  | 18 => (10809296309 / 1000000000000 : ℝ)
  | 19 => (5450176757 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch055Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (581290249 / 62500000000 : ℝ)
  | 1 => (9387152267 / 1000000000000 : ℝ)
  | 2 => (4736979229 / 500000000000 : ℝ)
  | 3 => (9561059121 / 1000000000000 : ℝ)
  | 4 => (9648450749 / 1000000000000 : ℝ)
  | 5 => (9736129769 / 1000000000000 : ℝ)
  | 6 => (1228011567 / 125000000000 : ℝ)
  | 7 => (9912335337 / 1000000000000 : ℝ)
  | 8 => (2000170877 / 200000000000 : ℝ)
  | 9 => (39412679 / 3906250000 : ℝ)
  | 10 => (10178705723 / 1000000000000 : ℝ)
  | 11 => (16043797 / 1562500000 : ℝ)
  | 12 => (10357614819 / 1000000000000 : ℝ)
  | 13 => (2611863947 / 250000000000 : ℝ)
  | 14 => (5268774381 / 500000000000 : ℝ)
  | 15 => (10627889439 / 1000000000000 : ℝ)
  | 16 => (66990459 / 6250000000 : ℝ)
  | 17 => (1080929631 / 100000000000 : ℝ)
  | 18 => (2180070703 / 200000000000 : ℝ)
  | 19 => (10991640443 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch055Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1100 : ℝ) + (j.val : ℝ)) / 1600)
      (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch055Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch055Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1100 : ℝ) + (j.val : ℝ)) / 1600)
    (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch055Neg45WeightLower j.val) (hpThetaShiftTwoBatch055Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch055Neg45WeightLower, hpThetaShiftTwoBatch055Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch055Neg45_integral_bounds :
    (673568503 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (27767881 / 40000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch055Lower hpThetaJensenCellsBatch055Upper
    hpThetaShiftTwoBatch055Neg45WeightLower hpThetaShiftTwoBatch055Neg45WeightUpper hpThetaJensenCellsBatch055_bounds hpThetaShiftTwoBatch055Neg45_weight_bounds
  have hl : (673568503 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch055Lower j * hpThetaShiftTwoBatch055Neg45WeightLower j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftTwoBatch055Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftTwoBatch055Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch055Lower j * hpThetaShiftTwoBatch055Neg45WeightUpper j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftTwoBatch055Neg45WeightUpper j) / 1600) ≤ (27767881 / 40000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftTwoBatch055Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1100 : ℝ) / 1600 = 55 / 80 by norm_num,
    show ((1100 : ℝ) + 20) / 1600 = (55 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch055Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3865355027 / 1000000000000 : ℝ)
  | 1 => (-3863224021 / 1000000000000 : ℝ)
  | 2 => (-3860871439 / 1000000000000 : ℝ)
  | 3 => (-3858295419 / 1000000000000 : ℝ)
  | 4 => (-3855494091 / 1000000000000 : ℝ)
  | 5 => (-1926232791 / 500000000000 : ℝ)
  | 6 => (-384920801 / 100000000000 : ℝ)
  | 7 => (-60089367 / 15625000000 : ℝ)
  | 8 => (-1920999063 / 500000000000 : ℝ)
  | 9 => (-3838042023 / 1000000000000 : ℝ)
  | 10 => (-3833849277 / 1000000000000 : ℝ)
  | 11 => (-1914708989 / 500000000000 : ℝ)
  | 12 => (-3824746209 / 1000000000000 : ℝ)
  | 13 => (-76396641 / 20000000000 : ℝ)
  | 14 => (-1907336787 / 500000000000 : ℝ)
  | 15 => (-238079303 / 62500000000 : ℝ)
  | 16 => (-1901807967 / 500000000000 : ℝ)
  | 17 => (-474714111 / 125000000000 : ℝ)
  | 18 => (-5924309 / 1562500000 : ℝ)
  | 19 => (-946287149 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch055Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-193161201 / 50000000000 : ℝ)
  | 1 => (-1930435719 / 500000000000 : ℝ)
  | 2 => (-1929147709 / 500000000000 : ℝ)
  | 3 => (-385549409 / 100000000000 : ℝ)
  | 4 => (-3852465581 / 1000000000000 : ℝ)
  | 5 => (-3849208009 / 1000000000000 : ℝ)
  | 6 => (-3845719487 / 1000000000000 : ℝ)
  | 7 => (-6147197 / 1600000000 : ℝ)
  | 8 => (-1919021011 / 500000000000 : ℝ)
  | 9 => (-958462319 / 250000000000 : ℝ)
  | 10 => (-3829417977 / 1000000000000 : ℝ)
  | 11 => (-119523319 / 31250000000 : ℝ)
  | 12 => (-3819832049 / 1000000000000 : ℝ)
  | 13 => (-3814673573 / 1000000000000 : ℝ)
  | 14 => (-3809268847 / 1000000000000 : ℝ)
  | 15 => (-3803615933 / 1000000000000 : ℝ)
  | 16 => (-3797712887 / 1000000000000 : ℝ)
  | 17 => (-3791557759 / 1000000000000 : ℝ)
  | 18 => (-757029719 / 200000000000 : ℝ)
  | 19 => (-1889241717 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch055Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1100 : ℝ) + (j.val : ℝ)) / 1600)
      (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch055Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch055Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1100 : ℝ) + (j.val : ℝ)) / 1600)
    (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch055Neg25WeightLower j.val) (hpThetaShiftTwoBatch055Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch055Neg25WeightLower, hpThetaShiftTwoBatch055Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch055Neg25_integral_bounds :
    (-32935233 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-257634629 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch055Lower hpThetaJensenCellsBatch055Upper
    hpThetaShiftTwoBatch055Neg25WeightLower hpThetaShiftTwoBatch055Neg25WeightUpper hpThetaJensenCellsBatch055_bounds hpThetaShiftTwoBatch055Neg25_weight_bounds
  have hl : (-32935233 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch055Lower j * hpThetaShiftTwoBatch055Neg25WeightLower j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftTwoBatch055Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftTwoBatch055Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch055Lower j * hpThetaShiftTwoBatch055Neg25WeightUpper j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftTwoBatch055Neg25WeightUpper j) / 1600) ≤ (-257634629 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftTwoBatch055Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1100 : ℝ) / 1600 = 55 / 80 by norm_num,
    show ((1100 : ℝ) + 20) / 1600 = (55 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch055Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch055Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch055Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch055Neg25_integral_bounds
end HodgeProofHP
