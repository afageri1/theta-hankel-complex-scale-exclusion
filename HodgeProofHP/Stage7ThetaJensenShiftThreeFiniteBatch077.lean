/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch077

/-! Exact signed weight and batch integral certificates, batch 77 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch077Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-200912566823 / 500000000000 : ℝ)
  | 1 => (-81107292561 / 200000000000 : ℝ)
  | 2 => (-10231961427 / 25000000000 : ℝ)
  | 3 => (-413051341941 / 1000000000000 : ℝ)
  | 4 => (-208427672161 / 500000000000 : ℝ)
  | 5 => (-420690692629 / 1000000000000 : ℝ)
  | 6 => (-1698230467 / 4000000000 : ℝ)
  | 7 => (-21422817403 / 50000000000 : ℝ)
  | 8 => (-432387119433 / 1000000000000 : ℝ)
  | 9 => (-1704492833 / 3906250000 : ℝ)
  | 10 => (-220172860699 / 500000000000 : ℝ)
  | 11 => (-444374025299 / 1000000000000 : ℝ)
  | 12 => (-4484353159 / 10000000000 : ℝ)
  | 13 => (-452529833689 / 1000000000000 : ℝ)
  | 14 => (-456657820701 / 1000000000000 : ℝ)
  | 15 => (-460819520533 / 1000000000000 : ℝ)
  | 16 => (-465015178343 / 1000000000000 : ℝ)
  | 17 => (-117311260217 / 250000000000 : ℝ)
  | 18 => (-118377339107 / 250000000000 : ℝ)
  | 19 => (-238904187467 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch077Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-398144245587 / 1000000000000 : ℝ)
  | 1 => (-80365026729 / 200000000000 : ℝ)
  | 2 => (-101384115701 / 250000000000 : ℝ)
  | 3 => (-409278457079 / 1000000000000 : ℝ)
  | 4 => (-20652567097 / 50000000000 : ℝ)
  | 5 => (-416855344321 / 1000000000000 : ℝ)
  | 6 => (-105172673157 / 250000000000 : ℝ)
  | 7 => (-424557616749 / 1000000000000 : ℝ)
  | 8 => (-428456348059 / 1000000000000 : ℝ)
  | 9 => (-54048389929 / 125000000000 : ℝ)
  | 10 => (-436350165247 / 1000000000000 : ℝ)
  | 11 => (-440345721397 / 1000000000000 : ℝ)
  | 12 => (-222187012649 / 500000000000 : ℝ)
  | 13 => (-448435315899 / 1000000000000 : ℝ)
  | 14 => (-56566229211 / 125000000000 : ℝ)
  | 15 => (-4566578207 / 10000000000 : ℝ)
  | 16 => (-115204880133 / 250000000000 : ℝ)
  | 17 => (-232507589171 / 500000000000 : ℝ)
  | 18 => (-469245040867 / 1000000000000 : ℝ)
  | 19 => (-473509356427 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch077Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1540 : ℝ) + (j.val : ℝ)) / 1600)
      (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch077Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch077Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1540 : ℝ) + (j.val : ℝ)) / 1600)
    (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch077Neg100WeightLower j.val) (hpThetaShiftThreeBatch077Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch077Neg100WeightLower, hpThetaShiftThreeBatch077Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch077Neg100_integral_bounds :
    (-10885097 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-2087561 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch077Lower hpThetaJensenCellsBatch077Upper
    hpThetaShiftThreeBatch077Neg100WeightLower hpThetaShiftThreeBatch077Neg100WeightUpper hpThetaJensenCellsBatch077_bounds hpThetaShiftThreeBatch077Neg100_weight_bounds
  have hl : (-10885097 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch077Lower j * hpThetaShiftThreeBatch077Neg100WeightLower j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftThreeBatch077Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftThreeBatch077Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch077Lower j * hpThetaShiftThreeBatch077Neg100WeightUpper j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftThreeBatch077Neg100WeightUpper j) / 1600) ≤ (-2087561 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftThreeBatch077Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1540 : ℝ) / 1600 = 77 / 80 by norm_num,
    show ((1540 : ℝ) + 20) / 1600 = (77 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch077Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-80498499657 / 1000000000000 : ℝ)
  | 1 => (-81348183269 / 1000000000000 : ℝ)
  | 2 => (-82205631371 / 1000000000000 : ℝ)
  | 3 => (-83070905671 / 1000000000000 : ℝ)
  | 4 => (-83944068299 / 1000000000000 : ℝ)
  | 5 => (-42412590909 / 500000000000 : ℝ)
  | 6 => (-85714309217 / 1000000000000 : ℝ)
  | 7 => (-86611513923 / 1000000000000 : ℝ)
  | 8 => (-43758429897 / 500000000000 : ℝ)
  | 9 => (-22107602783 / 250000000000 : ℝ)
  | 10 => (-22338058169 / 250000000000 : ℝ)
  | 11 => (-9028238961 / 100000000000 : ℝ)
  | 12 => (-22805236891 / 250000000000 : ℝ)
  | 13 => (-92167972619 / 1000000000000 : ℝ)
  | 14 => (-46561765653 / 500000000000 : ℝ)
  | 15 => (-9408769061 / 100000000000 : ℝ)
  | 16 => (-47530258987 / 500000000000 : ℝ)
  | 17 => (-960420813 / 10000000000 : ℝ)
  | 18 => (-97032448953 / 1000000000000 : ℝ)
  | 19 => (-98031689763 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch077Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-19914129813 / 250000000000 : ℝ)
  | 1 => (-10062312457 / 125000000000 : ℝ)
  | 2 => (-20337045817 / 250000000000 : ℝ)
  | 3 => (-8220563137 / 100000000000 : ℝ)
  | 4 => (-8307090567 / 100000000000 : ℝ)
  | 5 => (-41972034149 / 500000000000 : ℝ)
  | 6 => (-84825181817 / 1000000000000 : ℝ)
  | 7 => (-2678572163 / 31250000000 : ℝ)
  | 8 => (-43305756961 / 500000000000 : ℝ)
  | 9 => (-87516859793 / 1000000000000 : ℝ)
  | 10 => (-88430411131 / 1000000000000 : ℝ)
  | 11 => (-3574089307 / 40000000000 : ℝ)
  | 12 => (-90282389609 / 1000000000000 : ℝ)
  | 13 => (-91220947563 / 1000000000000 : ℝ)
  | 14 => (-46083986309 / 500000000000 : ℝ)
  | 15 => (-18624706261 / 200000000000 : ℝ)
  | 16 => (-94087690609 / 1000000000000 : ℝ)
  | 17 => (-95060517973 / 1000000000000 : ℝ)
  | 18 => (-96042081299 / 1000000000000 : ℝ)
  | 19 => (-12129056119 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch077Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1540 : ℝ) + (j.val : ℝ)) / 1600)
      (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch077Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch077Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1540 : ℝ) + (j.val : ℝ)) / 1600)
    (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch077Neg70WeightLower j.val) (hpThetaShiftThreeBatch077Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch077Neg70WeightLower, hpThetaShiftThreeBatch077Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch077Neg70_integral_bounds :
    (-2205809 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-2112499 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch077Lower hpThetaJensenCellsBatch077Upper
    hpThetaShiftThreeBatch077Neg70WeightLower hpThetaShiftThreeBatch077Neg70WeightUpper hpThetaJensenCellsBatch077_bounds hpThetaShiftThreeBatch077Neg70_weight_bounds
  have hl : (-2205809 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch077Lower j * hpThetaShiftThreeBatch077Neg70WeightLower j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftThreeBatch077Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftThreeBatch077Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch077Lower j * hpThetaShiftThreeBatch077Neg70WeightUpper j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftThreeBatch077Neg70WeightUpper j) / 1600) ≤ (-2112499 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftThreeBatch077Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1540 : ℝ) / 1600 = 77 / 80 by norm_num,
    show ((1540 : ℝ) + 20) / 1600 = (77 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch077Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-426844511 / 200000000000 : ℝ)
  | 1 => (-440369169 / 200000000000 : ℝ)
  | 2 => (-90816769 / 40000000000 : ℝ)
  | 3 => (-1169976193 / 500000000000 : ℝ)
  | 4 => (-2410455099 / 1000000000000 : ℝ)
  | 5 => (-38780269 / 15625000000 : ℝ)
  | 6 => (-2554408667 / 1000000000000 : ℝ)
  | 7 => (-1313939731 / 500000000000 : ℝ)
  | 8 => (-1351179847 / 500000000000 : ℝ)
  | 9 => (-173616221 / 62500000000 : ℝ)
  | 10 => (-713597311 / 250000000000 : ℝ)
  | 11 => (-586391831 / 200000000000 : ℝ)
  | 12 => (-752644923 / 250000000000 : ℝ)
  | 13 => (-3090261359 / 1000000000000 : ℝ)
  | 14 => (-634202949 / 200000000000 : ℝ)
  | 15 => (-130114021 / 40000000000 : ℝ)
  | 16 => (-1667889729 / 500000000000 : ℝ)
  | 17 => (-341981239 / 100000000000 : ℝ)
  | 18 => (-3504960253 / 1000000000000 : ℝ)
  | 19 => (-1795617033 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch077Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1033769869 / 500000000000 : ℝ)
  | 1 => (-1067111277 / 500000000000 : ℝ)
  | 2 => (-550461461 / 250000000000 : ℝ)
  | 3 => (-283802403 / 125000000000 : ℝ)
  | 4 => (-467990477 / 200000000000 : ℝ)
  | 5 => (-1205227549 / 500000000000 : ℝ)
  | 6 => (-496387443 / 200000000000 : ℝ)
  | 7 => (-1277204333 / 500000000000 : ℝ)
  | 8 => (-2627879461 / 1000000000000 : ℝ)
  | 9 => (-2702359693 / 1000000000000 : ℝ)
  | 10 => (-555571907 / 200000000000 : ℝ)
  | 11 => (-2854389243 / 1000000000000 : ℝ)
  | 12 => (-1465979577 / 500000000000 : ℝ)
  | 13 => (-3010579691 / 1000000000000 : ℝ)
  | 14 => (-1545130679 / 500000000000 : ℝ)
  | 15 => (-396376843 / 125000000000 : ℝ)
  | 16 => (-813212631 / 250000000000 : ℝ)
  | 17 => (-3335779457 / 1000000000000 : ℝ)
  | 18 => (-3419812389 / 1000000000000 : ℝ)
  | 19 => (-876240063 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch077Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1540 : ℝ) + (j.val : ℝ)) / 1600)
      (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch077Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch077Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1540 : ℝ) + (j.val : ℝ)) / 1600)
    (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch077Neg45WeightLower j.val) (hpThetaShiftThreeBatch077Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch077Neg45WeightLower, hpThetaShiftThreeBatch077Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch077Neg45_integral_bounds :
    (-541 / 7812500000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-65187 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch077Lower hpThetaJensenCellsBatch077Upper
    hpThetaShiftThreeBatch077Neg45WeightLower hpThetaShiftThreeBatch077Neg45WeightUpper hpThetaJensenCellsBatch077_bounds hpThetaShiftThreeBatch077Neg45_weight_bounds
  have hl : (-541 / 7812500000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch077Lower j * hpThetaShiftThreeBatch077Neg45WeightLower j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftThreeBatch077Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftThreeBatch077Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch077Lower j * hpThetaShiftThreeBatch077Neg45WeightUpper j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftThreeBatch077Neg45WeightUpper j) / 1600) ≤ (-65187 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftThreeBatch077Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1540 : ℝ) / 1600 = 77 / 80 by norm_num,
    show ((1540 : ℝ) + 20) / 1600 = (77 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch077Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (602754523 / 500000000000 : ℝ)
  | 1 => (1219593767 / 1000000000000 : ℝ)
  | 2 => (61688263 / 50000000000 : ℝ)
  | 3 => (156002961 / 125000000000 : ℝ)
  | 4 => (1262369211 / 1000000000000 : ℝ)
  | 5 => (638400993 / 500000000000 : ℝ)
  | 6 => (161415271 / 125000000000 : ℝ)
  | 7 => (1305929907 / 1000000000000 : ℝ)
  | 8 => (1320625353 / 1000000000000 : ℝ)
  | 9 => (1335408649 / 1000000000000 : ℝ)
  | 10 => (1350279937 / 1000000000000 : ℝ)
  | 11 => (1365239357 / 1000000000000 : ℝ)
  | 12 => (690143521 / 500000000000 : ℝ)
  | 13 => (697711563 / 500000000000 : ℝ)
  | 14 => (1410647737 / 1000000000000 : ℝ)
  | 15 => (1425960999 / 1000000000000 : ℝ)
  | 16 => (288272607 / 200000000000 : ℝ)
  | 17 => (1456853963 / 1000000000000 : ℝ)
  | 18 => (736216949 / 500000000000 : ℝ)
  | 19 => (1488102951 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch077Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (152449221 / 125000000000 : ℝ)
  | 1 => (1233765261 / 1000000000000 : ℝ)
  | 2 => (1248023689 / 1000000000000 : ℝ)
  | 3 => (315592303 / 250000000000 : ℝ)
  | 4 => (1276801987 / 1000000000000 : ℝ)
  | 5 => (1291322169 / 1000000000000 : ℝ)
  | 6 => (326482477 / 250000000000 : ℝ)
  | 7 => (660312677 / 500000000000 : ℝ)
  | 8 => (26708173 / 20000000000 : ℝ)
  | 9 => (675139969 / 500000000000 : ℝ)
  | 10 => (682619679 / 500000000000 : ℝ)
  | 11 => (1380287043 / 1000000000000 : ℝ)
  | 12 => (1395423127 / 1000000000000 : ℝ)
  | 13 => (705323869 / 500000000000 : ℝ)
  | 14 => (1425961 / 1000000000 : ℝ)
  | 15 => (360340759 / 250000000000 : ℝ)
  | 16 => (364213491 / 250000000000 : ℝ)
  | 17 => (1472433899 / 1000000000000 : ℝ)
  | 18 => (186012869 / 125000000000 : ℝ)
  | 19 => (150386123 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch077Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1540 : ℝ) + (j.val : ℝ)) / 1600)
      (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch077Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch077Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1540 : ℝ) + (j.val : ℝ)) / 1600)
    (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch077Neg25WeightLower j.val) (hpThetaShiftThreeBatch077Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch077Neg25WeightLower, hpThetaShiftThreeBatch077Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch077Neg25_integral_bounds :
    (8053 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (33659 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch077Lower hpThetaJensenCellsBatch077Upper
    hpThetaShiftThreeBatch077Neg25WeightLower hpThetaShiftThreeBatch077Neg25WeightUpper hpThetaJensenCellsBatch077_bounds hpThetaShiftThreeBatch077Neg25_weight_bounds
  have hl : (8053 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch077Lower j * hpThetaShiftThreeBatch077Neg25WeightLower j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftThreeBatch077Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftThreeBatch077Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch077Lower j * hpThetaShiftThreeBatch077Neg25WeightUpper j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftThreeBatch077Neg25WeightUpper j) / 1600) ≤ (33659 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftThreeBatch077Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1540 : ℝ) / 1600 = 77 / 80 by norm_num,
    show ((1540 : ℝ) + 20) / 1600 = (77 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch077Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch077Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch077Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch077Neg25_integral_bounds
end HodgeProofHP
