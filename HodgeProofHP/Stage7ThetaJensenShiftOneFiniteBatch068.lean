/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch068

/-! Exact signed weight and batch integral certificates, batch 68 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch068Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-81175980513943 / 1000000000000 : ℝ)
  | 1 => (-40878587842603 / 500000000000 : ℝ)
  | 2 => (-20585467837263 / 250000000000 : ℝ)
  | 3 => (-41465042486287 / 500000000000 : ℝ)
  | 4 => (-20880458523337 / 250000000000 : ℝ)
  | 5 => (-84117136319653 / 1000000000000 : ℝ)
  | 6 => (-84716009330697 / 1000000000000 : ℝ)
  | 7 => (-42659235438417 / 500000000000 : ℝ)
  | 8 => (-85924538779791 / 1000000000000 : ℝ)
  | 9 => (-86534230932889 / 1000000000000 : ℝ)
  | 10 => (-8714756530127 / 100000000000 : ℝ)
  | 11 => (-43882279961059 / 500000000000 : ℝ)
  | 12 => (-88385232904887 / 1000000000000 : ℝ)
  | 13 => (-89009602431523 / 1000000000000 : ℝ)
  | 14 => (-44818843378347 / 500000000000 : ℝ)
  | 15 => (-5641844013001 / 62500000000 : ℝ)
  | 16 => (-22726268296569 / 250000000000 : ℝ)
  | 17 => (-45772206082833 / 500000000000 : ℝ)
  | 18 => (-18437507938801 / 200000000000 : ℝ)
  | 19 => (-92834474392971 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch068Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8059826843843 / 100000000000 : ℝ)
  | 1 => (-40587990256971 / 500000000000 : ℝ)
  | 2 => (-16351435137041 / 200000000000 : ℝ)
  | 3 => (-82341871349051 / 1000000000000 : ℝ)
  | 4 => (-82930084972573 / 1000000000000 : ℝ)
  | 5 => (-83521834093347 / 1000000000000 : ℝ)
  | 6 => (-21029284079913 / 250000000000 : ℝ)
  | 7 => (-10589501166337 / 125000000000 : ℝ)
  | 8 => (-85318470876833 / 1000000000000 : ℝ)
  | 9 => (-8592453877979 / 100000000000 : ℝ)
  | 10 => (-10816778866611 / 125000000000 : ℝ)
  | 11 => (-87147565301269 / 1000000000000 : ℝ)
  | 12 => (-87764559922117 / 1000000000000 : ℝ)
  | 13 => (-44192616452443 / 500000000000 : ℝ)
  | 14 => (-44504801215761 / 500000000000 : ℝ)
  | 15 => (-89637686756693 / 1000000000000 : ℝ)
  | 16 => (-18053900841603 / 200000000000 : ℝ)
  | 17 => (-3636202927451 / 40000000000 : ℝ)
  | 18 => (-18308882433133 / 200000000000 : ℝ)
  | 19 => (-23046884923501 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch068Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1360 : ℝ) + (j.val : ℝ)) / 1600)
      (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch068Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch068Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1360 : ℝ) + (j.val : ℝ)) / 1600)
    (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch068Neg100WeightLower j.val) (hpThetaShiftOneBatch068Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch068Neg100WeightLower, hpThetaShiftOneBatch068Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch068Neg100_integral_bounds :
    (-25704780349 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-49671434627 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch068Lower hpThetaJensenCellsBatch068Upper
    hpThetaShiftOneBatch068Neg100WeightLower hpThetaShiftOneBatch068Neg100WeightUpper hpThetaJensenCellsBatch068_bounds hpThetaShiftOneBatch068Neg100_weight_bounds
  have hl : (-25704780349 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch068Lower j * hpThetaShiftOneBatch068Neg100WeightLower j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftOneBatch068Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftOneBatch068Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch068Lower j * hpThetaShiftOneBatch068Neg100WeightUpper j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftOneBatch068Neg100WeightUpper j) / 1600) ≤ (-49671434627 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftOneBatch068Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1360 : ℝ) / 1600 = 68 / 80 by norm_num,
    show ((1360 : ℝ) + 20) / 1600 = (68 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch068Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-12939281226431 / 1000000000000 : ℝ)
  | 1 => (-815694358279 / 62500000000 : ℝ)
  | 2 => (-13163703672889 / 1000000000000 : ℝ)
  | 3 => (-2655413444523 / 200000000000 : ℝ)
  | 4 => (-1339120457447 / 100000000000 : ℝ)
  | 5 => (-13506119939257 / 1000000000000 : ℝ)
  | 6 => (-3405454386453 / 250000000000 : ℝ)
  | 7 => (-6869150820533 / 500000000000 : ℝ)
  | 8 => (-1731947061263 / 125000000000 : ℝ)
  | 9 => (-6986823188109 / 500000000000 : ℝ)
  | 10 => (-880782225061 / 62500000000 : ℝ)
  | 11 => (-7106094242137 / 500000000000 : ℝ)
  | 12 => (-14332669364397 / 1000000000000 : ℝ)
  | 13 => (-7226981299041 / 500000000000 : ℝ)
  | 14 => (-583042902423 / 40000000000 : ℝ)
  | 15 => (-14699003645693 / 1000000000000 : ℝ)
  | 16 => (-370569006647 / 25000000000 : ℝ)
  | 17 => (-14947346852273 / 1000000000000 : ℝ)
  | 18 => (-7536383927379 / 500000000000 : ℝ)
  | 19 => (-3799756935509 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch068Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2565642799547 / 200000000000 : ℝ)
  | 1 => (-1293928122643 / 100000000000 : ℝ)
  | 2 => (-13051109732463 / 1000000000000 : ℝ)
  | 3 => (-1645462959111 / 125000000000 : ℝ)
  | 4 => (-6638533611307 / 500000000000 : ℝ)
  | 5 => (-13391204574469 / 1000000000000 : ℝ)
  | 6 => (-1688264992407 / 125000000000 : ℝ)
  | 7 => (-13621817545811 / 1000000000000 : ℝ)
  | 8 => (-2747660328213 / 200000000000 : ℝ)
  | 9 => (-13855576490103 / 1000000000000 : ℝ)
  | 10 => (-13973646376217 / 1000000000000 : ℝ)
  | 11 => (-563700624039 / 40000000000 : ℝ)
  | 12 => (-14212188484273 / 1000000000000 : ℝ)
  | 13 => (-3583167341099 / 250000000000 : ℝ)
  | 14 => (-14453962598081 / 1000000000000 : ℝ)
  | 15 => (-7288036280287 / 500000000000 : ℝ)
  | 16 => (-3674750911423 / 250000000000 : ℝ)
  | 17 => (-14822760265879 / 1000000000000 : ℝ)
  | 18 => (-934209178267 / 62500000000 : ℝ)
  | 19 => (-15072767854757 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch068Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1360 : ℝ) + (j.val : ℝ)) / 1600)
      (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch068Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch068Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1360 : ℝ) + (j.val : ℝ)) / 1600)
    (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch068Neg65WeightLower j.val) (hpThetaShiftOneBatch068Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch068Neg65WeightLower, hpThetaShiftOneBatch068Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch068Neg65_integral_bounds :
    (-1037786667 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-16020503709 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch068Lower hpThetaJensenCellsBatch068Upper
    hpThetaShiftOneBatch068Neg65WeightLower hpThetaShiftOneBatch068Neg65WeightUpper hpThetaJensenCellsBatch068_bounds hpThetaShiftOneBatch068Neg65_weight_bounds
  have hl : (-1037786667 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch068Lower j * hpThetaShiftOneBatch068Neg65WeightLower j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftOneBatch068Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftOneBatch068Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch068Lower j * hpThetaShiftOneBatch068Neg65WeightUpper j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftOneBatch068Neg65WeightUpper j) / 1600) ≤ (-16020503709 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftOneBatch068Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1360 : ℝ) / 1600 = 68 / 80 by norm_num,
    show ((1360 : ℝ) + 20) / 1600 = (68 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch068Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-40700836003 / 250000000000 : ℝ)
  | 1 => (-172287179137 / 1000000000000 : ℝ)
  | 2 => (-181875532479 / 1000000000000 : ℝ)
  | 3 => (-191569129651 / 1000000000000 : ℝ)
  | 4 => (-201368699853 / 1000000000000 : ℝ)
  | 5 => (-105637487941 / 500000000000 : ℝ)
  | 6 => (-44257738829 / 200000000000 : ℝ)
  | 7 => (-14463162167 / 62500000000 : ℝ)
  | 8 => (-60410355283 / 250000000000 : ℝ)
  | 9 => (-6299548021 / 25000000000 : ℝ)
  | 10 => (-131216422387 / 500000000000 : ℝ)
  | 11 => (-68248736897 / 250000000000 : ℝ)
  | 12 => (-283668987621 / 1000000000000 : ℝ)
  | 13 => (-147227863459 / 500000000000 : ℝ)
  | 14 => (-305355931233 / 1000000000000 : ℝ)
  | 15 => (-316370370049 / 1000000000000 : ℝ)
  | 16 => (-20468738537 / 62500000000 : ℝ)
  | 17 => (-84686261959 / 250000000000 : ℝ)
  | 18 => (-350106844527 / 1000000000000 : ℝ)
  | 19 => (-180792995593 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch068Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-153423305059 / 1000000000000 : ℝ)
  | 1 => (-162803344011 / 1000000000000 : ℝ)
  | 2 => (-1345993587 / 7812500000 : ℝ)
  | 3 => (-90937766239 / 500000000000 : ℝ)
  | 4 => (-3831382593 / 20000000000 : ℝ)
  | 5 => (-50342174963 / 250000000000 : ℝ)
  | 6 => (-211274975881 / 1000000000000 : ℝ)
  | 7 => (-1728817923 / 7812500000 : ℝ)
  | 8 => (-231410594671 / 1000000000000 : ℝ)
  | 9 => (-241641421131 / 1000000000000 : ℝ)
  | 10 => (-251981920839 / 1000000000000 : ℝ)
  | 11 => (-262432844773 / 1000000000000 : ℝ)
  | 12 => (-272994947587 / 1000000000000 : ℝ)
  | 13 => (-14183449381 / 50000000000 : ℝ)
  | 14 => (-294455726917 / 1000000000000 : ℝ)
  | 15 => (-9542372851 / 31250000000 : ℝ)
  | 16 => (-617910879 / 1953125000 : ℝ)
  | 17 => (-327499816591 / 1000000000000 : ℝ)
  | 18 => (-67749009567 / 200000000000 : ℝ)
  | 19 => (-175053422263 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch068Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1360 : ℝ) + (j.val : ℝ)) / 1600)
      (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch068Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch068Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1360 : ℝ) + (j.val : ℝ)) / 1600)
    (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch068Neg40WeightLower j.val) (hpThetaShiftOneBatch068Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch068Neg40WeightLower, hpThetaShiftOneBatch068Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch068Neg40_integral_bounds :
    (-15004587 / 50000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-140019057 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch068Lower hpThetaJensenCellsBatch068Upper
    hpThetaShiftOneBatch068Neg40WeightLower hpThetaShiftOneBatch068Neg40WeightUpper hpThetaJensenCellsBatch068_bounds hpThetaShiftOneBatch068Neg40_weight_bounds
  have hl : (-15004587 / 50000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch068Lower j * hpThetaShiftOneBatch068Neg40WeightLower j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftOneBatch068Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftOneBatch068Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch068Lower j * hpThetaShiftOneBatch068Neg40WeightUpper j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftOneBatch068Neg40WeightUpper j) / 1600) ≤ (-140019057 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftOneBatch068Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1360 : ℝ) / 1600 = 68 / 80 by norm_num,
    show ((1360 : ℝ) + 20) / 1600 = (68 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch068Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (56284994373 / 250000000000 : ℝ)
  | 1 => (56750873737 / 250000000000 : ℝ)
  | 2 => (228872337179 / 1000000000000 : ℝ)
  | 3 => (230746485489 / 1000000000000 : ℝ)
  | 4 => (116312960461 / 500000000000 : ℝ)
  | 5 => (11725531213 / 50000000000 : ℝ)
  | 6 => (11820028801 / 50000000000 : ℝ)
  | 7 => (47659151291 / 200000000000 : ℝ)
  | 8 => (4803922911 / 20000000000 : ℝ)
  | 9 => (15131357689 / 62500000000 : ℝ)
  | 10 => (9760498733 / 40000000000 : ℝ)
  | 11 => (245928360633 / 1000000000000 : ℝ)
  | 12 => (123924689427 / 500000000000 : ℝ)
  | 13 => (124887750811 / 500000000000 : ℝ)
  | 14 => (251706707297 / 1000000000000 : ℝ)
  | 15 => (126821486981 / 500000000000 : ℝ)
  | 16 => (255584279423 / 1000000000000 : ℝ)
  | 17 => (25753060121 / 100000000000 : ℝ)
  | 18 => (259481916571 / 1000000000000 : ℝ)
  | 19 => (32679775309 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch068Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (227003494949 / 1000000000000 : ℝ)
  | 1 => (11443616859 / 50000000000 : ℝ)
  | 2 => (23074648549 / 100000000000 : ℝ)
  | 3 => (232625920923 / 1000000000000 : ℝ)
  | 4 => (234510624261 / 1000000000000 : ℝ)
  | 5 => (236400576021 / 1000000000000 : ℝ)
  | 6 => (29786969557 / 125000000000 : ℝ)
  | 7 => (240196145551 / 1000000000000 : ℝ)
  | 8 => (9684068921 / 40000000000 : ℝ)
  | 9 => (122006234163 / 500000000000 : ℝ)
  | 10 => (122964180317 / 500000000000 : ℝ)
  | 11 => (49569875771 / 200000000000 : ℝ)
  | 12 => (249775501623 / 1000000000000 : ℝ)
  | 13 => (125853353649 / 500000000000 : ℝ)
  | 14 => (253642973963 / 1000000000000 : ℝ)
  | 15 => (1996752183 / 7812500000 : ℝ)
  | 16 => (257530601211 / 1000000000000 : ℝ)
  | 17 => (64870479143 / 250000000000 : ℝ)
  | 18 => (261438202473 / 1000000000000 : ℝ)
  | 19 => (658498589 / 2500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch068Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1360 : ℝ) + (j.val : ℝ)) / 1600)
      (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch068Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch068Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1360 : ℝ) + (j.val : ℝ)) / 1600)
    (((1360 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch068Neg20WeightLower j.val) (hpThetaShiftOneBatch068Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch068Neg20WeightLower, hpThetaShiftOneBatch068Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch068Neg20_integral_bounds :
    (279784561 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (68 / 80 : ℝ) ((68 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (144902293 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1360 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch068Lower hpThetaJensenCellsBatch068Upper
    hpThetaShiftOneBatch068Neg20WeightLower hpThetaShiftOneBatch068Neg20WeightUpper hpThetaJensenCellsBatch068_bounds hpThetaShiftOneBatch068Neg20_weight_bounds
  have hl : (279784561 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch068Lower j * hpThetaShiftOneBatch068Neg20WeightLower j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftOneBatch068Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftOneBatch068Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch068Lower j * hpThetaShiftOneBatch068Neg20WeightUpper j)
        (hpThetaJensenCellsBatch068Upper j * hpThetaShiftOneBatch068Neg20WeightUpper j) / 1600) ≤ (144902293 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch068Lower, hpThetaJensenCellsBatch068Upper,
      hpThetaShiftOneBatch068Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1360 : ℝ) / 1600 = 68 / 80 by norm_num,
    show ((1360 : ℝ) + 20) / 1600 = (68 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch068Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch068Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch068Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch068Neg20_integral_bounds
end HodgeProofHP
