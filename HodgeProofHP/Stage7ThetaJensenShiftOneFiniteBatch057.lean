/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch057

/-! Exact signed weight and batch integral certificates, batch 57 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch057Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-13143254981599 / 1000000000000 : ℝ)
  | 1 => (-106177764409 / 8000000000 : ℝ)
  | 2 => (-2680441325971 / 200000000000 : ℝ)
  | 3 => (-13533219720383 / 1000000000000 : ℝ)
  | 4 => (-21864426173 / 1600000000 : ℝ)
  | 5 => (-13798353111447 / 1000000000000 : ℝ)
  | 6 => (-13932486581793 / 1000000000000 : ℝ)
  | 7 => (-3516918350953 / 250000000000 : ℝ)
  | 8 => (-7101960122743 / 500000000000 : ℝ)
  | 9 => (-7170616904129 / 500000000000 : ℝ)
  | 10 => (-14479620827161 / 1000000000000 : ℝ)
  | 11 => (-14619088070949 / 1000000000000 : ℝ)
  | 12 => (-922477646389 / 62500000000 : ℝ)
  | 13 => (-7450645238783 / 500000000000 : ℝ)
  | 14 => (-940252459229 / 62500000000 : ℝ)
  | 15 => (-1898486982181 / 125000000000 : ℝ)
  | 16 => (-7666433473109 / 500000000000 : ℝ)
  | 17 => (-7739479793887 / 500000000000 : ℝ)
  | 18 => (-312523615811 / 20000000000 : ℝ)
  | 19 => (-3943634399437 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch057Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-13015303451379 / 1000000000000 : ℝ)
  | 1 => (-6571627490799 / 500000000000 : ℝ)
  | 2 => (-3318055137781 / 250000000000 : ℝ)
  | 3 => (-6701103314927 / 500000000000 : ℝ)
  | 4 => (-6766609860191 / 500000000000 : ℝ)
  | 5 => (-3416316589531 / 250000000000 : ℝ)
  | 6 => (-6899176555723 / 500000000000 : ℝ)
  | 7 => (-435390205681 / 31250000000 : ℝ)
  | 8 => (-14067673403811 / 1000000000000 : ℝ)
  | 9 => (-2840784049097 / 200000000000 : ℝ)
  | 10 => (-14341233808257 / 1000000000000 : ℝ)
  | 11 => (-361990520679 / 25000000000 : ℝ)
  | 12 => (-3654772017737 / 250000000000 : ℝ)
  | 13 => (-14759642342223 / 1000000000000 : ℝ)
  | 14 => (-2980258095513 / 200000000000 : ℝ)
  | 15 => (-15044039347663 / 1000000000000 : ℝ)
  | 16 => (-15187895857447 / 1000000000000 : ℝ)
  | 17 => (-15332866946217 / 1000000000000 : ℝ)
  | 18 => (-15478959587773 / 1000000000000 : ℝ)
  | 19 => (-15626180790549 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch057Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1140 : ℝ) + (j.val : ℝ)) / 1600)
      (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch057Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch057Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1140 : ℝ) + (j.val : ℝ)) / 1600)
    (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch057Neg100WeightLower j.val) (hpThetaShiftOneBatch057Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch057Neg100WeightLower, hpThetaShiftOneBatch057Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch057Neg100_integral_bounds :
    (-291952364587 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-7070682123 / 12500000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch057Lower hpThetaJensenCellsBatch057Upper
    hpThetaShiftOneBatch057Neg100WeightLower hpThetaShiftOneBatch057Neg100WeightUpper hpThetaJensenCellsBatch057_bounds hpThetaShiftOneBatch057Neg100_weight_bounds
  have hl : (-291952364587 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch057Lower j * hpThetaShiftOneBatch057Neg100WeightLower j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftOneBatch057Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftOneBatch057Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch057Lower j * hpThetaShiftOneBatch057Neg100WeightUpper j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftOneBatch057Neg100WeightUpper j) / 1600) ≤ (-7070682123 / 12500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftOneBatch057Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1140 : ℝ) / 1600 = 57 / 80 by norm_num,
    show ((1140 : ℝ) + 20) / 1600 = (57 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch057Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-197971688573 / 200000000000 : ℝ)
  | 1 => (-201569541569 / 200000000000 : ℝ)
  | 2 => (-128253365229 / 125000000000 : ℝ)
  | 3 => (-261099378883 / 250000000000 : ℝ)
  | 4 => (-1062960927659 / 1000000000000 : ℝ)
  | 5 => (-43268744199 / 40000000000 : ℝ)
  | 6 => (-1100672002319 / 1000000000000 : ℝ)
  | 7 => (-559911291321 / 500000000000 : ℝ)
  | 8 => (-14239647713 / 12500000000 : ℝ)
  | 9 => (-231744236957 / 200000000000 : ℝ)
  | 10 => (-235694434673 / 200000000000 : ℝ)
  | 11 => (-1198426278509 / 1000000000000 : ℝ)
  | 12 => (-304646251057 / 250000000000 : ℝ)
  | 13 => (-619474931423 / 500000000000 : ℝ)
  | 14 => (-1259522375033 / 1000000000000 : ℝ)
  | 15 => (-1280304069841 / 1000000000000 : ℝ)
  | 16 => (-260259296947 / 200000000000 : ℝ)
  | 17 => (-1322501165631 / 1000000000000 : ℝ)
  | 18 => (-1343919666929 / 1000000000000 : ℝ)
  | 19 => (-1365553551547 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch057Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-121507213021 / 125000000000 : ℝ)
  | 1 => (-61866152679 / 62500000000 : ℝ)
  | 2 => (-251961926961 / 250000000000 : ℝ)
  | 3 => (-1026026921831 / 1000000000000 : ℝ)
  | 4 => (-1044397515531 / 1000000000000 : ℝ)
  | 5 => (-531480463829 / 500000000000 : ℝ)
  | 6 => (-540859302487 / 500000000000 : ℝ)
  | 7 => (-550336001159 / 500000000000 : ℝ)
  | 8 => (-1119822582641 / 1000000000000 : ℝ)
  | 9 => (-1139171817039 / 1000000000000 : ℝ)
  | 10 => (-72420074049 / 62500000000 : ℝ)
  | 11 => (-294618043341 / 250000000000 : ℝ)
  | 12 => (-299606569627 / 250000000000 : ℝ)
  | 13 => (-1218585004227 / 1000000000000 : ℝ)
  | 14 => (-247789972569 / 200000000000 : ℝ)
  | 15 => (-157440296879 / 125000000000 : ℝ)
  | 16 => (-16003800873 / 12500000000 : ℝ)
  | 17 => (-650648242367 / 500000000000 : ℝ)
  | 18 => (-132250116563 / 100000000000 : ℝ)
  | 19 => (-83994979183 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch057Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1140 : ℝ) + (j.val : ℝ)) / 1600)
      (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch057Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch057Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1140 : ℝ) + (j.val : ℝ)) / 1600)
    (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch057Neg65WeightLower j.val) (hpThetaShiftOneBatch057Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch057Neg65WeightLower, hpThetaShiftOneBatch057Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch057Neg65_integral_bounds :
    (-47272280707 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-11364612663 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch057Lower hpThetaJensenCellsBatch057Upper
    hpThetaShiftOneBatch057Neg65WeightLower hpThetaShiftOneBatch057Neg65WeightUpper hpThetaJensenCellsBatch057_bounds hpThetaShiftOneBatch057Neg65_weight_bounds
  have hl : (-47272280707 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch057Lower j * hpThetaShiftOneBatch057Neg65WeightLower j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftOneBatch057Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftOneBatch057Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch057Lower j * hpThetaShiftOneBatch057Neg65WeightUpper j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftOneBatch057Neg65WeightUpper j) / 1600) ≤ (-11364612663 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftOneBatch057Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1140 : ℝ) / 1600 = 57 / 80 by norm_num,
    show ((1140 : ℝ) + 20) / 1600 = (57 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch057Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (379732336527 / 1000000000000 : ℝ)
  | 1 => (190458438213 / 500000000000 : ℝ)
  | 2 => (95522399101 / 250000000000 : ℝ)
  | 3 => (95812575651 / 250000000000 : ℝ)
  | 4 => (384398799713 / 1000000000000 : ℝ)
  | 5 => (77106978193 / 200000000000 : ℝ)
  | 6 => (386658378123 / 1000000000000 : ℝ)
  | 7 => (9694226537 / 25000000000 : ℝ)
  | 8 => (388866739851 / 1000000000000 : ℝ)
  | 9 => (194975605281 / 500000000000 : ℝ)
  | 10 => (195511134723 / 500000000000 : ℝ)
  | 11 => (78415942167 / 200000000000 : ℝ)
  | 12 => (78624665511 / 200000000000 : ℝ)
  | 13 => (78830582183 / 200000000000 : ℝ)
  | 14 => (395168250703 / 1000000000000 : ℝ)
  | 15 => (198084567589 / 500000000000 : ℝ)
  | 16 => (397155351063 / 1000000000000 : ℝ)
  | 17 => (398126683537 / 1000000000000 : ℝ)
  | 18 => (399082916227 / 1000000000000 : ℝ)
  | 19 => (200011915603 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch057Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (380916876427 / 1000000000000 : ℝ)
  | 1 => (76417919281 / 200000000000 : ℝ)
  | 2 => (76650060521 / 200000000000 : ℝ)
  | 3 => (192199399857 / 500000000000 : ℝ)
  | 4 => (192767445483 / 500000000000 : ℝ)
  | 5 => (96664594531 / 250000000000 : ℝ)
  | 6 => (387769061481 / 1000000000000 : ℝ)
  | 7 => (97216684963 / 250000000000 : ℝ)
  | 8 => (389951210563 / 1000000000000 : ℝ)
  | 9 => (391022269447 / 1000000000000 : ℝ)
  | 10 => (98019927709 / 250000000000 : ℝ)
  | 11 => (98280831889 / 250000000000 : ℝ)
  | 12 => (98538227729 / 250000000000 : ℝ)
  | 13 => (24698015669 / 62500000000 : ℝ)
  | 14 => (396169135179 / 1000000000000 : ℝ)
  | 15 => (49644418883 / 125000000000 : ℝ)
  | 16 => (199063341769 / 500000000000 : ℝ)
  | 17 => (99770729057 / 250000000000 : ℝ)
  | 18 => (400023831207 / 1000000000000 : ℝ)
  | 19 => (400949208979 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch057Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1140 : ℝ) + (j.val : ℝ)) / 1600)
      (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch057Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch057Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1140 : ℝ) + (j.val : ℝ)) / 1600)
    (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch057Neg40WeightLower j.val) (hpThetaShiftOneBatch057Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch057Neg40WeightLower, hpThetaShiftOneBatch057Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch057Neg40_integral_bounds :
    (1549591367 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (7943043389 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch057Lower hpThetaJensenCellsBatch057Upper
    hpThetaShiftOneBatch057Neg40WeightLower hpThetaShiftOneBatch057Neg40WeightUpper hpThetaJensenCellsBatch057_bounds hpThetaShiftOneBatch057Neg40_weight_bounds
  have hl : (1549591367 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch057Lower j * hpThetaShiftOneBatch057Neg40WeightLower j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftOneBatch057Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftOneBatch057Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch057Lower j * hpThetaShiftOneBatch057Neg40WeightUpper j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftOneBatch057Neg40WeightUpper j) / 1600) ≤ (7943043389 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftOneBatch057Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1140 : ℝ) / 1600 = 57 / 80 by norm_num,
    show ((1140 : ℝ) + 20) / 1600 = (57 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch057Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-10677946617 / 250000000000 : ℝ)
  | 1 => (-42118880541 / 1000000000000 : ℝ)
  | 2 => (-41520896069 / 1000000000000 : ℝ)
  | 3 => (-5114727471 / 125000000000 : ℝ)
  | 4 => (-40309638407 / 1000000000000 : ℝ)
  | 5 => (-19848169407 / 500000000000 : ℝ)
  | 6 => (-39077907869 / 1000000000000 : ℝ)
  | 7 => (-38454332513 / 1000000000000 : ℝ)
  | 8 => (-147756249 / 3906250000 : ℝ)
  | 9 => (-37191696617 / 1000000000000 : ℝ)
  | 10 => (-36552610247 / 1000000000000 : ℝ)
  | 11 => (-280533811 / 7812500000 : ℝ)
  | 12 => (-4407354567 / 125000000000 : ℝ)
  | 13 => (-34604123727 / 1000000000000 : ℝ)
  | 14 => (-33944176737 / 1000000000000 : ℝ)
  | 15 => (-16639491493 / 500000000000 : ℝ)
  | 16 => (-16304264979 / 500000000000 : ℝ)
  | 17 => (-15966402599 / 500000000000 : ℝ)
  | 18 => (-7812949079 / 250000000000 : ℝ)
  | 19 => (-7641372747 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch057Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2105944027 / 50000000000 : ℝ)
  | 1 => (-10380224017 / 250000000000 : ℝ)
  | 2 => (-40917819767 / 1000000000000 : ℝ)
  | 3 => (-20154819203 / 500000000000 : ℝ)
  | 4 => (-39696338813 / 1000000000000 : ℝ)
  | 5 => (-9769476967 / 250000000000 : ℝ)
  | 6 => (-1201697891 / 31250000000 : ℝ)
  | 7 => (-37825599743 / 1000000000000 : ℝ)
  | 8 => (-4648962077 / 125000000000 : ℝ)
  | 9 => (-18276305123 / 500000000000 : ℝ)
  | 10 => (-35908327807 / 1000000000000 : ℝ)
  | 11 => (-7051767307 / 200000000000 : ℝ)
  | 12 => (-17302061863 / 500000000000 : ℝ)
  | 13 => (-1060755523 / 31250000000 : ℝ)
  | 14 => (-6655796597 / 200000000000 : ℝ)
  | 15 => (-32608529957 / 1000000000000 : ℝ)
  | 16 => (-31932805197 / 1000000000000 : ℝ)
  | 17 => (-6250359263 / 200000000000 : ℝ)
  | 18 => (-30565490987 / 1000000000000 : ℝ)
  | 19 => (-29873876953 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch057Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1140 : ℝ) + (j.val : ℝ)) / 1600)
      (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch057Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch057Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1140 : ℝ) + (j.val : ℝ)) / 1600)
    (((1140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch057Neg20WeightLower j.val) (hpThetaShiftOneBatch057Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch057Neg20WeightLower, hpThetaShiftOneBatch057Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch057Neg20_integral_bounds :
    (-1506871599 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (57 / 80 : ℝ) ((57 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-724239747 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch057Lower hpThetaJensenCellsBatch057Upper
    hpThetaShiftOneBatch057Neg20WeightLower hpThetaShiftOneBatch057Neg20WeightUpper hpThetaJensenCellsBatch057_bounds hpThetaShiftOneBatch057Neg20_weight_bounds
  have hl : (-1506871599 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch057Lower j * hpThetaShiftOneBatch057Neg20WeightLower j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftOneBatch057Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftOneBatch057Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch057Lower j * hpThetaShiftOneBatch057Neg20WeightUpper j)
        (hpThetaJensenCellsBatch057Upper j * hpThetaShiftOneBatch057Neg20WeightUpper j) / 1600) ≤ (-724239747 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch057Lower, hpThetaJensenCellsBatch057Upper,
      hpThetaShiftOneBatch057Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1140 : ℝ) / 1600 = 57 / 80 by norm_num,
    show ((1140 : ℝ) + 20) / 1600 = (57 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch057Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch057Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch057Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch057Neg20_integral_bounds
end HodgeProofHP
