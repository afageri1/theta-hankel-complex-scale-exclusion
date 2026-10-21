/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch023

/-! Exact signed weight and batch integral certificates, batch 23 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch023Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-16079160759 / 1000000000000 : ℝ)
  | 1 => (-8012379643 / 500000000000 : ℝ)
  | 2 => (-638678187 / 40000000000 : ℝ)
  | 3 => (-7952855451 / 500000000000 : ℝ)
  | 4 => (-15840991951 / 1000000000000 : ℝ)
  | 5 => (-15772761817 / 1000000000000 : ℝ)
  | 6 => (-15700984511 / 1000000000000 : ℝ)
  | 7 => (-7812812033 / 500000000000 : ℝ)
  | 8 => (-15546644537 / 1000000000000 : ℝ)
  | 9 => (-1933001251 / 125000000000 : ℝ)
  | 10 => (-76888423 / 5000000000 : ℝ)
  | 11 => (-15287632467 / 1000000000000 : ℝ)
  | 12 => (-1519381781 / 100000000000 : ℝ)
  | 13 => (-3774051219 / 250000000000 : ℝ)
  | 14 => (-7497378981 / 500000000000 : ℝ)
  | 15 => (-7444720713 / 500000000000 : ℝ)
  | 16 => (-14780219683 / 1000000000000 : ℝ)
  | 17 => (-14667057219 / 1000000000000 : ℝ)
  | 18 => (-14549918587 / 1000000000000 : ℝ)
  | 19 => (-14428768419 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch023Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3204951857 / 200000000000 : ℝ)
  | 1 => (-7983477337 / 500000000000 : ℝ)
  | 2 => (-15905710901 / 1000000000000 : ℝ)
  | 3 => (-316819839 / 20000000000 : ℝ)
  | 4 => (-1971595227 / 125000000000 : ℝ)
  | 5 => (-1570098451 / 100000000000 : ℝ)
  | 6 => (-3125124813 / 200000000000 : ℝ)
  | 7 => (-1943330567 / 125000000000 : ℝ)
  | 8 => (-15464010007 / 1000000000000 : ℝ)
  | 9 => (-15377684599 / 1000000000000 : ℝ)
  | 10 => (-7643816233 / 500000000000 : ℝ)
  | 11 => (-15193817809 / 1000000000000 : ℝ)
  | 12 => (-120769639 / 8000000000 : ℝ)
  | 13 => (-14994757961 / 1000000000000 : ℝ)
  | 14 => (-595577657 / 40000000000 : ℝ)
  | 15 => (-7390109841 / 500000000000 : ℝ)
  | 16 => (-7333528609 / 500000000000 : ℝ)
  | 17 => (-7274959293 / 500000000000 : ℝ)
  | 18 => (-7214384209 / 500000000000 : ℝ)
  | 19 => (-3575892857 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch023Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((460 : ℝ) + (j.val : ℝ)) / 1600)
      (((460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch023Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch023Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((460 : ℝ) + (j.val : ℝ)) / 1600)
    (((460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch023Neg100WeightLower j.val) (hpThetaShiftOneBatch023Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch023Neg100WeightLower, hpThetaShiftOneBatch023Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch023Neg100_integral_bounds :
    (-9231881633 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-36242578387 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch023Lower hpThetaJensenCellsBatch023Upper
    hpThetaShiftOneBatch023Neg100WeightLower hpThetaShiftOneBatch023Neg100WeightUpper hpThetaJensenCellsBatch023_bounds hpThetaShiftOneBatch023Neg100_weight_bounds
  have hl : (-9231881633 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch023Lower j * hpThetaShiftOneBatch023Neg100WeightLower j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftOneBatch023Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftOneBatch023Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch023Lower j * hpThetaShiftOneBatch023Neg100WeightUpper j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftOneBatch023Neg100WeightUpper j) / 1600) ≤ (-36242578387 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftOneBatch023Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (460 : ℝ) / 1600 = 23 / 80 by norm_num,
    show ((460 : ℝ) + 20) / 1600 = (23 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch023Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-17815349889 / 1000000000000 : ℝ)
  | 1 => (-8977462623 / 500000000000 : ℝ)
  | 2 => (-4523482197 / 250000000000 : ℝ)
  | 3 => (-455808509 / 25000000000 : ℝ)
  | 4 => (-18370139673 / 1000000000000 : ℝ)
  | 5 => (-18507306307 / 1000000000000 : ℝ)
  | 6 => (-4660954927 / 250000000000 : ℝ)
  | 7 => (-9389829597 / 500000000000 : ℝ)
  | 8 => (-18914803951 / 1000000000000 : ℝ)
  | 9 => (-19049233033 / 1000000000000 : ℝ)
  | 10 => (-19182925369 / 1000000000000 : ℝ)
  | 11 => (-19315859753 / 1000000000000 : ℝ)
  | 12 => (-3889602971 / 200000000000 : ℝ)
  | 13 => (-3915873843 / 200000000000 : ℝ)
  | 14 => (-9854950623 / 500000000000 : ℝ)
  | 15 => (-19839589233 / 1000000000000 : ℝ)
  | 16 => (-2496051417 / 125000000000 : ℝ)
  | 17 => (-20096345589 / 1000000000000 : ℝ)
  | 18 => (-202233699 / 10000000000 : ℝ)
  | 19 => (-10174731027 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch023Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-883761137 / 50000000000 : ℝ)
  | 1 => (-139182421 / 7812500000 : ℝ)
  | 2 => (-3590985049 / 200000000000 : ℝ)
  | 3 => (-18093928787 / 1000000000000 : ℝ)
  | 4 => (-18232340359 / 1000000000000 : ℝ)
  | 5 => (-2296267459 / 125000000000 : ℝ)
  | 6 => (-9253653153 / 500000000000 : ℝ)
  | 7 => (-18643819707 / 1000000000000 : ℝ)
  | 8 => (-18779659193 / 1000000000000 : ℝ)
  | 9 => (-378296079 / 20000000000 : ℝ)
  | 10 => (-2381154129 / 125000000000 : ℝ)
  | 11 => (-2397865671 / 125000000000 : ℝ)
  | 12 => (-2414482469 / 125000000000 : ℝ)
  | 13 => (-9724007427 / 500000000000 : ℝ)
  | 14 => (-9789684607 / 500000000000 : ℝ)
  | 15 => (-3941980249 / 200000000000 : ℝ)
  | 16 => (-1239974327 / 62500000000 : ℝ)
  | 17 => (-3993682267 / 200000000000 : ℝ)
  | 18 => (-5024086397 / 250000000000 : ℝ)
  | 19 => (-20223369899 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch023Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((460 : ℝ) + (j.val : ℝ)) / 1600)
      (((460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch023Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch023Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((460 : ℝ) + (j.val : ℝ)) / 1600)
    (((460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch023Neg65WeightLower j.val) (hpThetaShiftOneBatch023Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch023Neg65WeightLower, hpThetaShiftOneBatch023Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch023Neg65_integral_bounds :
    (-183423273767 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-35958277679 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch023Lower hpThetaJensenCellsBatch023Upper
    hpThetaShiftOneBatch023Neg65WeightLower hpThetaShiftOneBatch023Neg65WeightUpper hpThetaJensenCellsBatch023_bounds hpThetaShiftOneBatch023Neg65_weight_bounds
  have hl : (-183423273767 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch023Lower j * hpThetaShiftOneBatch023Neg65WeightLower j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftOneBatch023Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftOneBatch023Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch023Lower j * hpThetaShiftOneBatch023Neg65WeightUpper j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftOneBatch023Neg65WeightUpper j) / 1600) ≤ (-35958277679 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftOneBatch023Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (460 : ℝ) / 1600 = 23 / 80 by norm_num,
    show ((460 : ℝ) + 20) / 1600 = (23 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch023Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6333190213 / 1000000000000 : ℝ)
  | 1 => (-6485009027 / 1000000000000 : ℝ)
  | 2 => (-6637569903 / 1000000000000 : ℝ)
  | 3 => (-6790867781 / 1000000000000 : ℝ)
  | 4 => (-3472448761 / 500000000000 : ℝ)
  | 5 => (-3549826953 / 500000000000 : ℝ)
  | 6 => (-1813782909 / 250000000000 : ℝ)
  | 7 => (-3705662667 / 500000000000 : ℝ)
  | 8 => (-946028693 / 125000000000 : ℝ)
  | 9 => (-7725838729 / 1000000000000 : ℝ)
  | 10 => (-985518409 / 125000000000 : ℝ)
  | 11 => (-321725979 / 40000000000 : ℝ)
  | 12 => (-8202839561 / 1000000000000 : ℝ)
  | 13 => (-8363211671 / 1000000000000 : ℝ)
  | 14 => (-4262129933 / 500000000000 : ℝ)
  | 15 => (-8685978127 / 1000000000000 : ℝ)
  | 16 => (-8848360351 / 1000000000000 : ℝ)
  | 17 => (-9011400357 / 1000000000000 : ℝ)
  | 18 => (-9175091879 / 1000000000000 : ℝ)
  | 19 => (-2334857143 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch023Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6182118443 / 1000000000000 : ℝ)
  | 1 => (-1583297553 / 250000000000 : ℝ)
  | 2 => (-3242504513 / 500000000000 : ℝ)
  | 3 => (-3318784951 / 500000000000 : ℝ)
  | 4 => (-339543389 / 50000000000 : ℝ)
  | 5 => (-6944897521 / 1000000000000 : ℝ)
  | 6 => (-1419930781 / 200000000000 : ℝ)
  | 7 => (-1451026327 / 200000000000 : ℝ)
  | 8 => (-7411325333 / 1000000000000 : ℝ)
  | 9 => (-7568229543 / 1000000000000 : ℝ)
  | 10 => (-965729841 / 125000000000 : ℝ)
  | 11 => (-7884147271 / 1000000000000 : ℝ)
  | 12 => (-4021574737 / 500000000000 : ℝ)
  | 13 => (-205070989 / 25000000000 : ℝ)
  | 14 => (-836321167 / 100000000000 : ℝ)
  | 15 => (-1704851973 / 200000000000 : ℝ)
  | 16 => (-4342989063 / 500000000000 : ℝ)
  | 17 => (-176967207 / 20000000000 : ℝ)
  | 18 => (-2252850089 / 250000000000 : ℝ)
  | 19 => (-4587545939 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch023Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((460 : ℝ) + (j.val : ℝ)) / 1600)
      (((460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch023Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch023Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((460 : ℝ) + (j.val : ℝ)) / 1600)
    (((460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch023Neg40WeightLower j.val) (hpThetaShiftOneBatch023Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch023Neg40WeightLower, hpThetaShiftOneBatch023Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch023Neg40_integral_bounds :
    (-37461826013 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-36230817567 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch023Lower hpThetaJensenCellsBatch023Upper
    hpThetaShiftOneBatch023Neg40WeightLower hpThetaShiftOneBatch023Neg40WeightUpper hpThetaJensenCellsBatch023_bounds hpThetaShiftOneBatch023Neg40_weight_bounds
  have hl : (-37461826013 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch023Lower j * hpThetaShiftOneBatch023Neg40WeightLower j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftOneBatch023Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftOneBatch023Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch023Lower j * hpThetaShiftOneBatch023Neg40WeightUpper j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftOneBatch023Neg40WeightUpper j) / 1600) ≤ (-36230817567 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftOneBatch023Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (460 : ℝ) / 1600 = 23 / 80 by norm_num,
    show ((460 : ℝ) + 20) / 1600 = (23 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch023Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (784045479 / 62500000000 : ℝ)
  | 1 => (6247975977 / 500000000000 : ℝ)
  | 2 => (3111591751 / 250000000000 : ℝ)
  | 3 => (1549496329 / 125000000000 : ℝ)
  | 4 => (12344760677 / 1000000000000 : ℝ)
  | 5 => (12292734997 / 1000000000000 : ℝ)
  | 6 => (3059972867 / 250000000000 : ℝ)
  | 7 => (12186227987 / 1000000000000 : ℝ)
  | 8 => (12131742471 / 1000000000000 : ℝ)
  | 9 => (6038216427 / 500000000000 : ℝ)
  | 10 => (3005074273 / 250000000000 : ℝ)
  | 11 => (5981666581 / 500000000000 : ℝ)
  | 12 => (11905539059 / 1000000000000 : ℝ)
  | 13 => (11846912799 / 1000000000000 : ℝ)
  | 14 => (11787452419 / 1000000000000 : ℝ)
  | 15 => (469086239 / 40000000000 : ℝ)
  | 16 => (2333204309 / 200000000000 : ℝ)
  | 17 => (2901011807 / 250000000000 : ℝ)
  | 18 => (5770615571 / 500000000000 : ℝ)
  | 19 => (2869392857 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch023Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2518539267 / 200000000000 : ℝ)
  | 1 => (2508945533 / 200000000000 : ℝ)
  | 2 => (2499190391 / 200000000000 : ℝ)
  | 3 => (2489273401 / 200000000000 : ℝ)
  | 4 => (12395970633 / 1000000000000 : ℝ)
  | 5 => (6172380339 / 500000000000 : ℝ)
  | 6 => (6146367499 / 500000000000 : ℝ)
  | 7 => (12239891469 / 1000000000000 : ℝ)
  | 8 => (3046556997 / 250000000000 : ℝ)
  | 9 => (1516467809 / 125000000000 : ℝ)
  | 10 => (2415286571 / 200000000000 : ℝ)
  | 11 => (12020297093 / 1000000000000 : ℝ)
  | 12 => (11963333163 / 1000000000000 : ℝ)
  | 13 => (595276953 / 50000000000 : ℝ)
  | 14 => (14808641 / 1250000000 : ℝ)
  | 15 => (589372621 / 50000000000 : ℝ)
  | 16 => (1465894497 / 125000000000 : ℝ)
  | 17 => (5833010773 / 500000000000 : ℝ)
  | 18 => (11604047229 / 1000000000000 : ℝ)
  | 19 => (11541231143 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch023Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((460 : ℝ) + (j.val : ℝ)) / 1600)
      (((460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch023Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch023Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((460 : ℝ) + (j.val : ℝ)) / 1600)
    (((460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch023Neg20WeightLower j.val) (hpThetaShiftOneBatch023Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch023Neg20WeightLower, hpThetaShiftOneBatch023Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch023Neg20_integral_bounds :
    (57115276249 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (116255549673 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch023Lower hpThetaJensenCellsBatch023Upper
    hpThetaShiftOneBatch023Neg20WeightLower hpThetaShiftOneBatch023Neg20WeightUpper hpThetaJensenCellsBatch023_bounds hpThetaShiftOneBatch023Neg20_weight_bounds
  have hl : (57115276249 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch023Lower j * hpThetaShiftOneBatch023Neg20WeightLower j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftOneBatch023Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftOneBatch023Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch023Lower j * hpThetaShiftOneBatch023Neg20WeightUpper j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftOneBatch023Neg20WeightUpper j) / 1600) ≤ (116255549673 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftOneBatch023Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (460 : ℝ) / 1600 = 23 / 80 by norm_num,
    show ((460 : ℝ) + 20) / 1600 = (23 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch023Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch023Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch023Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch023Neg20_integral_bounds
end HodgeProofHP
