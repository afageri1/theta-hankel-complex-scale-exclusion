/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch067

/-! Exact signed weight and batch integral certificates, batch 67 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch067Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3513044800467 / 50000000000 : ℝ)
  | 1 => (-4423477675909 / 62500000000 : ℝ)
  | 2 => (-35646777617641 / 500000000000 : ℝ)
  | 3 => (-7013149353 / 97656250 : ℝ)
  | 4 => (-14467788280437 / 200000000000 : ℝ)
  | 5 => (-18216611888343 / 250000000000 : ℝ)
  | 6 => (-28670775051 / 390625000 : ℝ)
  | 7 => (-9241395937853 / 125000000000 : ℝ)
  | 8 => (-74468414106247 / 1000000000000 : ℝ)
  | 9 => (-18752235111033 / 250000000000 : ℝ)
  | 10 => (-3777638154361 / 50000000000 : ℝ)
  | 11 => (-38049949336949 / 500000000000 : ℝ)
  | 12 => (-38325181955211 / 500000000000 : ℝ)
  | 13 => (-617633404569 / 8000000000 : ℝ)
  | 14 => (-77761350498637 / 1000000000000 : ℝ)
  | 15 => (-39160952802051 / 500000000000 : ℝ)
  | 16 => (-7888585786739 / 100000000000 : ℝ)
  | 17 => (-39726612168661 / 500000000000 : ℝ)
  | 18 => (-2000600553297 / 25000000000 : ℝ)
  | 19 => (-80598268438431 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch067Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-69749298782451 / 1000000000000 : ℝ)
  | 1 => (-70260896009339 / 1000000000000 : ℝ)
  | 2 => (-70775642814543 / 1000000000000 : ℝ)
  | 3 => (-71293555235281 / 1000000000000 : ℝ)
  | 4 => (-7013149353 / 97656250 : ℝ)
  | 5 => (-9042367675273 / 125000000000 : ℝ)
  | 6 => (-72866447553371 / 1000000000000 : ℝ)
  | 7 => (-73397184130559 / 1000000000000 : ℝ)
  | 8 => (-73931167502823 / 1000000000000 : ℝ)
  | 9 => (-37234207053123 / 500000000000 : ℝ)
  | 10 => (-75008940444131 / 1000000000000 : ℝ)
  | 11 => (-75552763087219 / 1000000000000 : ℝ)
  | 12 => (-76099898673897 / 1000000000000 : ℝ)
  | 13 => (-76650363910421 / 1000000000000 : ℝ)
  | 14 => (-19301043892781 / 250000000000 : ℝ)
  | 15 => (-19440337624659 / 250000000000 : ℝ)
  | 16 => (-78321905604101 / 1000000000000 : ℝ)
  | 17 => (-78885857867389 / 1000000000000 : ℝ)
  | 18 => (-79453224337321 / 1000000000000 : ℝ)
  | 19 => (-80024022131879 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch067Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1340 : ℝ) + (j.val : ℝ)) / 1600)
      (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch067Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch067Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1340 : ℝ) + (j.val : ℝ)) / 1600)
    (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch067Neg100WeightLower j.val) (hpThetaShiftOneBatch067Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch067Neg100WeightLower, hpThetaShiftOneBatch067Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch067Neg100_integral_bounds :
    (-6456920379 / 50000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-6240937991 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch067Lower hpThetaJensenCellsBatch067Upper
    hpThetaShiftOneBatch067Neg100WeightLower hpThetaShiftOneBatch067Neg100WeightUpper hpThetaJensenCellsBatch067_bounds hpThetaShiftOneBatch067Neg100_weight_bounds
  have hl : (-6456920379 / 50000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch067Lower j * hpThetaShiftOneBatch067Neg100WeightLower j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftOneBatch067Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftOneBatch067Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch067Lower j * hpThetaShiftOneBatch067Neg100WeightUpper j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftOneBatch067Neg100WeightUpper j) / 1600) ≤ (-6240937991 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftOneBatch067Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1340 : ℝ) / 1600 = 67 / 80 by norm_num,
    show ((1340 : ℝ) + 20) / 1600 = (67 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch067Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5428589576213 / 500000000000 : ℝ)
  | 1 => (-5477274311579 / 500000000000 : ℝ)
  | 2 => (-11052603703533 / 1000000000000 : ℝ)
  | 3 => (-11151348222229 / 1000000000000 : ℝ)
  | 4 => (-5625393012347 / 500000000000 : ℝ)
  | 5 => (-2270184194641 / 200000000000 : ℝ)
  | 6 => (-11451756946927 / 1000000000000 : ℝ)
  | 7 => (-11553297841961 / 1000000000000 : ℝ)
  | 8 => (-728471723213 / 62500000000 : ℝ)
  | 9 => (-5879255032711 / 500000000000 : ℝ)
  | 10 => (-2965547317817 / 250000000000 : ℝ)
  | 11 => (-11966589153377 / 1000000000000 : ℝ)
  | 12 => (-12071713693403 / 1000000000000 : ℝ)
  | 13 => (-3044391722571 / 250000000000 : ℝ)
  | 14 => (-12284152760293 / 1000000000000 : ℝ)
  | 15 => (-12391475337099 / 1000000000000 : ℝ)
  | 16 => (-781221166989 / 62500000000 : ℝ)
  | 17 => (-12608346833101 / 1000000000000 : ℝ)
  | 18 => (-1271790390713 / 100000000000 : ℝ)
  | 19 => (-1603526749717 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch067Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-672530717461 / 62500000000 : ℝ)
  | 1 => (-434287166097 / 40000000000 : ℝ)
  | 2 => (-10954548623157 / 1000000000000 : ℝ)
  | 3 => (-2763150925883 / 250000000000 : ℝ)
  | 4 => (-2787837055557 / 250000000000 : ℝ)
  | 5 => (-11250786024693 / 1000000000000 : ℝ)
  | 6 => (-2837730243301 / 250000000000 : ℝ)
  | 7 => (-5725878473463 / 500000000000 : ℝ)
  | 8 => (-288832446049 / 25000000000 : ℝ)
  | 9 => (-11655547571407 / 1000000000000 : ℝ)
  | 10 => (-11758510065421 / 1000000000000 : ℝ)
  | 11 => (-11862189271267 / 1000000000000 : ℝ)
  | 12 => (-373955911043 / 31250000000 : ℝ)
  | 13 => (-6035856846701 / 500000000000 : ℝ)
  | 14 => (-12177566890283 / 1000000000000 : ℝ)
  | 15 => (-3071038190073 / 250000000000 : ℝ)
  | 16 => (-6195737668549 / 500000000000 : ℝ)
  | 17 => (-12499538671823 / 1000000000000 : ℝ)
  | 18 => (-126083468331 / 10000000000 : ℝ)
  | 19 => (-12717903907129 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch067Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1340 : ℝ) + (j.val : ℝ)) / 1600)
      (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch067Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch067Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1340 : ℝ) + (j.val : ℝ)) / 1600)
    (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch067Neg65WeightLower j.val) (hpThetaShiftOneBatch067Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch067Neg65WeightLower, hpThetaShiftOneBatch067Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch067Neg65_integral_bounds :
    (-316347817 / 15625000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-9769230269 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch067Lower hpThetaJensenCellsBatch067Upper
    hpThetaShiftOneBatch067Neg65WeightLower hpThetaShiftOneBatch067Neg65WeightUpper hpThetaJensenCellsBatch067_bounds hpThetaShiftOneBatch067Neg65_weight_bounds
  have hl : (-316347817 / 15625000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch067Lower j * hpThetaShiftOneBatch067Neg65WeightLower j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftOneBatch067Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftOneBatch067Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch067Lower j * hpThetaShiftOneBatch067Neg65WeightUpper j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftOneBatch067Neg65WeightUpper j) / 1600) ≤ (-9769230269 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftOneBatch067Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1340 : ℝ) / 1600 = 67 / 80 by norm_num,
    show ((1340 : ℝ) + 20) / 1600 = (67 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch067Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3005385859 / 500000000000 : ℝ)
  | 1 => (-61186761 / 40000000000 : ℝ)
  | 2 => (-9160849147 / 1000000000000 : ℝ)
  | 3 => (-16883425199 / 1000000000000 : ℝ)
  | 4 => (-24698057063 / 1000000000000 : ℝ)
  | 5 => (-1304216319 / 40000000000 : ℝ)
  | 6 => (-2537884033 / 62500000000 : ℝ)
  | 7 => (-48700936687 / 1000000000000 : ℝ)
  | 8 => (-11378091561 / 200000000000 : ℝ)
  | 9 => (-65175384629 / 1000000000000 : ℝ)
  | 10 => (-73556397317 / 1000000000000 : ℝ)
  | 11 => (-1640683589 / 20000000000 : ℝ)
  | 12 => (-2265235451 / 25000000000 : ℝ)
  | 13 => (-24820700887 / 250000000000 : ℝ)
  | 14 => (-54027514947 / 500000000000 : ℝ)
  | 15 => (-29231698617 / 250000000000 : ℝ)
  | 16 => (-25179759629 / 200000000000 : ℝ)
  | 17 => (-26994349059 / 200000000000 : ℝ)
  | 18 => (-720731719 / 5000000000 : ℝ)
  | 19 => (-7671165253 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch067Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (6730563153 / 500000000000 : ℝ)
  | 1 => (6010771719 / 1000000000000 : ℝ)
  | 2 => (-47802157 / 31250000000 : ℝ)
  | 3 => (-4580424573 / 500000000000 : ℝ)
  | 4 => (-8441712599 / 500000000000 : ℝ)
  | 5 => (-12349028531 / 500000000000 : ℝ)
  | 6 => (-16302703987 / 500000000000 : ℝ)
  | 7 => (-40606144527 / 1000000000000 : ℝ)
  | 8 => (-24350468343 / 500000000000 : ℝ)
  | 9 => (-14222614451 / 250000000000 : ℝ)
  | 10 => (-16293846157 / 250000000000 : ℝ)
  | 11 => (-18389099329 / 250000000000 : ℝ)
  | 12 => (-82034179449 / 1000000000000 : ℝ)
  | 13 => (-90609418039 / 1000000000000 : ℝ)
  | 14 => (-99282803547 / 1000000000000 : ℝ)
  | 15 => (-108055029893 / 1000000000000 : ℝ)
  | 16 => (-116926794467 / 1000000000000 : ℝ)
  | 17 => (-1967168721 / 15625000000 : ℝ)
  | 18 => (-67485872647 / 500000000000 : ℝ)
  | 19 => (-144146343799 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch067Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1340 : ℝ) + (j.val : ℝ)) / 1600)
      (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch067Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch067Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1340 : ℝ) + (j.val : ℝ)) / 1600)
    (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch067Neg40WeightLower j.val) (hpThetaShiftOneBatch067Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch067Neg40WeightLower, hpThetaShiftOneBatch067Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch067Neg40_integral_bounds :
    (-113438913 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-96472483 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch067Lower hpThetaJensenCellsBatch067Upper
    hpThetaShiftOneBatch067Neg40WeightLower hpThetaShiftOneBatch067Neg40WeightUpper hpThetaJensenCellsBatch067_bounds hpThetaShiftOneBatch067Neg40_weight_bounds
  have hl : (-113438913 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch067Lower j * hpThetaShiftOneBatch067Neg40WeightLower j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftOneBatch067Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftOneBatch067Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch067Lower j * hpThetaShiftOneBatch067Neg40WeightUpper j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftOneBatch067Neg40WeightUpper j) / 1600) ≤ (-96472483 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftOneBatch067Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1340 : ℝ) / 1600 = 67 / 80 by norm_num,
    show ((1340 : ℝ) + 20) / 1600 = (67 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch067Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (23626795307 / 125000000000 : ℝ)
  | 1 => (23845981181 / 125000000000 : ℝ)
  | 2 => (96263491111 / 500000000000 : ℝ)
  | 3 => (1214323419 / 6250000000 : ℝ)
  | 4 => (19606212993 / 100000000000 : ℝ)
  | 5 => (197838116679 / 1000000000000 : ℝ)
  | 6 => (4990492321 / 25000000000 : ℝ)
  | 7 => (100703421861 / 500000000000 : ℝ)
  | 8 => (203199554397 / 1000000000000 : ℝ)
  | 9 => (51249452423 / 250000000000 : ℝ)
  | 10 => (206801594191 / 1000000000000 : ℝ)
  | 11 => (52152723059 / 250000000000 : ℝ)
  | 12 => (105212843959 / 500000000000 : ℝ)
  | 13 => (212245965087 / 1000000000000 : ℝ)
  | 14 => (214071707339 / 1000000000000 : ℝ)
  | 15 => (215902898023 / 1000000000000 : ℝ)
  | 16 => (217739520237 / 1000000000000 : ℝ)
  | 17 => (219581556827 / 1000000000000 : ℝ)
  | 18 => (13839311899 / 62500000000 : ℝ)
  | 19 => (44656360649 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch067Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (190767849449 / 1000000000000 : ℝ)
  | 1 => (192526982223 / 1000000000000 : ℝ)
  | 2 => (194291747041 / 1000000000000 : ℝ)
  | 3 => (196062129931 / 1000000000000 : ℝ)
  | 4 => (4945952917 / 25000000000 : ℝ)
  | 5 => (199619692841 / 1000000000000 : ℝ)
  | 6 => (201406843723 / 1000000000000 : ℝ)
  | 7 => (101599777199 / 500000000000 : ℝ)
  | 8 => (204997809693 / 1000000000000 : ℝ)
  | 9 => (12925099637 / 62500000000 : ℝ)
  | 10 => (208610892237 / 1000000000000 : ℝ)
  | 11 => (210425687919 / 1000000000000 : ℝ)
  | 12 => (6632686409 / 31250000000 : ℝ)
  | 13 => (10703585367 / 50000000000 : ℝ)
  | 14 => (26987862253 / 125000000000 : ℝ)
  | 15 => (108869760119 / 500000000000 : ℝ)
  | 16 => (54895389207 / 250000000000 : ℝ)
  | 17 => (44285798077 / 200000000000 : ℝ)
  | 18 => (111640901623 / 500000000000 : ℝ)
  | 19 => (225139977493 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch067Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1340 : ℝ) + (j.val : ℝ)) / 1600)
      (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch067Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch067Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1340 : ℝ) + (j.val : ℝ)) / 1600)
    (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch067Neg20WeightLower j.val) (hpThetaShiftOneBatch067Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch067Neg20WeightLower, hpThetaShiftOneBatch067Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch067Neg20_integral_bounds :
    (171724403 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (177939467 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch067Lower hpThetaJensenCellsBatch067Upper
    hpThetaShiftOneBatch067Neg20WeightLower hpThetaShiftOneBatch067Neg20WeightUpper hpThetaJensenCellsBatch067_bounds hpThetaShiftOneBatch067Neg20_weight_bounds
  have hl : (171724403 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch067Lower j * hpThetaShiftOneBatch067Neg20WeightLower j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftOneBatch067Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftOneBatch067Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch067Lower j * hpThetaShiftOneBatch067Neg20WeightUpper j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftOneBatch067Neg20WeightUpper j) / 1600) ≤ (177939467 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftOneBatch067Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1340 : ℝ) / 1600 = 67 / 80 by norm_num,
    show ((1340 : ℝ) + 20) / 1600 = (67 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch067Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch067Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch067Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch067Neg20_integral_bounds
end HodgeProofHP
