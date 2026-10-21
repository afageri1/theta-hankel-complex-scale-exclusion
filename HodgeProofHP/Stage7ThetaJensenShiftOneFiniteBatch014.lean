/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch014

/-! Exact signed weight and batch integral certificates, batch 14 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch014Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1564719481 / 1000000000000 : ℝ)
  | 1 => (-330524539 / 200000000000 : ℝ)
  | 2 => (-1741338823 / 1000000000000 : ℝ)
  | 3 => (-915430897 / 500000000000 : ℝ)
  | 4 => (-1921185347 / 1000000000000 : ℝ)
  | 5 => (-201230303 / 100000000000 : ℝ)
  | 6 => (-526052051 / 250000000000 : ℝ)
  | 7 => (-439378807 / 200000000000 : ℝ)
  | 8 => (-2290353499 / 1000000000000 : ℝ)
  | 9 => (-2384579377 / 1000000000000 : ℝ)
  | 10 => (-1239782129 / 500000000000 : ℝ)
  | 11 => (-1287650267 / 500000000000 : ℝ)
  | 12 => (-1335890201 / 500000000000 : ℝ)
  | 13 => (-346124483 / 125000000000 : ℝ)
  | 14 => (-2866938723 / 1000000000000 : ℝ)
  | 15 => (-1482800291 / 500000000000 : ℝ)
  | 16 => (-61299457 / 20000000000 : ℝ)
  | 17 => (-3165046731 / 1000000000000 : ℝ)
  | 18 => (-3265813233 / 1000000000000 : ℝ)
  | 19 => (-3367263159 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch014Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-295527013 / 200000000000 : ℝ)
  | 1 => (-39117987 / 25000000000 : ℝ)
  | 2 => (-826311347 / 500000000000 : ℝ)
  | 3 => (-870669411 / 500000000000 : ℝ)
  | 4 => (-1830861793 / 1000000000000 : ℝ)
  | 5 => (-960592673 / 500000000000 : ℝ)
  | 6 => (-2012303029 / 1000000000000 : ℝ)
  | 7 => (-2104208203 / 1000000000000 : ℝ)
  | 8 => (-1098447017 / 500000000000 : ℝ)
  | 9 => (-1145176749 / 500000000000 : ℝ)
  | 10 => (-149036211 / 62500000000 : ℝ)
  | 11 => (-2479564257 / 1000000000000 : ℝ)
  | 12 => (-2575300533 / 1000000000000 : ℝ)
  | 13 => (-2671780401 / 1000000000000 : ℝ)
  | 14 => (-2768995863 / 1000000000000 : ℝ)
  | 15 => (-1433469361 / 500000000000 : ℝ)
  | 16 => (-2965600581 / 1000000000000 : ℝ)
  | 17 => (-3064972849 / 1000000000000 : ℝ)
  | 18 => (-316504673 / 100000000000 : ℝ)
  | 19 => (-204113327 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch014Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((280 : ℝ) + (j.val : ℝ)) / 1600)
      (((280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch014Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch014Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((280 : ℝ) + (j.val : ℝ)) / 1600)
    (((280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch014Neg100WeightLower j.val) (hpThetaShiftOneBatch014Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch014Neg100WeightLower, hpThetaShiftOneBatch014Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch014Neg100_integral_bounds :
    (-40055412097 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-594612879 / 15625000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch014Lower hpThetaJensenCellsBatch014Upper
    hpThetaShiftOneBatch014Neg100WeightLower hpThetaShiftOneBatch014Neg100WeightUpper hpThetaJensenCellsBatch014_bounds hpThetaShiftOneBatch014Neg100_weight_bounds
  have hl : (-40055412097 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch014Lower j * hpThetaShiftOneBatch014Neg100WeightLower j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftOneBatch014Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftOneBatch014Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch014Lower j * hpThetaShiftOneBatch014Neg100WeightUpper j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftOneBatch014Neg100WeightUpper j) / 1600) ≤ (-594612879 / 15625000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftOneBatch014Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (280 : ℝ) / 1600 = 14 / 80 by norm_num,
    show ((280 : ℝ) + 20) / 1600 = (14 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch014Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (582790491 / 200000000000 : ℝ)
  | 1 => (2865177197 / 1000000000000 : ℝ)
  | 2 => (1407756807 / 500000000000 : ℝ)
  | 3 => (1382479813 / 500000000000 : ℝ)
  | 4 => (1356756617 / 500000000000 : ℝ)
  | 5 => (1330586261 / 500000000000 : ℝ)
  | 6 => (521587131 / 200000000000 : ℝ)
  | 7 => (2553800881 / 1000000000000 : ℝ)
  | 8 => (1249383267 / 500000000000 : ℝ)
  | 9 => (2442831031 / 1000000000000 : ℝ)
  | 10 => (2385992873 / 1000000000000 : ℝ)
  | 11 => (291031331 / 125000000000 : ℝ)
  | 12 => (283700379 / 125000000000 : ℝ)
  | 13 => (442009757 / 200000000000 : ℝ)
  | 14 => (2149586759 / 1000000000000 : ℝ)
  | 15 => (208821589 / 100000000000 : ℝ)
  | 16 => (2025935207 / 1000000000000 : ℝ)
  | 17 => (490685957 / 250000000000 : ℝ)
  | 18 => (5933253 / 3125000000 : ℝ)
  | 19 => (114601619 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch014Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (740460387 / 250000000000 : ℝ)
  | 1 => (364244057 / 125000000000 : ℝ)
  | 2 => (1432588599 / 500000000000 : ℝ)
  | 3 => (563102723 / 200000000000 : ℝ)
  | 4 => (2764959627 / 1000000000000 : ℝ)
  | 5 => (542702647 / 200000000000 : ℝ)
  | 6 => (2661172523 / 1000000000000 : ℝ)
  | 7 => (325991957 / 125000000000 : ℝ)
  | 8 => (1276900441 / 500000000000 : ℝ)
  | 9 => (499753307 / 200000000000 : ℝ)
  | 10 => (305353879 / 125000000000 : ℝ)
  | 11 => (1192996437 / 500000000000 : ℝ)
  | 12 => (2328250649 / 1000000000000 : ℝ)
  | 13 => (2269603033 / 1000000000000 : ℝ)
  | 14 => (1105024393 / 500000000000 : ℝ)
  | 15 => (53739669 / 25000000000 : ℝ)
  | 16 => (2088215891 / 1000000000000 : ℝ)
  | 17 => (253241901 / 125000000000 : ℝ)
  | 18 => (1962743829 / 1000000000000 : ℝ)
  | 19 => (1898640961 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch014Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((280 : ℝ) + (j.val : ℝ)) / 1600)
      (((280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch014Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch014Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((280 : ℝ) + (j.val : ℝ)) / 1600)
    (((280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch014Neg65WeightLower j.val) (hpThetaShiftOneBatch014Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch014Neg65WeightLower, hpThetaShiftOneBatch014Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch014Neg65_integral_bounds :
    (39039114883 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (20212315849 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch014Lower hpThetaJensenCellsBatch014Upper
    hpThetaShiftOneBatch014Neg65WeightLower hpThetaShiftOneBatch014Neg65WeightUpper hpThetaJensenCellsBatch014_bounds hpThetaShiftOneBatch014Neg65_weight_bounds
  have hl : (39039114883 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch014Lower j * hpThetaShiftOneBatch014Neg65WeightLower j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftOneBatch014Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftOneBatch014Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch014Lower j * hpThetaShiftOneBatch014Neg65WeightUpper j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftOneBatch014Neg65WeightUpper j) / 1600) ≤ (20212315849 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftOneBatch014Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (280 : ℝ) / 1600 = 14 / 80 by norm_num,
    show ((280 : ℝ) + 20) / 1600 = (14 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch014Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (7047737181 / 1000000000000 : ℝ)
  | 1 => (880730119 / 125000000000 : ℝ)
  | 2 => (281732263 / 40000000000 : ℝ)
  | 3 => (3520064809 / 500000000000 : ℝ)
  | 4 => (7036305671 / 1000000000000 : ℝ)
  | 5 => (140636607 / 20000000000 : ℝ)
  | 6 => (1756674823 / 250000000000 : ℝ)
  | 7 => (7020908157 / 1000000000000 : ℝ)
  | 8 => (7014452631 / 1000000000000 : ℝ)
  | 9 => (3503664211 / 500000000000 : ℝ)
  | 10 => (3499765633 / 500000000000 : ℝ)
  | 11 => (6991056919 / 1000000000000 : ℝ)
  | 12 => (436368823 / 62500000000 : ℝ)
  | 13 => (3486029911 / 500000000000 : ℝ)
  | 14 => (6961528717 / 1000000000000 : ℝ)
  | 15 => (1737575929 / 250000000000 : ℝ)
  | 16 => (6938380707 / 1000000000000 : ℝ)
  | 17 => (6925755609 / 1000000000000 : ℝ)
  | 18 => (1728106091 / 250000000000 : ℝ)
  | 19 => (215574467 / 31250000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch014Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1762249929 / 250000000000 : ℝ)
  | 1 => (3523868591 / 500000000000 : ℝ)
  | 2 => (7045840953 / 1000000000000 : ℝ)
  | 3 => (440206661 / 62500000000 : ℝ)
  | 4 => (7040129619 / 1000000000000 : ℝ)
  | 5 => (879538209 / 125000000000 : ℝ)
  | 6 => (7031830351 / 1000000000000 : ℝ)
  | 7 => (7026699293 / 1000000000000 : ℝ)
  | 8 => (3510454079 / 500000000000 : ℝ)
  | 9 => (876806579 / 125000000000 : ℝ)
  | 10 => (7007328423 / 1000000000000 : ℝ)
  | 11 => (6999531267 / 1000000000000 : ℝ)
  | 12 => (174776423 / 25000000000 : ℝ)
  | 13 => (6981901169 / 1000000000000 : ℝ)
  | 14 => (6972059823 / 1000000000000 : ℝ)
  | 15 => (3480764359 / 500000000000 : ℝ)
  | 16 => (6950303717 / 1000000000000 : ℝ)
  | 17 => (1734595177 / 250000000000 : ℝ)
  | 18 => (692575561 / 100000000000 : ℝ)
  | 19 => (1382484873 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch014Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((280 : ℝ) + (j.val : ℝ)) / 1600)
      (((280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch014Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch014Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((280 : ℝ) + (j.val : ℝ)) / 1600)
    (((280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch014Neg40WeightLower j.val) (hpThetaShiftOneBatch014Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch014Neg40WeightLower, hpThetaShiftOneBatch014Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch014Neg40_integral_bounds :
    (56786664727 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (57516967177 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch014Lower hpThetaJensenCellsBatch014Upper
    hpThetaShiftOneBatch014Neg40WeightLower hpThetaShiftOneBatch014Neg40WeightUpper hpThetaJensenCellsBatch014_bounds hpThetaShiftOneBatch014Neg40_weight_bounds
  have hl : (56786664727 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch014Lower j * hpThetaShiftOneBatch014Neg40WeightLower j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftOneBatch014Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftOneBatch014Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch014Lower j * hpThetaShiftOneBatch014Neg40WeightUpper j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftOneBatch014Neg40WeightUpper j) / 1600) ≤ (57516967177 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftOneBatch014Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (280 : ℝ) / 1600 = 14 / 80 by norm_num,
    show ((280 : ℝ) + 20) / 1600 = (14 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch014Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (5453043561 / 500000000000 : ℝ)
  | 1 => (2738598611 / 250000000000 : ℝ)
  | 2 => (1375309739 / 125000000000 : ℝ)
  | 3 => (11050333901 / 1000000000000 : ℝ)
  | 4 => (2219591757 / 200000000000 : ℝ)
  | 5 => (11145348933 / 1000000000000 : ℝ)
  | 6 => (2238500143 / 200000000000 : ℝ)
  | 7 => (2247882099 / 200000000000 : ℝ)
  | 8 => (11286074639 / 1000000000000 : ℝ)
  | 9 => (11332489509 / 1000000000000 : ℝ)
  | 10 => (2275730293 / 200000000000 : ℝ)
  | 11 => (5712278433 / 500000000000 : ℝ)
  | 12 => (2867550517 / 250000000000 : ℝ)
  | 13 => (11515583429 / 1000000000000 : ℝ)
  | 14 => (5780348651 / 500000000000 : ℝ)
  | 15 => (290138501 / 25000000000 : ℝ)
  | 16 => (2912526999 / 250000000000 : ℝ)
  | 17 => (146179969 / 12500000000 : ℝ)
  | 18 => (11738404961 / 1000000000000 : ℝ)
  | 19 => (1178212667 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch014Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2190878889 / 200000000000 : ℝ)
  | 1 => (11002477913 / 1000000000000 : ℝ)
  | 2 => (5525166951 / 500000000000 : ℝ)
  | 3 => (5548979393 / 500000000000 : ℝ)
  | 4 => (5572674467 / 500000000000 : ℝ)
  | 5 => (2798125179 / 250000000000 : ℝ)
  | 6 => (175615789 / 15625000000 : ℝ)
  | 7 => (141075933 / 12500000000 : ℝ)
  | 8 => (1133248951 / 100000000000 : ℝ)
  | 9 => (5689325733 / 500000000000 : ℝ)
  | 10 => (11424556867 / 1000000000000 : ℝ)
  | 11 => (11470202069 / 1000000000000 : ℝ)
  | 12 => (1151558343 / 100000000000 : ℝ)
  | 13 => (11560697303 / 1000000000000 : ℝ)
  | 14 => (11605540041 / 1000000000000 : ℝ)
  | 15 => (11650107997 / 1000000000000 : ℝ)
  | 16 => (11694397521 / 1000000000000 : ℝ)
  | 17 => (5869202481 / 500000000000 : ℝ)
  | 18 => (11782126671 / 1000000000000 : ℝ)
  | 19 => (2956389749 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch014Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((280 : ℝ) + (j.val : ℝ)) / 1600)
      (((280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch014Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch014Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((280 : ℝ) + (j.val : ℝ)) / 1600)
    (((280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch014Neg20WeightLower j.val) (hpThetaShiftOneBatch014Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch014Neg20WeightLower, hpThetaShiftOneBatch014Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch014Neg20_integral_bounds :
    (184305941653 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (14 / 80 : ℝ) ((14 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (23404082123 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch014Lower hpThetaJensenCellsBatch014Upper
    hpThetaShiftOneBatch014Neg20WeightLower hpThetaShiftOneBatch014Neg20WeightUpper hpThetaJensenCellsBatch014_bounds hpThetaShiftOneBatch014Neg20_weight_bounds
  have hl : (184305941653 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch014Lower j * hpThetaShiftOneBatch014Neg20WeightLower j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftOneBatch014Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftOneBatch014Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch014Lower j * hpThetaShiftOneBatch014Neg20WeightUpper j)
        (hpThetaJensenCellsBatch014Upper j * hpThetaShiftOneBatch014Neg20WeightUpper j) / 1600) ≤ (23404082123 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch014Lower, hpThetaJensenCellsBatch014Upper,
      hpThetaShiftOneBatch014Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (280 : ℝ) / 1600 = 14 / 80 by norm_num,
    show ((280 : ℝ) + 20) / 1600 = (14 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch014Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch014Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch014Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch014Neg20_integral_bounds
end HodgeProofHP
