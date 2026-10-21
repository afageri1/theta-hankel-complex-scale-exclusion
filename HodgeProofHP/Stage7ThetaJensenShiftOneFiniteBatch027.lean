/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch027

/-! Exact signed weight and batch integral certificates, batch 27 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch027Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (232150187 / 125000000000 : ℝ)
  | 1 => (1144551457 / 500000000000 : ℝ)
  | 2 => (2726832823 / 1000000000000 : ℝ)
  | 3 => (634081753 / 200000000000 : ℝ)
  | 4 => (904961939 / 250000000000 : ℝ)
  | 5 => (4075166279 / 1000000000000 : ℝ)
  | 6 => (1134095069 / 250000000000 : ℝ)
  | 7 => (1250876283 / 250000000000 : ℝ)
  | 8 => (219062227 / 40000000000 : ℝ)
  | 9 => (5955546159 / 1000000000000 : ℝ)
  | 10 => (3220245129 / 500000000000 : ℝ)
  | 11 => (6931401059 / 1000000000000 : ℝ)
  | 12 => (3714145523 / 500000000000 : ℝ)
  | 13 => (30981141 / 3906250000 : ℝ)
  | 14 => (4220027733 / 500000000000 : ℝ)
  | 15 => (8954951787 / 1000000000000 : ℝ)
  | 16 => (9475871049 / 1000000000000 : ℝ)
  | 17 => (5001411297 / 500000000000 : ℝ)
  | 18 => (2633953777 / 250000000000 : ℝ)
  | 19 => (11074856607 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch027Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (457820583 / 200000000000 : ℝ)
  | 1 => (340854103 / 125000000000 : ℝ)
  | 2 => (1585204383 / 500000000000 : ℝ)
  | 3 => (3619847757 / 1000000000000 : ℝ)
  | 4 => (101879157 / 25000000000 : ℝ)
  | 5 => (4536380277 / 1000000000000 : ℝ)
  | 6 => (5003505133 / 1000000000000 : ℝ)
  | 7 => (1369138919 / 250000000000 : ℝ)
  | 8 => (74444327 / 12500000000 : ℝ)
  | 9 => (6440490259 / 1000000000000 : ℝ)
  | 10 => (346570053 / 50000000000 : ℝ)
  | 11 => (7428291047 / 1000000000000 : ℝ)
  | 12 => (7931172097 / 1000000000000 : ℝ)
  | 13 => (8440055467 / 1000000000000 : ℝ)
  | 14 => (2238737947 / 250000000000 : ℝ)
  | 15 => (189517421 / 20000000000 : ℝ)
  | 16 => (2000564519 / 200000000000 : ℝ)
  | 17 => (10535815109 / 1000000000000 : ℝ)
  | 18 => (346089269 / 31250000000 : ℝ)
  | 19 => (2904988607 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch027Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((540 : ℝ) + (j.val : ℝ)) / 1600)
      (((540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch027Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch027Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((540 : ℝ) + (j.val : ℝ)) / 1600)
    (((540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch027Neg100WeightLower j.val) (hpThetaShiftOneBatch027Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch027Neg100WeightLower, hpThetaShiftOneBatch027Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch027Neg100_integral_bounds :
    (42178937501 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (46107860659 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch027Lower hpThetaJensenCellsBatch027Upper
    hpThetaShiftOneBatch027Neg100WeightLower hpThetaShiftOneBatch027Neg100WeightUpper hpThetaJensenCellsBatch027_bounds hpThetaShiftOneBatch027Neg100_weight_bounds
  have hl : (42178937501 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch027Lower j * hpThetaShiftOneBatch027Neg100WeightLower j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftOneBatch027Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftOneBatch027Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch027Lower j * hpThetaShiftOneBatch027Neg100WeightUpper j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftOneBatch027Neg100WeightUpper j) / 1600) ≤ (46107860659 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftOneBatch027Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (540 : ℝ) / 1600 = 27 / 80 by norm_num,
    show ((540 : ℝ) + 20) / 1600 = (27 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch027Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6330847187 / 250000000000 : ℝ)
  | 1 => (-2534365347 / 100000000000 : ℝ)
  | 2 => (-3170171561 / 125000000000 : ℝ)
  | 3 => (-6344129389 / 250000000000 : ℝ)
  | 4 => (-12694530187 / 500000000000 : ℝ)
  | 5 => (-25398972591 / 1000000000000 : ℝ)
  | 6 => (-6351556451 / 250000000000 : ℝ)
  | 7 => (-12705395783 / 500000000000 : ℝ)
  | 8 => (-12706320691 / 500000000000 : ℝ)
  | 9 => (-6353178239 / 250000000000 : ℝ)
  | 10 => (-25411746711 / 1000000000000 : ℝ)
  | 11 => (-25408078971 / 1000000000000 : ℝ)
  | 12 => (-1270080477 / 50000000000 : ℝ)
  | 13 => (-5078461951 / 200000000000 : ℝ)
  | 14 => (-5076030183 / 200000000000 : ℝ)
  | 15 => (-12682552143 / 500000000000 : ℝ)
  | 16 => (-25347141097 / 1000000000000 : ℝ)
  | 17 => (-6331558137 / 250000000000 : ℝ)
  | 18 => (-25302349807 / 1000000000000 : ℝ)
  | 19 => (-5055092803 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch027Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6325151629 / 250000000000 : ℝ)
  | 1 => (-25323388747 / 1000000000000 : ℝ)
  | 2 => (-25343653469 / 1000000000000 : ℝ)
  | 3 => (-25361372487 / 1000000000000 : ℝ)
  | 4 => (-5075303511 / 200000000000 : ℝ)
  | 5 => (-25389060373 / 1000000000000 : ℝ)
  | 6 => (-2539897259 / 100000000000 : ℝ)
  | 7 => (-25406225803 / 1000000000000 : ℝ)
  | 8 => (-5082158313 / 200000000000 : ℝ)
  | 9 => (-2541174671 / 100000000000 : ℝ)
  | 10 => (-2540807897 / 100000000000 : ℝ)
  | 11 => (-25401609539 / 1000000000000 : ℝ)
  | 12 => (-12696154877 / 500000000000 : ℝ)
  | 13 => (-12690075457 / 500000000000 : ℝ)
  | 14 => (-5073020857 / 200000000000 : ℝ)
  | 15 => (-3168392637 / 125000000000 : ℝ)
  | 16 => (-25326232547 / 1000000000000 : ℝ)
  | 17 => (-12651174903 / 500000000000 : ℝ)
  | 18 => (-12637732007 / 500000000000 : ℝ)
  | 19 => (-6311386571 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch027Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((540 : ℝ) + (j.val : ℝ)) / 1600)
      (((540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch027Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch027Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((540 : ℝ) + (j.val : ℝ)) / 1600)
    (((540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch027Neg65WeightLower j.val) (hpThetaShiftOneBatch027Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch027Neg65WeightLower, hpThetaShiftOneBatch027Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch027Neg65_integral_bounds :
    (-2179543997 / 12500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-10744103849 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch027Lower hpThetaJensenCellsBatch027Upper
    hpThetaShiftOneBatch027Neg65WeightLower hpThetaShiftOneBatch027Neg65WeightUpper hpThetaJensenCellsBatch027_bounds hpThetaShiftOneBatch027Neg65_weight_bounds
  have hl : (-2179543997 / 12500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch027Lower j * hpThetaShiftOneBatch027Neg65WeightLower j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftOneBatch027Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftOneBatch027Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch027Lower j * hpThetaShiftOneBatch027Neg65WeightUpper j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftOneBatch027Neg65WeightUpper j) / 1600) ≤ (-10744103849 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftOneBatch027Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (540 : ℝ) / 1600 = 27 / 80 by norm_num,
    show ((540 : ℝ) + 20) / 1600 = (27 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch027Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5069723271 / 250000000000 : ℝ)
  | 1 => (-10233670081 / 500000000000 : ℝ)
  | 2 => (-20655862323 / 1000000000000 : ℝ)
  | 3 => (-260555597 / 12500000000 : ℝ)
  | 4 => (-21033084577 / 1000000000000 : ℝ)
  | 5 => (-21221760791 / 1000000000000 : ℝ)
  | 6 => (-21410464333 / 1000000000000 : ℝ)
  | 7 => (-21599183047 / 1000000000000 : ℝ)
  | 8 => (-21787904691 / 1000000000000 : ℝ)
  | 9 => (-10988308467 / 500000000000 : ℝ)
  | 10 => (-22165307361 / 1000000000000 : ℝ)
  | 11 => (-5588490867 / 250000000000 : ℝ)
  | 12 => (-11271286333 / 500000000000 : ℝ)
  | 13 => (-568278057 / 25000000000 : ℝ)
  | 14 => (-4583919909 / 200000000000 : ℝ)
  | 15 => (-11553995807 / 500000000000 : ℝ)
  | 16 => (-465925711 / 20000000000 : ℝ)
  | 17 => (-5871117083 / 250000000000 : ℝ)
  | 18 => (-23672526853 / 1000000000000 : ℝ)
  | 19 => (-23860447917 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch027Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-20090532811 / 1000000000000 : ℝ)
  | 1 => (-20278893083 / 1000000000000 : ℝ)
  | 2 => (-20467340161 / 1000000000000 : ℝ)
  | 3 => (-10327931161 / 500000000000 : ℝ)
  | 4 => (-20844447759 / 1000000000000 : ℝ)
  | 5 => (-657283893 / 31250000000 : ℝ)
  | 6 => (-2122176079 / 100000000000 : ℝ)
  | 7 => (-5352616083 / 250000000000 : ℝ)
  | 8 => (-10799591523 / 500000000000 : ℝ)
  | 9 => (-2178790469 / 100000000000 : ℝ)
  | 10 => (-21976616933 / 1000000000000 : ℝ)
  | 11 => (-138533171 / 6250000000 : ℝ)
  | 12 => (-22353963467 / 1000000000000 : ℝ)
  | 13 => (-4508514533 / 200000000000 : ℝ)
  | 14 => (-22731122279 / 1000000000000 : ℝ)
  | 15 => (-2864949943 / 125000000000 : ℝ)
  | 16 => (-23107991613 / 1000000000000 : ℝ)
  | 17 => (-23296285549 / 1000000000000 : ℝ)
  | 18 => (-23484468331 / 1000000000000 : ℝ)
  | 19 => (-5918131713 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch027Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((540 : ℝ) + (j.val : ℝ)) / 1600)
      (((540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch027Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch027Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((540 : ℝ) + (j.val : ℝ)) / 1600)
    (((540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch027Neg40WeightLower j.val) (hpThetaShiftOneBatch027Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch027Neg40WeightLower, hpThetaShiftOneBatch027Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch027Neg40_integral_bounds :
    (-30294564147 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-74070614809 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch027Lower hpThetaJensenCellsBatch027Upper
    hpThetaShiftOneBatch027Neg40WeightLower hpThetaShiftOneBatch027Neg40WeightUpper hpThetaJensenCellsBatch027_bounds hpThetaShiftOneBatch027Neg40_weight_bounds
  have hl : (-30294564147 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch027Lower j * hpThetaShiftOneBatch027Neg40WeightLower j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftOneBatch027Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftOneBatch027Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch027Lower j * hpThetaShiftOneBatch027Neg40WeightUpper j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftOneBatch027Neg40WeightUpper j) / 1600) ≤ (-74070614809 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftOneBatch027Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (540 : ℝ) / 1600 = 27 / 80 by norm_num,
    show ((540 : ℝ) + 20) / 1600 = (27 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch027Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2969761971 / 500000000000 : ℝ)
  | 1 => (2910442283 / 500000000000 : ℝ)
  | 2 => (5701332043 / 1000000000000 : ℝ)
  | 3 => (558086611 / 100000000000 : ℝ)
  | 4 => (545948653 / 100000000000 : ℝ)
  | 5 => (2668596549 / 500000000000 : ℝ)
  | 6 => (5213985637 / 1000000000000 : ℝ)
  | 7 => (5089863997 / 1000000000000 : ℝ)
  | 8 => (248241403 / 50000000000 : ℝ)
  | 9 => (967775547 / 200000000000 : ℝ)
  | 10 => (4712012963 / 1000000000000 : ℝ)
  | 11 => (4584233713 / 1000000000000 : ℝ)
  | 12 => (4455539983 / 1000000000000 : ℝ)
  | 13 => (4325931803 / 1000000000000 : ℝ)
  | 14 => (419540923 / 100000000000 : ℝ)
  | 15 => (4063972353 / 1000000000000 : ℝ)
  | 16 => (3931621291 / 1000000000000 : ℝ)
  | 17 => (3798356193 / 1000000000000 : ℝ)
  | 18 => (1832088619 / 500000000000 : ℝ)
  | 19 => (705816927 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch027Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1211450093 / 200000000000 : ℝ)
  | 1 => (5939523943 / 1000000000000 : ℝ)
  | 2 => (5820884567 / 1000000000000 : ℝ)
  | 3 => (1425333011 / 250000000000 : ℝ)
  | 4 => (5580866111 / 1000000000000 : ℝ)
  | 5 => (5459486531 / 1000000000000 : ℝ)
  | 6 => (5337193099 / 1000000000000 : ℝ)
  | 7 => (2606992819 / 500000000000 : ℝ)
  | 8 => (2544931999 / 500000000000 : ℝ)
  | 9 => (4964828061 / 1000000000000 : ℝ)
  | 10 => (604859717 / 125000000000 : ℝ)
  | 11 => (1178003241 / 250000000000 : ℝ)
  | 12 => (2292116857 / 500000000000 : ℝ)
  | 13 => (278471249 / 62500000000 : ℝ)
  | 14 => (1081482951 / 250000000000 : ℝ)
  | 15 => (4195409231 / 1000000000000 : ℝ)
  | 16 => (2031986177 / 500000000000 : ℝ)
  | 17 => (982905323 / 250000000000 : ℝ)
  | 18 => (1899178097 / 500000000000 : ℝ)
  | 19 => (3664177239 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch027Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((540 : ℝ) + (j.val : ℝ)) / 1600)
      (((540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch027Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch027Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((540 : ℝ) + (j.val : ℝ)) / 1600)
    (((540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch027Neg20WeightLower j.val) (hpThetaShiftOneBatch027Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch027Neg20WeightLower, hpThetaShiftOneBatch027Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch027Neg20_integral_bounds :
    (202512091 / 6250000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (27 / 80 : ℝ) ((27 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (8428670393 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch027Lower hpThetaJensenCellsBatch027Upper
    hpThetaShiftOneBatch027Neg20WeightLower hpThetaShiftOneBatch027Neg20WeightUpper hpThetaJensenCellsBatch027_bounds hpThetaShiftOneBatch027Neg20_weight_bounds
  have hl : (202512091 / 6250000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch027Lower j * hpThetaShiftOneBatch027Neg20WeightLower j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftOneBatch027Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftOneBatch027Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch027Lower j * hpThetaShiftOneBatch027Neg20WeightUpper j)
        (hpThetaJensenCellsBatch027Upper j * hpThetaShiftOneBatch027Neg20WeightUpper j) / 1600) ≤ (8428670393 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch027Lower, hpThetaJensenCellsBatch027Upper,
      hpThetaShiftOneBatch027Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (540 : ℝ) / 1600 = 27 / 80 by norm_num,
    show ((540 : ℝ) + 20) / 1600 = (27 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch027Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch027Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch027Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch027Neg20_integral_bounds
end HodgeProofHP
