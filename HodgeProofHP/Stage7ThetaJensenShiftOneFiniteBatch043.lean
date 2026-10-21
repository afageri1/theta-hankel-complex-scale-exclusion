/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch043

/-! Exact signed weight and batch integral certificates, batch 43 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch043Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-33242114801 / 500000000000 : ℝ)
  | 1 => (-36262675049 / 500000000000 : ℝ)
  | 2 => (-78671672451 / 1000000000000 : ℝ)
  | 3 => (-84924350949 / 1000000000000 : ℝ)
  | 4 => (-91284548891 / 1000000000000 : ℝ)
  | 5 => (-97753438637 / 1000000000000 : ℝ)
  | 6 => (-52166100831 / 500000000000 : ℝ)
  | 7 => (-111022028603 / 1000000000000 : ℝ)
  | 8 => (-7364007457 / 62500000000 : ℝ)
  | 9 => (-31184920727 / 250000000000 : ℝ)
  | 10 => (-131769937829 / 1000000000000 : ℝ)
  | 11 => (-3472902797 / 25000000000 : ℝ)
  | 12 => (-36544860573 / 250000000000 : ℝ)
  | 13 => (-19195146971 / 125000000000 : ℝ)
  | 14 => (-161062568539 / 1000000000000 : ℝ)
  | 15 => (-33736977283 / 200000000000 : ℝ)
  | 16 => (-176429404839 / 1000000000000 : ℝ)
  | 17 => (-184297408939 / 1000000000000 : ℝ)
  | 18 => (-192290193583 / 1000000000000 : ℝ)
  | 19 => (-200409063431 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch043Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-946049463 / 15625000000 : ℝ)
  | 1 => (-66484229601 / 1000000000000 : ℝ)
  | 2 => (-72525350097 / 1000000000000 : ℝ)
  | 3 => (-1573433449 / 20000000000 : ℝ)
  | 4 => (-21231087737 / 250000000000 : ℝ)
  | 5 => (-9128454889 / 100000000000 : ℝ)
  | 6 => (-24438359659 / 250000000000 : ℝ)
  | 7 => (-104332201661 / 1000000000000 : ℝ)
  | 8 => (-55511014301 / 500000000000 : ℝ)
  | 9 => (-117824119311 / 1000000000000 : ℝ)
  | 10 => (-124739682907 / 1000000000000 : ℝ)
  | 11 => (-32942484457 / 250000000000 : ℝ)
  | 12 => (-138916111879 / 1000000000000 : ℝ)
  | 13 => (-146179442291 / 1000000000000 : ℝ)
  | 14 => (-153561175767 / 1000000000000 : ℝ)
  | 15 => (-80531284269 / 500000000000 : ℝ)
  | 16 => (-84342443207 / 500000000000 : ℝ)
  | 17 => (-88214702419 / 500000000000 : ℝ)
  | 18 => (-92148704469 / 500000000000 : ℝ)
  | 19 => (-96145096791 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch043Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((860 : ℝ) + (j.val : ℝ)) / 1600)
      (((860 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch043Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch043Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((860 : ℝ) + (j.val : ℝ)) / 1600)
    (((860 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch043Neg100WeightLower j.val) (hpThetaShiftOneBatch043Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch043Neg100WeightLower, hpThetaShiftOneBatch043Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch043Neg100_integral_bounds :
    (-111004246349 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-12896060563 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (860 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch043Lower hpThetaJensenCellsBatch043Upper
    hpThetaShiftOneBatch043Neg100WeightLower hpThetaShiftOneBatch043Neg100WeightUpper hpThetaJensenCellsBatch043_bounds hpThetaShiftOneBatch043Neg100_weight_bounds
  have hl : (-111004246349 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch043Lower j * hpThetaShiftOneBatch043Neg100WeightLower j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftOneBatch043Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftOneBatch043Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch043Lower j * hpThetaShiftOneBatch043Neg100WeightUpper j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftOneBatch043Neg100WeightUpper j) / 1600) ≤ (-12896060563 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftOneBatch043Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (860 : ℝ) / 1600 = 43 / 80 by norm_num,
    show ((860 : ℝ) + 20) / 1600 = (43 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch043Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (9816929923 / 50000000000 : ℝ)
  | 1 => (49385015961 / 250000000000 : ℝ)
  | 2 => (198736826361 / 1000000000000 : ℝ)
  | 3 => (99964355469 / 500000000000 : ℝ)
  | 4 => (100557770297 / 500000000000 : ℝ)
  | 5 => (12643571027 / 62500000000 : ℝ)
  | 6 => (203473317623 / 1000000000000 : ℝ)
  | 7 => (102321950697 / 500000000000 : ℝ)
  | 8 => (205808703017 / 1000000000000 : ℝ)
  | 9 => (51741883949 / 250000000000 : ℝ)
  | 10 => (208120211051 / 1000000000000 : ℝ)
  | 11 => (209266538111 / 1000000000000 : ℝ)
  | 12 => (105203162147 / 500000000000 : ℝ)
  | 13 => (105769687451 / 500000000000 : ℝ)
  | 14 => (531663733 / 2500000000 : ℝ)
  | 15 => (21378448041 / 100000000000 : ℝ)
  | 16 => (53724033923 / 250000000000 : ℝ)
  | 17 => (27000032017 / 125000000000 : ℝ)
  | 18 => (108548318373 / 500000000000 : ℝ)
  | 19 => (8727402817 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch043Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (39508012769 / 200000000000 : ℝ)
  | 1 => (99368413181 / 500000000000 : ℝ)
  | 2 => (199928710939 / 1000000000000 : ℝ)
  | 3 => (40223108119 / 200000000000 : ℝ)
  | 4 => (202297136433 / 1000000000000 : ℝ)
  | 5 => (25434164703 / 125000000000 : ℝ)
  | 6 => (40928780279 / 200000000000 : ℝ)
  | 7 => (102904351509 / 500000000000 : ℝ)
  | 8 => (206967535797 / 1000000000000 : ℝ)
  | 9 => (52030052763 / 250000000000 : ℝ)
  | 10 => (1634894829 / 7812500000 : ℝ)
  | 11 => (42081264859 / 200000000000 : ℝ)
  | 12 => (211539374903 / 1000000000000 : ℝ)
  | 13 => (212665493201 / 1000000000000 : ℝ)
  | 14 => (213784480411 / 1000000000000 : ℝ)
  | 15 => (214896135693 / 1000000000000 : ℝ)
  | 16 => (216000256137 / 1000000000000 : ℝ)
  | 17 => (217096636747 / 1000000000000 : ℝ)
  | 18 => (109092535213 / 500000000000 : ℝ)
  | 19 => (1713010531 / 7812500000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch043Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((860 : ℝ) + (j.val : ℝ)) / 1600)
      (((860 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch043Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch043Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((860 : ℝ) + (j.val : ℝ)) / 1600)
    (((860 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch043Neg65WeightLower j.val) (hpThetaShiftOneBatch043Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch043Neg65WeightLower, hpThetaShiftOneBatch043Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch043Neg65_integral_bounds :
    (176319445049 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (180397246873 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (860 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch043Lower hpThetaJensenCellsBatch043Upper
    hpThetaShiftOneBatch043Neg65WeightLower hpThetaShiftOneBatch043Neg65WeightUpper hpThetaJensenCellsBatch043_bounds hpThetaShiftOneBatch043Neg65_weight_bounds
  have hl : (176319445049 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch043Lower j * hpThetaShiftOneBatch043Neg65WeightLower j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftOneBatch043Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftOneBatch043Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch043Lower j * hpThetaShiftOneBatch043Neg65WeightUpper j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftOneBatch043Neg65WeightUpper j) / 1600) ≤ (180397246873 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftOneBatch043Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (860 : ℝ) / 1600 = 43 / 80 by norm_num,
    show ((860 : ℝ) + 20) / 1600 = (43 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch043Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2237469921 / 250000000000 : ℝ)
  | 1 => (151051087 / 15625000000 : ℝ)
  | 2 => (2597636939 / 250000000000 : ℝ)
  | 3 => (5559862101 / 500000000000 : ℝ)
  | 4 => (11854808643 / 1000000000000 : ℝ)
  | 5 => (3148952647 / 250000000000 : ℝ)
  | 6 => (3335684831 / 250000000000 : ℝ)
  | 7 => (2819120781 / 200000000000 : ℝ)
  | 8 => (14854413157 / 1000000000000 : ℝ)
  | 9 => (1952396959 / 125000000000 : ℝ)
  | 10 => (4097474951 / 250000000000 : ℝ)
  | 11 => (17166593673 / 1000000000000 : ℝ)
  | 12 => (3589853031 / 200000000000 : ℝ)
  | 13 => (18737921883 / 1000000000000 : ℝ)
  | 14 => (9766285623 / 500000000000 : ℝ)
  | 15 => (635413137 / 31250000000 : ℝ)
  | 16 => (21139876187 / 1000000000000 : ℝ)
  | 17 => (5488136323 / 250000000000 : ℝ)
  | 18 => (142320213 / 6250000000 : ℝ)
  | 19 => (943837947 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch043Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (9667269569 / 1000000000000 : ℝ)
  | 1 => (10390547757 / 1000000000000 : ℝ)
  | 2 => (11119724203 / 1000000000000 : ℝ)
  | 3 => (2963702161 / 250000000000 : ℝ)
  | 4 => (12595810589 / 1000000000000 : ℝ)
  | 5 => (533709573 / 40000000000 : ℝ)
  | 6 => (7047801953 / 500000000000 : ℝ)
  | 7 => (7427206579 / 500000000000 : ℝ)
  | 8 => (15619175673 / 1000000000000 : ℝ)
  | 9 => (3277979961 / 200000000000 : ℝ)
  | 10 => (8583296837 / 500000000000 : ℝ)
  | 11 => (4487316289 / 250000000000 : ℝ)
  | 12 => (4684480471 / 250000000000 : ℝ)
  | 13 => (19532571247 / 1000000000000 : ℝ)
  | 14 => (4066644077 / 200000000000 : ℝ)
  | 15 => (5284969047 / 250000000000 : ℝ)
  | 16 => (21952545293 / 1000000000000 : ℝ)
  | 17 => (22771234081 / 1000000000000 : ℝ)
  | 18 => (5898987169 / 250000000000 : ℝ)
  | 19 => (24426694941 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch043Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((860 : ℝ) + (j.val : ℝ)) / 1600)
      (((860 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch043Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch043Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((860 : ℝ) + (j.val : ℝ)) / 1600)
    (((860 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch043Neg40WeightLower j.val) (hpThetaShiftOneBatch043Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch043Neg40WeightLower, hpThetaShiftOneBatch043Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch043Neg40_integral_bounds :
    (13521298471 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (901678441 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (860 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch043Lower hpThetaJensenCellsBatch043Upper
    hpThetaShiftOneBatch043Neg40WeightLower hpThetaShiftOneBatch043Neg40WeightUpper hpThetaJensenCellsBatch043_bounds hpThetaShiftOneBatch043Neg40_weight_bounds
  have hl : (13521298471 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch043Lower j * hpThetaShiftOneBatch043Neg40WeightLower j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftOneBatch043Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftOneBatch043Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch043Lower j * hpThetaShiftOneBatch043Neg40WeightUpper j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftOneBatch043Neg40WeightUpper j) / 1600) ≤ (901678441 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftOneBatch043Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (860 : ℝ) / 1600 = 43 / 80 by norm_num,
    show ((860 : ℝ) + 20) / 1600 = (43 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch043Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-65145858527 / 1000000000000 : ℝ)
  | 1 => (-65375887231 / 1000000000000 : ℝ)
  | 2 => (-32802501321 / 500000000000 : ℝ)
  | 3 => (-1645829811 / 25000000000 : ℝ)
  | 4 => (-6606044427 / 100000000000 : ℝ)
  | 5 => (-8285843217 / 125000000000 : ℝ)
  | 6 => (-66512084407 / 1000000000000 : ℝ)
  | 7 => (-66736447811 / 1000000000000 : ℝ)
  | 8 => (-66959823441 / 1000000000000 : ℝ)
  | 9 => (-67182198751 / 1000000000000 : ℝ)
  | 10 => (-33701780579 / 500000000000 : ℝ)
  | 11 => (-1690597451 / 25000000000 : ℝ)
  | 12 => (-67843196741 / 1000000000000 : ℝ)
  | 13 => (-17015361141 / 250000000000 : ℝ)
  | 14 => (-34139314389 / 500000000000 : ℝ)
  | 15 => (-34247368307 / 500000000000 : ℝ)
  | 16 => (-34354877633 / 500000000000 : ℝ)
  | 17 => (-6892367189 / 100000000000 : ℝ)
  | 18 => (-6913647361 / 100000000000 : ℝ)
  | 19 => (-17337036877 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch043Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8114366101 / 125000000000 : ℝ)
  | 1 => (-32572929263 / 500000000000 : ℝ)
  | 2 => (-6537588723 / 100000000000 : ℝ)
  | 3 => (-65605002641 / 1000000000000 : ℝ)
  | 4 => (-65833192439 / 1000000000000 : ℝ)
  | 5 => (-66060444269 / 1000000000000 : ℝ)
  | 6 => (-13257349147 / 200000000000 : ℝ)
  | 7 => (-33256042203 / 500000000000 : ℝ)
  | 8 => (-6673644781 / 100000000000 : ℝ)
  | 9 => (-836997793 / 12500000000 : ℝ)
  | 10 => (-53745759 / 800000000 : ℝ)
  | 11 => (-67403561157 / 1000000000000 : ℝ)
  | 12 => (-67623898039 / 1000000000000 : ℝ)
  | 13 => (-3392159837 / 50000000000 : ℝ)
  | 14 => (-68061444563 / 1000000000000 : ℝ)
  | 15 => (-68278628777 / 1000000000000 : ℝ)
  | 16 => (-68494736613 / 1000000000000 : ℝ)
  | 17 => (-13741951053 / 200000000000 : ℝ)
  | 18 => (-68923671889 / 1000000000000 : ℝ)
  | 19 => (-69136473609 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch043Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((860 : ℝ) + (j.val : ℝ)) / 1600)
      (((860 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch043Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch043Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((860 : ℝ) + (j.val : ℝ)) / 1600)
    (((860 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch043Neg20WeightLower j.val) (hpThetaShiftOneBatch043Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch043Neg20WeightLower, hpThetaShiftOneBatch043Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch043Neg20_integral_bounds :
    (-5822056393 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-14257769961 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (860 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch043Lower hpThetaJensenCellsBatch043Upper
    hpThetaShiftOneBatch043Neg20WeightLower hpThetaShiftOneBatch043Neg20WeightUpper hpThetaJensenCellsBatch043_bounds hpThetaShiftOneBatch043Neg20_weight_bounds
  have hl : (-5822056393 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch043Lower j * hpThetaShiftOneBatch043Neg20WeightLower j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftOneBatch043Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftOneBatch043Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch043Lower j * hpThetaShiftOneBatch043Neg20WeightUpper j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftOneBatch043Neg20WeightUpper j) / 1600) ≤ (-14257769961 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftOneBatch043Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (860 : ℝ) / 1600 = 43 / 80 by norm_num,
    show ((860 : ℝ) + 20) / 1600 = (43 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch043Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch043Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch043Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch043Neg20_integral_bounds
end HodgeProofHP
