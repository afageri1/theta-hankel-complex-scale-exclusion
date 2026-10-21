/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch007

/-! Exact signed weight and batch integral certificates, batch 7 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch007Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (618206109 / 250000000000 : ℝ)
  | 1 => (498032351 / 200000000000 : ℝ)
  | 2 => (1253575107 / 500000000000 : ℝ)
  | 3 => (2523781659 / 1000000000000 : ℝ)
  | 4 => (508009589 / 200000000000 : ℝ)
  | 5 => (511188187 / 200000000000 : ℝ)
  | 6 => (2571452501 / 1000000000000 : ℝ)
  | 7 => (40415227 / 15625000000 : ℝ)
  | 8 => (2601298911 / 1000000000000 : ℝ)
  | 9 => (2615617559 / 1000000000000 : ℝ)
  | 10 => (657380599 / 250000000000 : ℝ)
  | 11 => (2643005363 / 1000000000000 : ℝ)
  | 12 => (166003651 / 62500000000 : ℝ)
  | 13 => (667168383 / 250000000000 : ℝ)
  | 14 => (2680842707 / 1000000000000 : ℝ)
  | 15 => (1346278979 / 500000000000 : ℝ)
  | 16 => (1351905663 / 500000000000 : ℝ)
  | 17 => (2714594873 / 1000000000000 : ℝ)
  | 18 => (2724900689 / 1000000000000 : ℝ)
  | 19 => (273472089 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch007Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (622540439 / 250000000000 : ℝ)
  | 1 => (501430043 / 200000000000 : ℝ)
  | 2 => (126189083 / 50000000000 : ℝ)
  | 3 => (1270023973 / 500000000000 : ℝ)
  | 4 => (319492617 / 125000000000 : ℝ)
  | 5 => (1285726251 / 500000000000 : ℝ)
  | 6 => (2586574529 / 1000000000000 : ℝ)
  | 7 => (81290591 / 31250000000 : ℝ)
  | 8 => (65390439 / 25000000000 : ℝ)
  | 9 => (2629522397 / 1000000000000 : ℝ)
  | 10 => (660751341 / 250000000000 : ℝ)
  | 11 => (2656058417 / 1000000000000 : ℝ)
  | 12 => (2668673533 / 1000000000000 : ℝ)
  | 13 => (670210677 / 250000000000 : ℝ)
  | 14 => (2692557959 / 1000000000000 : ℝ)
  | 15 => (2703811327 / 1000000000000 : ℝ)
  | 16 => (1357297437 / 500000000000 : ℝ)
  | 17 => (272490069 / 100000000000 : ℝ)
  | 18 => (2734720891 / 1000000000000 : ℝ)
  | 19 => (137202381 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch007Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((140 : ℝ) + (j.val : ℝ)) / 1600)
      (((140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch007Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch007Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((140 : ℝ) + (j.val : ℝ)) / 1600)
    (((140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch007Neg100WeightLower j.val) (hpThetaShiftOneBatch007Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch007Neg100WeightLower, hpThetaShiftOneBatch007Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch007Neg100_integral_bounds :
    (26762627637 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (27199149789 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch007Lower hpThetaJensenCellsBatch007Upper
    hpThetaShiftOneBatch007Neg100WeightLower hpThetaShiftOneBatch007Neg100WeightUpper hpThetaJensenCellsBatch007_bounds hpThetaShiftOneBatch007Neg100_weight_bounds
  have hl : (26762627637 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch007Lower j * hpThetaShiftOneBatch007Neg100WeightLower j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftOneBatch007Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftOneBatch007Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch007Lower j * hpThetaShiftOneBatch007Neg100WeightUpper j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftOneBatch007Neg100WeightUpper j) / 1600) ≤ (27199149789 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftOneBatch007Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (140 : ℝ) / 1600 = 7 / 80 by norm_num,
    show ((140 : ℝ) + 20) / 1600 = (7 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch007Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2922422151 / 1000000000000 : ℝ)
  | 1 => (2951831717 / 1000000000000 : ℝ)
  | 2 => (2981113331 / 1000000000000 : ℝ)
  | 3 => (3010260643 / 1000000000000 : ℝ)
  | 4 => (1519633641 / 500000000000 : ℝ)
  | 5 => (191757929 / 62500000000 : ℝ)
  | 6 => (3096832989 / 1000000000000 : ℝ)
  | 7 => (3125379241 / 1000000000000 : ℝ)
  | 8 => (3153759193 / 1000000000000 : ℝ)
  | 9 => (3181966401 / 1000000000000 : ℝ)
  | 10 => (320999441 / 100000000000 : ℝ)
  | 11 => (202364797 / 62500000000 : ℝ)
  | 12 => (3265486949 / 1000000000000 : ℝ)
  | 13 => (3292938509 / 1000000000000 : ℝ)
  | 14 => (3320184931 / 1000000000000 : ℝ)
  | 15 => (418402463 / 125000000000 : ℝ)
  | 16 => (843509077 / 250000000000 : ℝ)
  | 17 => (3400628213 / 1000000000000 : ℝ)
  | 18 => (3426988883 / 1000000000000 : ℝ)
  | 19 => (3453111771 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch007Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1475915859 / 500000000000 : ℝ)
  | 1 => (745278333 / 250000000000 : ℝ)
  | 2 => (752565161 / 250000000000 : ℝ)
  | 3 => (3039267283 / 1000000000000 : ℝ)
  | 4 => (613625373 / 200000000000 : ℝ)
  | 5 => (309683299 / 100000000000 : ℝ)
  | 6 => (1562689621 / 500000000000 : ℝ)
  | 7 => (1576879597 / 500000000000 : ℝ)
  | 8 => (1590983201 / 500000000000 : ℝ)
  | 9 => (3209994411 / 1000000000000 : ℝ)
  | 10 => (3237836753 / 1000000000000 : ℝ)
  | 11 => (65309739 / 20000000000 : ℝ)
  | 12 => (329293851 / 100000000000 : ℝ)
  | 13 => (830046233 / 250000000000 : ℝ)
  | 14 => (669443941 / 200000000000 : ℝ)
  | 15 => (3374036309 / 1000000000000 : ℝ)
  | 16 => (1700314107 / 500000000000 : ℝ)
  | 17 => (856747221 / 250000000000 : ℝ)
  | 18 => (863277943 / 250000000000 : ℝ)
  | 19 => (434873791 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch007Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((140 : ℝ) + (j.val : ℝ)) / 1600)
      (((140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch007Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch007Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((140 : ℝ) + (j.val : ℝ)) / 1600)
    (((140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch007Neg65WeightLower j.val) (hpThetaShiftOneBatch007Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch007Neg65WeightLower, hpThetaShiftOneBatch007Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch007Neg65_integral_bounds :
    (1633254229 / 25000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (13325778643 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch007Lower hpThetaJensenCellsBatch007Upper
    hpThetaShiftOneBatch007Neg65WeightLower hpThetaShiftOneBatch007Neg65WeightUpper hpThetaJensenCellsBatch007_bounds hpThetaShiftOneBatch007Neg65_weight_bounds
  have hl : (1633254229 / 25000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch007Lower j * hpThetaShiftOneBatch007Neg65WeightLower j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftOneBatch007Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftOneBatch007Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch007Lower j * hpThetaShiftOneBatch007Neg65WeightUpper j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftOneBatch007Neg65WeightUpper j) / 1600) ≤ (13325778643 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftOneBatch007Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (140 : ℝ) / 1600 = 7 / 80 by norm_num,
    show ((140 : ℝ) + 20) / 1600 = (7 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch007Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3259764273 / 1000000000000 : ℝ)
  | 1 => (3298494303 / 1000000000000 : ℝ)
  | 2 => (667455761 / 200000000000 : ℝ)
  | 3 => (3376113391 / 1000000000000 : ℝ)
  | 4 => (853748413 / 250000000000 : ℝ)
  | 5 => (3453915161 / 1000000000000 : ℝ)
  | 6 => (349287347 / 100000000000 : ℝ)
  | 7 => (3531864113 / 1000000000000 : ℝ)
  | 8 => (714176521 / 200000000000 : ℝ)
  | 9 => (3609924441 / 1000000000000 : ℝ)
  | 10 => (1824492549 / 500000000000 : ℝ)
  | 11 => (737612007 / 200000000000 : ℝ)
  | 12 => (1863572347 / 500000000000 : ℝ)
  | 13 => (29423707 / 7812500000 : ℝ)
  | 14 => (237832803 / 62500000000 : ℝ)
  | 15 => (3844411137 / 1000000000000 : ℝ)
  | 16 => (776697747 / 200000000000 : ℝ)
  | 17 => (980638249 / 250000000000 : ℝ)
  | 18 => (3961599257 / 1000000000000 : ℝ)
  | 19 => (4000622839 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch007Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (103077947 / 31250000000 : ℝ)
  | 1 => (1668639403 / 500000000000 : ℝ)
  | 2 => (211007087 / 62500000000 : ℝ)
  | 3 => (3414993653 / 1000000000000 : ℝ)
  | 4 => (1726957581 / 500000000000 : ℝ)
  | 5 => (3492873471 / 1000000000000 : ℝ)
  | 6 => (1765932057 / 500000000000 : ℝ)
  | 7 => (1785441303 / 500000000000 : ℝ)
  | 8 => (1804962221 / 500000000000 : ℝ)
  | 9 => (3648985099 / 1000000000000 : ℝ)
  | 10 => (922015009 / 250000000000 : ℝ)
  | 11 => (745428939 / 200000000000 : ℝ)
  | 12 => (3766234497 / 1000000000000 : ℝ)
  | 13 => (3805324849 / 1000000000000 : ℝ)
  | 14 => (1922205569 / 500000000000 : ℝ)
  | 15 => (121359023 / 31250000000 : ℝ)
  | 16 => (3922552997 / 1000000000000 : ℝ)
  | 17 => (1980799629 / 500000000000 : ℝ)
  | 18 => (100015571 / 25000000000 : ℝ)
  | 19 => (504952381 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch007Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((140 : ℝ) + (j.val : ℝ)) / 1600)
      (((140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch007Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch007Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((140 : ℝ) + (j.val : ℝ)) / 1600)
    (((140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch007Neg40WeightLower j.val) (hpThetaShiftOneBatch007Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch007Neg40WeightLower, hpThetaShiftOneBatch007Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch007Neg40_integral_bounds :
    (74261042811 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (75889463957 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch007Lower hpThetaJensenCellsBatch007Upper
    hpThetaShiftOneBatch007Neg40WeightLower hpThetaShiftOneBatch007Neg40WeightUpper hpThetaJensenCellsBatch007_bounds hpThetaShiftOneBatch007Neg40_weight_bounds
  have hl : (74261042811 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch007Lower j * hpThetaShiftOneBatch007Neg40WeightLower j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftOneBatch007Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftOneBatch007Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch007Lower j * hpThetaShiftOneBatch007Neg40WeightUpper j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftOneBatch007Neg40WeightUpper j) / 1600) ≤ (75889463957 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftOneBatch007Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (140 : ℝ) / 1600 = 7 / 80 by norm_num,
    show ((140 : ℝ) + 20) / 1600 = (7 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch007Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (353950577 / 100000000000 : ℝ)
  | 1 => (3586119259 / 1000000000000 : ℝ)
  | 2 => (29063587 / 8000000000 : ℝ)
  | 3 => (3679990727 / 1000000000000 : ℝ)
  | 4 => (3727243911 / 1000000000000 : ℝ)
  | 5 => (943676377 / 250000000000 : ℝ)
  | 6 => (3822373087 / 1000000000000 : ℝ)
  | 7 => (19351221 / 5000000000 : ℝ)
  | 8 => (979579097 / 250000000000 : ℝ)
  | 9 => (495823397 / 125000000000 : ℝ)
  | 10 => (2007527039 / 500000000000 : ℝ)
  | 11 => (4063714591 / 1000000000000 : ℝ)
  | 12 => (2056283101 / 500000000000 : ℝ)
  | 13 => (2080803191 / 500000000000 : ℝ)
  | 14 => (1052708147 / 250000000000 : ℝ)
  | 15 => (4260242267 / 1000000000000 : ℝ)
  | 16 => (4309832849 / 1000000000000 : ℝ)
  | 17 => (4359601753 / 1000000000000 : ℝ)
  | 18 => (275596649 / 62500000000 : ℝ)
  | 19 => (4459664133 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch007Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (179305963 / 50000000000 : ℝ)
  | 1 => (454118547 / 125000000000 : ℝ)
  | 2 => (459998841 / 125000000000 : ℝ)
  | 3 => (465905489 / 125000000000 : ℝ)
  | 4 => (3774705509 / 1000000000000 : ℝ)
  | 5 => (119449159 / 31250000000 : ℝ)
  | 6 => (3870244201 / 1000000000000 : ℝ)
  | 7 => (3918316389 / 1000000000000 : ℝ)
  | 8 => (3966587177 / 1000000000000 : ℝ)
  | 9 => (4015054079 / 1000000000000 : ℝ)
  | 10 => (126991081 / 31250000000 : ℝ)
  | 11 => (4112566203 / 1000000000000 : ℝ)
  | 12 => (4161606383 / 1000000000000 : ℝ)
  | 13 => (4210832589 / 1000000000000 : ℝ)
  | 14 => (1065060567 / 250000000000 : ℝ)
  | 15 => (86196657 / 20000000000 : ℝ)
  | 16 => (2179800877 / 500000000000 : ℝ)
  | 17 => (881909277 / 200000000000 : ℝ)
  | 18 => (2229832067 / 500000000000 : ℝ)
  | 19 => (4509952381 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch007Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((140 : ℝ) + (j.val : ℝ)) / 1600)
      (((140 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch007Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch007Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((140 : ℝ) + (j.val : ℝ)) / 1600)
    (((140 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch007Neg20WeightLower j.val) (hpThetaShiftOneBatch007Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch007Neg20WeightLower, hpThetaShiftOneBatch007Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch007Neg20_integral_bounds :
    (81710316833 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (7 / 80 : ℝ) ((7 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (20904557241 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (140 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch007Lower hpThetaJensenCellsBatch007Upper
    hpThetaShiftOneBatch007Neg20WeightLower hpThetaShiftOneBatch007Neg20WeightUpper hpThetaJensenCellsBatch007_bounds hpThetaShiftOneBatch007Neg20_weight_bounds
  have hl : (81710316833 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch007Lower j * hpThetaShiftOneBatch007Neg20WeightLower j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftOneBatch007Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftOneBatch007Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch007Lower j * hpThetaShiftOneBatch007Neg20WeightUpper j)
        (hpThetaJensenCellsBatch007Upper j * hpThetaShiftOneBatch007Neg20WeightUpper j) / 1600) ≤ (20904557241 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch007Lower, hpThetaJensenCellsBatch007Upper,
      hpThetaShiftOneBatch007Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (140 : ℝ) / 1600 = 7 / 80 by norm_num,
    show ((140 : ℝ) + 20) / 1600 = (7 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch007Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch007Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch007Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch007Neg20_integral_bounds
end HodgeProofHP
