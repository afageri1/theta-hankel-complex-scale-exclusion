/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch061

/-! Exact signed weight and batch integral certificates, batch 61 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch061Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-27274636375457 / 1000000000000 : ℝ)
  | 1 => (-550173943607 / 20000000000 : ℝ)
  | 2 => (-6936103358177 / 250000000000 : ℝ)
  | 3 => (-6995448673107 / 250000000000 : ℝ)
  | 4 => (-7055212640891 / 250000000000 : ℝ)
  | 5 => (-28461590694483 / 1000000000000 : ℝ)
  | 6 => (-1148160991121 / 40000000000 : ℝ)
  | 7 => (-28948162551659 / 1000000000000 : ℝ)
  | 8 => (-14597006898823 / 500000000000 : ℝ)
  | 9 => (-3680198542899 / 125000000000 : ℝ)
  | 10 => (-14845448030307 / 500000000000 : ℝ)
  | 11 => (-29941946867493 / 1000000000000 : ℝ)
  | 12 => (-15097375363421 / 500000000000 : ℝ)
  | 13 => (-30449317647259 / 1000000000000 : ℝ)
  | 14 => (-30705657683093 / 1000000000000 : ℝ)
  | 15 => (-15481890467303 / 500000000000 : ℝ)
  | 16 => (-31223697548131 / 1000000000000 : ℝ)
  | 17 => (-15742708858119 / 500000000000 : ℝ)
  | 18 => (-6349790335579 / 200000000000 : ℝ)
  | 19 => (-4001788714829 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch061Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-13521110751067 / 500000000000 : ℝ)
  | 1 => (-852332386733 / 31250000000 : ℝ)
  | 2 => (-27508697180349 / 1000000000000 : ℝ)
  | 3 => (-27744413432707 / 1000000000000 : ℝ)
  | 4 => (-27981794692427 / 1000000000000 : ℝ)
  | 5 => (-28220850563563 / 1000000000000 : ℝ)
  | 6 => (-14230795347241 / 500000000000 : ℝ)
  | 7 => (-3588003097253 / 125000000000 : ℝ)
  | 8 => (-14474081275829 / 500000000000 : ℝ)
  | 9 => (-5838802759529 / 200000000000 : ℝ)
  | 10 => (-29441588343191 / 1000000000000 : ℝ)
  | 11 => (-29690896060613 / 1000000000000 : ℝ)
  | 12 => (-7485486716873 / 250000000000 : ℝ)
  | 13 => (-30194750726841 / 1000000000000 : ℝ)
  | 14 => (-15224658823629 / 500000000000 : ℝ)
  | 15 => (-7676414420773 / 250000000000 : ℝ)
  | 16 => (-6192756186921 / 200000000000 : ℝ)
  | 17 => (-3122369754813 / 100000000000 : ℝ)
  | 18 => (-31485417716237 / 1000000000000 : ℝ)
  | 19 => (-15874475838947 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch061Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1220 : ℝ) + (j.val : ℝ)) / 1600)
      (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch061Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch061Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1220 : ℝ) + (j.val : ℝ)) / 1600)
    (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch061Neg100WeightLower j.val) (hpThetaShiftOneBatch061Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch061Neg100WeightLower, hpThetaShiftOneBatch061Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch061Neg100_integral_bounds :
    (-37838193381 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-22897210181 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch061Lower hpThetaJensenCellsBatch061Upper
    hpThetaShiftOneBatch061Neg100WeightLower hpThetaShiftOneBatch061Neg100WeightUpper hpThetaJensenCellsBatch061_bounds hpThetaShiftOneBatch061Neg100_weight_bounds
  have hl : (-37838193381 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch061Lower j * hpThetaShiftOneBatch061Neg100WeightLower j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftOneBatch061Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftOneBatch061Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch061Lower j * hpThetaShiftOneBatch061Neg100WeightUpper j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftOneBatch061Neg100WeightUpper j) / 1600) ≤ (-22897210181 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftOneBatch061Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1220 : ℝ) / 1600 = 61 / 80 by norm_num,
    show ((1220 : ℝ) + 20) / 1600 = (61 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch061Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3160280923711 / 1000000000000 : ℝ)
  | 1 => (-399837505773 / 125000000000 : ℝ)
  | 2 => (-3237451764061 / 1000000000000 : ℝ)
  | 3 => (-655307652327 / 200000000000 : ℝ)
  | 4 => (-828990433543 / 250000000000 : ℝ)
  | 5 => (-838931096989 / 250000000000 : ℝ)
  | 6 => (-424478555041 / 125000000000 : ℝ)
  | 7 => (-214767257483 / 62500000000 : ℝ)
  | 8 => (-3477069665733 / 1000000000000 : ℝ)
  | 9 => (-1759105664553 / 500000000000 : ℝ)
  | 10 => (-3559703371833 / 1000000000000 : ℝ)
  | 11 => (-900387016791 / 250000000000 : ℝ)
  | 12 => (-3643747699659 / 1000000000000 : ℝ)
  | 13 => (-3686304565227 / 1000000000000 : ℝ)
  | 14 => (-372922097117 / 100000000000 : ℝ)
  | 15 => (-3772499236223 / 1000000000000 : ℝ)
  | 16 => (-1908070845301 / 500000000000 : ℝ)
  | 17 => (-96503766901 / 25000000000 : ℝ)
  | 18 => (-1952264272917 / 500000000000 : ℝ)
  | 19 => (-1974638832443 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch061Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3122192223279 / 1000000000000 : ℝ)
  | 1 => (-316028092371 / 100000000000 : ℝ)
  | 2 => (-3198700046183 / 1000000000000 : ℝ)
  | 3 => (-161872588203 / 50000000000 : ℝ)
  | 4 => (-1638269130817 / 500000000000 : ℝ)
  | 5 => (-3315961734171 / 1000000000000 : ℝ)
  | 6 => (-671144877591 / 200000000000 : ℝ)
  | 7 => (-3395828440327 / 1000000000000 : ℝ)
  | 8 => (-3436276119727 / 1000000000000 : ℝ)
  | 9 => (-869267416433 / 250000000000 : ℝ)
  | 10 => (-703642265821 / 200000000000 : ℝ)
  | 11 => (-444962921479 / 125000000000 : ℝ)
  | 12 => (-3601548067163 / 1000000000000 : ℝ)
  | 13 => (-1821873849829 / 500000000000 : ℝ)
  | 14 => (-1843152282613 / 500000000000 : ℝ)
  | 15 => (-3729220971169 / 1000000000000 : ℝ)
  | 16 => (-1886249618111 / 500000000000 : ℝ)
  | 17 => (-3816141690601 / 1000000000000 : ℝ)
  | 18 => (-3860150676039 / 1000000000000 : ℝ)
  | 19 => (-3904528545833 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch061Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1220 : ℝ) + (j.val : ℝ)) / 1600)
      (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch061Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch061Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1220 : ℝ) + (j.val : ℝ)) / 1600)
    (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch061Neg65WeightLower j.val) (hpThetaShiftOneBatch061Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch061Neg65WeightLower, hpThetaShiftOneBatch061Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch061Neg65_integral_bounds :
    (-904903667 / 20000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-43662125073 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch061Lower hpThetaJensenCellsBatch061Upper
    hpThetaShiftOneBatch061Neg65WeightLower hpThetaShiftOneBatch061Neg65WeightUpper hpThetaJensenCellsBatch061_bounds hpThetaShiftOneBatch061Neg65_weight_bounds
  have hl : (-904903667 / 20000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch061Lower j * hpThetaShiftOneBatch061Neg65WeightLower j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftOneBatch061Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftOneBatch061Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch061Lower j * hpThetaShiftOneBatch061Neg65WeightUpper j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftOneBatch061Neg65WeightUpper j) / 1600) ≤ (-43662125073 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftOneBatch061Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1220 : ℝ) / 1600 = 61 / 80 by norm_num,
    show ((1220 : ℝ) + 20) / 1600 = (61 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch061Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (104560894401 / 250000000000 : ℝ)
  | 1 => (41770664849 / 100000000000 : ℝ)
  | 2 => (104284216309 / 250000000000 : ℝ)
  | 3 => (6508342063 / 15625000000 : ℝ)
  | 4 => (83179478197 / 200000000000 : ℝ)
  | 5 => (83045404421 / 200000000000 : ℝ)
  | 6 => (12953826353 / 31250000000 : ℝ)
  | 7 => (413783310351 / 1000000000000 : ℝ)
  | 8 => (206504638471 / 500000000000 : ℝ)
  | 9 => (25762499663 / 62500000000 : ℝ)
  | 10 => (411355112749 / 1000000000000 : ℝ)
  | 11 => (51309284827 / 125000000000 : ℝ)
  | 12 => (409557137303 / 1000000000000 : ℝ)
  | 13 => (408603331737 / 1000000000000 : ℝ)
  | 14 => (101903125667 / 250000000000 : ℝ)
  | 15 => (406584288663 / 1000000000000 : ℝ)
  | 16 => (405518326093 / 1000000000000 : ℝ)
  | 17 => (50551781141 / 125000000000 : ℝ)
  | 18 => (100817922431 / 250000000000 : ℝ)
  | 19 => (25130642351 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch061Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (418747986309 / 1000000000000 : ℝ)
  | 1 => (83648715521 / 200000000000 : ℝ)
  | 2 => (417706648491 / 1000000000000 : ℝ)
  | 3 => (417136865237 / 1000000000000 : ℝ)
  | 4 => (416533892033 / 1000000000000 : ℝ)
  | 5 => (207948695493 / 500000000000 : ℝ)
  | 6 => (207613511053 / 500000000000 : ℝ)
  | 7 => (414522443297 / 1000000000000 : ℝ)
  | 8 => (25861456897 / 62500000000 : ℝ)
  | 9 => (413009276943 / 1000000000000 : ℝ)
  | 10 => (412199994609 / 1000000000000 : ℝ)
  | 11 => (1645420451 / 4000000000 : ℝ)
  | 12 => (410474278617 / 1000000000000 : ℝ)
  | 13 => (51194642163 / 125000000000 : ℝ)
  | 14 => (204301665869 / 500000000000 : ℝ)
  | 15 => (407612502669 / 1000000000000 : ℝ)
  | 16 => (50823036083 / 125000000000 : ℝ)
  | 17 => (202759163047 / 500000000000 : ℝ)
  | 18 => (404414249129 / 1000000000000 : ℝ)
  | 19 => (16130867589 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch061Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1220 : ℝ) + (j.val : ℝ)) / 1600)
      (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch061Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch061Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1220 : ℝ) + (j.val : ℝ)) / 1600)
    (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch061Neg40WeightLower j.val) (hpThetaShiftOneBatch061Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch061Neg40WeightLower, hpThetaShiftOneBatch061Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch061Neg40_integral_bounds :
    (129017791 / 25000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (5295738743 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch061Lower hpThetaJensenCellsBatch061Upper
    hpThetaShiftOneBatch061Neg40WeightLower hpThetaShiftOneBatch061Neg40WeightUpper hpThetaJensenCellsBatch061_bounds hpThetaShiftOneBatch061Neg40_weight_bounds
  have hl : (129017791 / 25000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch061Lower j * hpThetaShiftOneBatch061Neg40WeightLower j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftOneBatch061Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftOneBatch061Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch061Lower j * hpThetaShiftOneBatch061Neg40WeightUpper j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftOneBatch061Neg40WeightUpper j) / 1600) ≤ (5295738743 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftOneBatch061Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1220 : ℝ) / 1600 = 61 / 80 by norm_num,
    show ((1220 : ℝ) + 20) / 1600 = (61 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch061Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (10878642693 / 500000000000 : ℝ)
  | 1 => (11396435641 / 500000000000 : ℝ)
  | 2 => (23834368797 / 1000000000000 : ℝ)
  | 3 => (1244089231 / 50000000000 : ℝ)
  | 4 => (12967562663 / 500000000000 : ℝ)
  | 5 => (26994397377 / 1000000000000 : ℝ)
  | 6 => (14029803559 / 500000000000 : ℝ)
  | 7 => (1456538039 / 50000000000 : ℝ)
  | 8 => (30207864477 / 1000000000000 : ℝ)
  | 9 => (31290924207 / 1000000000000 : ℝ)
  | 10 => (16189972923 / 500000000000 : ℝ)
  | 11 => (6694987031 / 200000000000 : ℝ)
  | 12 => (8643974443 / 250000000000 : ℝ)
  | 13 => (7136567843 / 200000000000 : ℝ)
  | 14 => (36795764881 / 1000000000000 : ℝ)
  | 15 => (9478670011 / 250000000000 : ℝ)
  | 16 => (19519794927 / 500000000000 : ℝ)
  | 17 => (40170499337 / 1000000000000 : ℝ)
  | 18 => (8261482679 / 200000000000 : ℝ)
  | 19 => (42450336801 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch061Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (22792871283 / 1000000000000 : ℝ)
  | 1 => (11917184399 / 500000000000 : ℝ)
  | 2 => (24881784621 / 1000000000000 : ℝ)
  | 3 => (25935125327 / 1000000000000 : ℝ)
  | 4 => (13497198689 / 500000000000 : ℝ)
  | 5 => (28059607119 / 1000000000000 : ℝ)
  | 6 => (29130760781 / 1000000000000 : ℝ)
  | 7 => (15103932239 / 500000000000 : ℝ)
  | 8 => (1955682763 / 62500000000 : ℝ)
  | 9 => (32379945847 / 1000000000000 : ℝ)
  | 10 => (8368733789 / 250000000000 : ℝ)
  | 11 => (34575897773 / 1000000000000 : ℝ)
  | 12 => (2230177451 / 62500000000 : ℝ)
  | 13 => (18397882441 / 500000000000 : ℝ)
  | 14 => (7582936009 / 200000000000 : ℝ)
  | 15 => (7807917971 / 200000000000 : ℝ)
  | 16 => (20085249669 / 500000000000 : ℝ)
  | 17 => (10326853349 / 250000000000 : ℝ)
  | 18 => (21225168401 / 500000000000 : ℝ)
  | 19 => (8719854841 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch061Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1220 : ℝ) + (j.val : ℝ)) / 1600)
      (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch061Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch061Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1220 : ℝ) + (j.val : ℝ)) / 1600)
    (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch061Neg20WeightLower j.val) (hpThetaShiftOneBatch061Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch061Neg20WeightLower, hpThetaShiftOneBatch061Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch061Neg20_integral_bounds :
    (196716391 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (416924169 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch061Lower hpThetaJensenCellsBatch061Upper
    hpThetaShiftOneBatch061Neg20WeightLower hpThetaShiftOneBatch061Neg20WeightUpper hpThetaJensenCellsBatch061_bounds hpThetaShiftOneBatch061Neg20_weight_bounds
  have hl : (196716391 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch061Lower j * hpThetaShiftOneBatch061Neg20WeightLower j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftOneBatch061Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftOneBatch061Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch061Lower j * hpThetaShiftOneBatch061Neg20WeightUpper j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftOneBatch061Neg20WeightUpper j) / 1600) ≤ (416924169 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftOneBatch061Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1220 : ℝ) / 1600 = 61 / 80 by norm_num,
    show ((1220 : ℝ) + 20) / 1600 = (61 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch061Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch061Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch061Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch061Neg20_integral_bounds
end HodgeProofHP
