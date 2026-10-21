/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch046

/-! Exact signed weight and batch integral certificates, batch 46 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch046Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-329669780053 / 500000000000 : ℝ)
  | 1 => (-134814013307 / 200000000000 : ℝ)
  | 2 => (-688992815667 / 1000000000000 : ℝ)
  | 3 => (-140821919839 / 200000000000 : ℝ)
  | 4 => (-179855555309 / 250000000000 : ℝ)
  | 5 => (-183733124597 / 250000000000 : ℝ)
  | 6 => (-187660564949 / 250000000000 : ℝ)
  | 7 => (-47909584201 / 62500000000 : ℝ)
  | 8 => (-782667615079 / 1000000000000 : ℝ)
  | 9 => (-399493465279 / 500000000000 : ℝ)
  | 10 => (-6524105389 / 8000000000 : ℝ)
  | 11 => (-416124118563 / 500000000000 : ℝ)
  | 12 => (-424597013419 / 500000000000 : ℝ)
  | 13 => (-866352461537 / 1000000000000 : ℝ)
  | 14 => (-176745094613 / 200000000000 : ℝ)
  | 15 => (-450657503197 / 500000000000 : ℝ)
  | 16 => (-229780754923 / 250000000000 : ℝ)
  | 17 => (-937151484391 / 1000000000000 : ℝ)
  | 18 => (-3821609541 / 4000000000 : ℝ)
  | 19 => (-38955108817 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch046Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-644799517041 / 1000000000000 : ℝ)
  | 1 => (-131867912021 / 200000000000 : ℝ)
  | 2 => (-337035033267 / 500000000000 : ℝ)
  | 3 => (-344496407833 / 500000000000 : ℝ)
  | 4 => (-352054799597 / 500000000000 : ℝ)
  | 5 => (-143884444247 / 200000000000 : ℝ)
  | 6 => (-734932498387 / 1000000000000 : ℝ)
  | 7 => (-150128451959 / 200000000000 : ℝ)
  | 8 => (-153310669443 / 200000000000 : ℝ)
  | 9 => (-391333807539 / 500000000000 : ℝ)
  | 10 => (-798986930557 / 1000000000000 : ℝ)
  | 11 => (-101939146703 / 125000000000 : ℝ)
  | 12 => (-6657985897 / 8000000000 : ℝ)
  | 13 => (-849194026837 / 1000000000000 : ℝ)
  | 14 => (-27073514423 / 31250000000 : ℝ)
  | 15 => (-110465684133 / 125000000000 : ℝ)
  | 16 => (-901315006393 / 1000000000000 : ℝ)
  | 17 => (-919123019691 / 1000000000000 : ℝ)
  | 18 => (-93715148439 / 100000000000 : ℝ)
  | 19 => (-955402385249 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch046Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((920 : ℝ) + (j.val : ℝ)) / 1600)
      (((920 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch046Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch046Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((920 : ℝ) + (j.val : ℝ)) / 1600)
    (((920 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch046Neg100WeightLower j.val) (hpThetaShiftOneBatch046Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch046Neg100WeightLower, hpThetaShiftOneBatch046Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch046Neg100_integral_bounds :
    (-5068472863 / 12500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-195025866483 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (920 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch046Lower hpThetaJensenCellsBatch046Upper
    hpThetaShiftOneBatch046Neg100WeightLower hpThetaShiftOneBatch046Neg100WeightUpper hpThetaJensenCellsBatch046_bounds hpThetaShiftOneBatch046Neg100_weight_bounds
  have hl : (-5068472863 / 12500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch046Lower j * hpThetaShiftOneBatch046Neg100WeightLower j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftOneBatch046Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftOneBatch046Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch046Lower j * hpThetaShiftOneBatch046Neg100WeightUpper j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftOneBatch046Neg100WeightUpper j) / 1600) ≤ (-195025866483 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftOneBatch046Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (920 : ℝ) / 1600 = 46 / 80 by norm_num,
    show ((920 : ℝ) + 20) / 1600 = (46 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch046Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (126555580143 / 500000000000 : ℝ)
  | 1 => (63412242283 / 250000000000 : ℝ)
  | 2 => (63541935847 / 250000000000 : ℝ)
  | 3 => (127333584823 / 500000000000 : ℝ)
  | 4 => (7973341617 / 31250000000 : ℝ)
  | 5 => (63901677687 / 250000000000 : ℝ)
  | 6 => (128023092471 / 500000000000 : ℝ)
  | 7 => (256465029807 / 1000000000000 : ℝ)
  | 8 => (256862918007 / 1000000000000 : ℝ)
  | 9 => (257239519371 / 1000000000000 : ℝ)
  | 10 => (128797250441 / 500000000000 : ℝ)
  | 11 => (64481881663 / 250000000000 : ℝ)
  | 12 => (51647651583 / 200000000000 : ℝ)
  | 13 => (258526353003 / 1000000000000 : ℝ)
  | 14 => (129395733667 / 500000000000 : ℝ)
  | 15 => (64758313349 / 250000000000 : ℝ)
  | 16 => (10370054429 / 40000000000 : ℝ)
  | 17 => (129722717947 / 500000000000 : ℝ)
  | 18 => (4056486289 / 15625000000 : ℝ)
  | 19 => (64940015281 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch046Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (253648969133 / 1000000000000 : ℝ)
  | 1 => (254167743389 / 1000000000000 : ℝ)
  | 2 => (254667169647 / 1000000000000 : ℝ)
  | 3 => (51029386349 / 200000000000 : ℝ)
  | 4 => (255606710749 / 1000000000000 : ℝ)
  | 5 => (256046184943 / 1000000000000 : ℝ)
  | 6 => (16029064363 / 62500000000 : ℝ)
  | 7 => (32107864751 / 125000000000 : ℝ)
  | 8 => (64309879843 / 250000000000 : ℝ)
  | 9 => (257594500883 / 1000000000000 : ℝ)
  | 10 => (257927526653 / 1000000000000 : ℝ)
  | 11 => (64559564479 / 250000000000 : ℝ)
  | 12 => (64631588251 / 250000000000 : ℝ)
  | 13 => (51758293467 / 200000000000 : ℝ)
  | 14 => (259033253397 / 1000000000000 : ℝ)
  | 15 => (129625680363 / 500000000000 : ℝ)
  | 16 => (51889087179 / 200000000000 : ℝ)
  | 17 => (259615122497 / 1000000000000 : ℝ)
  | 18 => (2078080489 / 8000000000 : ℝ)
  | 19 => (64969972339 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch046Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((920 : ℝ) + (j.val : ℝ)) / 1600)
      (((920 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch046Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch046Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((920 : ℝ) + (j.val : ℝ)) / 1600)
    (((920 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch046Neg65WeightLower j.val) (hpThetaShiftOneBatch046Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch046Neg65WeightLower, hpThetaShiftOneBatch046Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch046Neg65_integral_bounds :
    (7938451949 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (32381139769 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (920 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch046Lower hpThetaJensenCellsBatch046Upper
    hpThetaShiftOneBatch046Neg65WeightLower hpThetaShiftOneBatch046Neg65WeightUpper hpThetaJensenCellsBatch046_bounds hpThetaShiftOneBatch046Neg65_weight_bounds
  have hl : (7938451949 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch046Lower j * hpThetaShiftOneBatch046Neg65WeightLower j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftOneBatch046Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftOneBatch046Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch046Lower j * hpThetaShiftOneBatch046Neg65WeightUpper j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftOneBatch046Neg65WeightUpper j) / 1600) ≤ (32381139769 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftOneBatch046Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (920 : ℝ) / 1600 = 46 / 80 by norm_num,
    show ((920 : ℝ) + 20) / 1600 = (46 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch046Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1957338649 / 31250000000 : ℝ)
  | 1 => (15928589391 / 250000000000 : ℝ)
  | 2 => (32399942913 / 500000000000 : ℝ)
  | 3 => (65891413657 / 1000000000000 : ℝ)
  | 4 => (66988932773 / 1000000000000 : ℝ)
  | 5 => (34046217253 / 500000000000 : ℝ)
  | 6 => (13840381959 / 200000000000 : ℝ)
  | 7 => (70317349187 / 1000000000000 : ℝ)
  | 8 => (35719371417 / 500000000000 : ℝ)
  | 9 => (72566080487 / 1000000000000 : ℝ)
  | 10 => (36849675747 / 500000000000 : ℝ)
  | 11 => (93548181 / 1250000000 : ℝ)
  | 12 => (37991824469 / 500000000000 : ℝ)
  | 13 => (77134652031 / 1000000000000 : ℝ)
  | 14 => (9786442723 / 125000000000 : ℝ)
  | 15 => (39727152743 / 500000000000 : ℝ)
  | 16 => (20155732501 / 250000000000 : ℝ)
  | 17 => (81797401777 / 1000000000000 : ℝ)
  | 18 => (4148885341 / 50000000000 : ℝ)
  | 19 => (84163830713 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch046Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (12742871513 / 200000000000 : ℝ)
  | 1 => (64799885827 / 1000000000000 : ℝ)
  | 2 => (32945706829 / 500000000000 : ℝ)
  | 3 => (33494466387 / 500000000000 : ℝ)
  | 4 => (68092434507 / 1000000000000 : ℝ)
  | 5 => (17300477449 / 250000000000 : ℝ)
  | 6 => (17579337297 / 250000000000 : ℝ)
  | 7 => (14287748567 / 200000000000 : ℝ)
  | 8 => (9070760061 / 125000000000 : ℝ)
  | 9 => (14739870299 / 200000000000 : ℝ)
  | 10 => (74838544801 / 1000000000000 : ℝ)
  | 11 => (75983648939 / 1000000000000 : ℝ)
  | 12 => (602614469 / 7812500000 : ℝ)
  | 13 => (15658308357 / 200000000000 : ℝ)
  | 14 => (79454305487 / 1000000000000 : ℝ)
  | 15 => (16124586001 / 200000000000 : ℝ)
  | 16 => (40898700889 / 500000000000 : ℝ)
  | 17 => (82977706821 / 1000000000000 : ℝ)
  | 18 => (42081915357 / 500000000000 : ℝ)
  | 19 => (42677879301 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch046Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((920 : ℝ) + (j.val : ℝ)) / 1600)
      (((920 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch046Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch046Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((920 : ℝ) + (j.val : ℝ)) / 1600)
    (((920 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch046Neg40WeightLower j.val) (hpThetaShiftOneBatch046Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch046Neg40WeightLower, hpThetaShiftOneBatch046Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch046Neg40_integral_bounds :
    (9005615169 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (9314010103 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (920 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch046Lower hpThetaJensenCellsBatch046Upper
    hpThetaShiftOneBatch046Neg40WeightLower hpThetaShiftOneBatch046Neg40WeightUpper hpThetaJensenCellsBatch046_bounds hpThetaShiftOneBatch046Neg40_weight_bounds
  have hl : (9005615169 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch046Lower j * hpThetaShiftOneBatch046Neg40WeightLower j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftOneBatch046Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftOneBatch046Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch046Lower j * hpThetaShiftOneBatch046Neg40WeightUpper j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftOneBatch046Neg40WeightUpper j) / 1600) ≤ (9314010103 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftOneBatch046Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (920 : ℝ) / 1600 = 46 / 80 by norm_num,
    show ((920 : ℝ) + 20) / 1600 = (46 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch046Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-38445778959 / 500000000000 : ℝ)
  | 1 => (-77043739129 / 1000000000000 : ℝ)
  | 2 => (-19298551181 / 250000000000 : ℝ)
  | 3 => (-77342940331 / 1000000000000 : ℝ)
  | 4 => (-1549798631 / 20000000000 : ℝ)
  | 5 => (-77635163949 / 1000000000000 : ℝ)
  | 6 => (-77778623071 / 1000000000000 : ℝ)
  | 7 => (-38960147213 / 500000000000 : ℝ)
  | 8 => (-78060163499 / 1000000000000 : ℝ)
  | 9 => (-39099107873 / 500000000000 : ℝ)
  | 10 => (-4895902287 / 62500000000 : ℝ)
  | 11 => (-78468811437 / 1000000000000 : ℝ)
  | 12 => (-39300662827 / 500000000000 : ℝ)
  | 13 => (-15746392917 / 200000000000 : ℝ)
  | 14 => (-78860713547 / 1000000000000 : ℝ)
  | 15 => (-78987557831 / 1000000000000 : ℝ)
  | 16 => (-79112482697 / 1000000000000 : ℝ)
  | 17 => (-79235473383 / 1000000000000 : ℝ)
  | 18 => (-79356515097 / 1000000000000 : ℝ)
  | 19 => (-39737796511 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch046Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-76737675433 / 1000000000000 : ℝ)
  | 1 => (-76891557917 / 1000000000000 : ℝ)
  | 2 => (-9630467391 / 125000000000 : ℝ)
  | 3 => (-77194204723 / 1000000000000 : ℝ)
  | 4 => (-7734294033 / 100000000000 : ℝ)
  | 5 => (-77489931549 / 1000000000000 : ℝ)
  | 6 => (-19408790987 / 250000000000 : ℝ)
  | 7 => (-7777862307 / 100000000000 : ℝ)
  | 8 => (-3116811777 / 40000000000 : ℝ)
  | 9 => (-39030081749 / 500000000000 : ℝ)
  | 10 => (-15639643149 / 200000000000 : ℝ)
  | 11 => (-78334436591 / 1000000000000 : ℝ)
  | 12 => (-19617202859 / 250000000000 : ℝ)
  | 13 => (-78601325653 / 1000000000000 : ℝ)
  | 14 => (-9841495573 / 125000000000 : ℝ)
  | 15 => (-39430356773 / 500000000000 : ℝ)
  | 16 => (-7898755783 / 100000000000 : ℝ)
  | 17 => (-9889060337 / 125000000000 : ℝ)
  | 18 => (-39617736691 / 500000000000 : ℝ)
  | 19 => (-9919564387 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch046Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((920 : ℝ) + (j.val : ℝ)) / 1600)
      (((920 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch046Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch046Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((920 : ℝ) + (j.val : ℝ)) / 1600)
    (((920 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch046Neg20WeightLower j.val) (hpThetaShiftOneBatch046Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch046Neg20WeightLower, hpThetaShiftOneBatch046Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch046Neg20_integral_bounds :
    (-39363599019 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-19292457481 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (920 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch046Lower hpThetaJensenCellsBatch046Upper
    hpThetaShiftOneBatch046Neg20WeightLower hpThetaShiftOneBatch046Neg20WeightUpper hpThetaJensenCellsBatch046_bounds hpThetaShiftOneBatch046Neg20_weight_bounds
  have hl : (-39363599019 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch046Lower j * hpThetaShiftOneBatch046Neg20WeightLower j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftOneBatch046Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftOneBatch046Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch046Lower j * hpThetaShiftOneBatch046Neg20WeightUpper j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftOneBatch046Neg20WeightUpper j) / 1600) ≤ (-19292457481 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftOneBatch046Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (920 : ℝ) / 1600 = 46 / 80 by norm_num,
    show ((920 : ℝ) + 20) / 1600 = (46 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch046Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch046Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch046Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch046Neg20_integral_bounds
end HodgeProofHP
