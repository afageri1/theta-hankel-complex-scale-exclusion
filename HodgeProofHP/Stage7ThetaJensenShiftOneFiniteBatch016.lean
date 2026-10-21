/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch016

/-! Exact signed weight and batch integral certificates, batch 16 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch016Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5637123829 / 1000000000000 : ℝ)
  | 1 => (-1150173409 / 200000000000 : ℝ)
  | 2 => (-5865025181 / 1000000000000 : ℝ)
  | 3 => (-1494896007 / 250000000000 : ℝ)
  | 4 => (-3047264583 / 500000000000 : ℝ)
  | 5 => (-1552461489 / 250000000000 : ℝ)
  | 6 => (-1581379887 / 250000000000 : ℝ)
  | 7 => (-6441534873 / 1000000000000 : ℝ)
  | 8 => (-819734581 / 125000000000 : ℝ)
  | 9 => (-3337264687 / 500000000000 : ℝ)
  | 10 => (-3395738667 / 500000000000 : ℝ)
  | 11 => (-1727176149 / 250000000000 : ℝ)
  | 12 => (-702619501 / 100000000000 : ℝ)
  | 13 => (-1785983053 / 250000000000 : ℝ)
  | 14 => (-7261899617 / 1000000000000 : ℝ)
  | 15 => (-7380080427 / 1000000000000 : ℝ)
  | 16 => (-7498457623 / 1000000000000 : ℝ)
  | 17 => (-761701397 / 100000000000 : ℝ)
  | 18 => (-3867866009 / 500000000000 : ℝ)
  | 19 => (-1570918819 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch016Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5523809523 / 1000000000000 : ℝ)
  | 1 => (-1409280957 / 250000000000 : ℝ)
  | 2 => (-1437716761 / 250000000000 : ℝ)
  | 3 => (-293251259 / 50000000000 : ℝ)
  | 4 => (-5979584027 / 1000000000000 : ℝ)
  | 5 => (-1218905833 / 200000000000 : ℝ)
  | 6 => (-1241969191 / 200000000000 : ℝ)
  | 7 => (-6325519547 / 1000000000000 : ℝ)
  | 8 => (-805191859 / 125000000000 : ℝ)
  | 9 => (-6557876647 / 1000000000000 : ℝ)
  | 10 => (-6674529373 / 1000000000000 : ℝ)
  | 11 => (-6791477333 / 1000000000000 : ℝ)
  | 12 => (-1381740919 / 200000000000 : ℝ)
  | 13 => (-7026195009 / 1000000000000 : ℝ)
  | 14 => (-7143932211 / 1000000000000 : ℝ)
  | 15 => (-226934363 / 31250000000 : ℝ)
  | 16 => (-3690040213 / 500000000000 : ℝ)
  | 17 => (-3749228811 / 500000000000 : ℝ)
  | 18 => (-7617013969 / 1000000000000 : ℝ)
  | 19 => (-7735732017 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch016Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((320 : ℝ) + (j.val : ℝ)) / 1600)
      (((320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch016Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch016Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((320 : ℝ) + (j.val : ℝ)) / 1600)
    (((320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch016Neg100WeightLower j.val) (hpThetaShiftOneBatch016Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch016Neg100WeightLower, hpThetaShiftOneBatch016Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch016Neg100_integral_bounds :
    (-100554724129 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-95350317 / 976562500000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch016Lower hpThetaJensenCellsBatch016Upper
    hpThetaShiftOneBatch016Neg100WeightLower hpThetaShiftOneBatch016Neg100WeightUpper hpThetaJensenCellsBatch016_bounds hpThetaShiftOneBatch016Neg100_weight_bounds
  have hl : (-100554724129 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch016Lower j * hpThetaShiftOneBatch016Neg100WeightLower j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftOneBatch016Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftOneBatch016Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch016Lower j * hpThetaShiftOneBatch016Neg100WeightUpper j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftOneBatch016Neg100WeightUpper j) / 1600) ≤ (-95350317 / 976562500000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftOneBatch016Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (320 : ℝ) / 1600 = 16 / 80 by norm_num,
    show ((320 : ℝ) + 20) / 1600 = (16 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch016Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (64339957 / 250000000000 : ℝ)
  | 1 => (34458539 / 200000000000 : ℝ)
  | 2 => (86323991 / 1000000000000 : ℝ)
  | 3 => (-136149 / 250000000000 : ℝ)
  | 4 => (-88311271 / 1000000000000 : ℝ)
  | 5 => (-176974131 / 1000000000000 : ℝ)
  | 6 => (-133265583 / 500000000000 : ℝ)
  | 7 => (-356980253 / 1000000000000 : ℝ)
  | 8 => (-224159581 / 500000000000 : ℝ)
  | 9 => (-270272777 / 500000000000 : ℝ)
  | 10 => (-39603561 / 62500000000 : ℝ)
  | 11 => (-145530173 / 200000000000 : ℝ)
  | 12 => (-164504909 / 200000000000 : ℝ)
  | 13 => (-918275231 / 1000000000000 : ℝ)
  | 14 => (-1014900019 / 1000000000000 : ℝ)
  | 15 => (-139049487 / 125000000000 : ℝ)
  | 16 => (-302689933 / 250000000000 : ℝ)
  | 17 => (-327497071 / 250000000000 : ℝ)
  | 18 => (-88129887 / 62500000000 : ℝ)
  | 19 => (-75551299 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch016Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (34152381 / 100000000000 : ℝ)
  | 1 => (257359829 / 1000000000000 : ℝ)
  | 2 => (21536587 / 125000000000 : ℝ)
  | 3 => (10790499 / 125000000000 : ℝ)
  | 4 => (-108919 / 200000000000 : ℝ)
  | 5 => (-8831127 / 100000000000 : ℝ)
  | 6 => (-17697413 / 100000000000 : ℝ)
  | 7 => (-53306233 / 200000000000 : ℝ)
  | 8 => (-89245063 / 250000000000 : ℝ)
  | 9 => (-448319161 / 1000000000000 : ℝ)
  | 10 => (-540545553 / 1000000000000 : ℝ)
  | 11 => (-25346279 / 40000000000 : ℝ)
  | 12 => (-45478179 / 62500000000 : ℝ)
  | 13 => (-6425973 / 7812500000 : ℝ)
  | 14 => (-91827523 / 100000000000 : ℝ)
  | 15 => (-507450009 / 500000000000 : ℝ)
  | 16 => (-222479179 / 200000000000 : ℝ)
  | 17 => (-1210759731 / 1000000000000 : ℝ)
  | 18 => (-1309988283 / 1000000000000 : ℝ)
  | 19 => (-1410078191 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch016Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((320 : ℝ) + (j.val : ℝ)) / 1600)
      (((320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch016Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch016Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((320 : ℝ) + (j.val : ℝ)) / 1600)
    (((320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch016Neg65WeightLower j.val) (hpThetaShiftOneBatch016Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch016Neg65WeightLower, hpThetaShiftOneBatch016Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch016Neg65_integral_bounds :
    (-2219964153 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-1848709761 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch016Lower hpThetaJensenCellsBatch016Upper
    hpThetaShiftOneBatch016Neg65WeightLower hpThetaShiftOneBatch016Neg65WeightUpper hpThetaJensenCellsBatch016_bounds hpThetaShiftOneBatch016Neg65_weight_bounds
  have hl : (-2219964153 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch016Lower j * hpThetaShiftOneBatch016Neg65WeightLower j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftOneBatch016Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftOneBatch016Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch016Lower j * hpThetaShiftOneBatch016Neg65WeightUpper j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftOneBatch016Neg65WeightUpper j) / 1600) ≤ (-1848709761 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftOneBatch016Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (320 : ℝ) / 1600 = 16 / 80 by norm_num,
    show ((320 : ℝ) + 20) / 1600 = (16 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch016Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1286528737 / 200000000000 : ℝ)
  | 1 => (1600505037 / 250000000000 : ℝ)
  | 2 => (6370602291 / 1000000000000 : ℝ)
  | 3 => (6338386859 / 1000000000000 : ℝ)
  | 4 => (1576342659 / 250000000000 : ℝ)
  | 5 => (6271550441 / 1000000000000 : ℝ)
  | 6 => (3118461567 / 500000000000 : ℝ)
  | 7 => (775185701 / 125000000000 : ℝ)
  | 8 => (3082617399 / 500000000000 : ℝ)
  | 9 => (1532041919 / 250000000000 : ℝ)
  | 10 => (1522570313 / 250000000000 : ℝ)
  | 11 => (3025786289 / 500000000000 : ℝ)
  | 12 => (6012038741 / 1000000000000 : ℝ)
  | 13 => (746459609 / 125000000000 : ℝ)
  | 14 => (296524207 / 50000000000 : ℝ)
  | 15 => (1472114439 / 250000000000 : ℝ)
  | 16 => (5845594971 / 1000000000000 : ℝ)
  | 17 => (5801893077 / 1000000000000 : ℝ)
  | 18 => (5757349409 / 1000000000000 : ℝ)
  | 19 => (2855980671 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch016Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (6462476191 / 1000000000000 : ℝ)
  | 1 => (3216321843 / 500000000000 : ℝ)
  | 2 => (6402020149 / 1000000000000 : ℝ)
  | 3 => (1592650573 / 250000000000 : ℝ)
  | 4 => (316919343 / 50000000000 : ℝ)
  | 5 => (6305370637 / 1000000000000 : ℝ)
  | 6 => (3135775221 / 500000000000 : ℝ)
  | 7 => (1247384627 / 200000000000 : ℝ)
  | 8 => (6201485609 / 1000000000000 : ℝ)
  | 9 => (6165234799 / 1000000000000 : ℝ)
  | 10 => (6128167677 / 1000000000000 : ℝ)
  | 11 => (6090281253 / 1000000000000 : ℝ)
  | 12 => (6051572579 / 1000000000000 : ℝ)
  | 13 => (3006019371 / 500000000000 : ℝ)
  | 14 => (5971676873 / 1000000000000 : ℝ)
  | 15 => (5930484141 / 1000000000000 : ℝ)
  | 16 => (5888457757 / 1000000000000 : ℝ)
  | 17 => (1461398743 / 250000000000 : ℝ)
  | 18 => (2900946539 / 500000000000 : ℝ)
  | 19 => (575734941 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch016Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((320 : ℝ) + (j.val : ℝ)) / 1600)
      (((320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch016Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch016Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((320 : ℝ) + (j.val : ℝ)) / 1600)
    (((320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch016Neg40WeightLower j.val) (hpThetaShiftOneBatch016Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch016Neg40WeightLower, hpThetaShiftOneBatch016Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch016Neg40_integral_bounds :
    (2814714417 / 31250000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (91713762713 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch016Lower hpThetaJensenCellsBatch016Upper
    hpThetaShiftOneBatch016Neg40WeightLower hpThetaShiftOneBatch016Neg40WeightUpper hpThetaJensenCellsBatch016_bounds hpThetaShiftOneBatch016Neg40_weight_bounds
  have hl : (2814714417 / 31250000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch016Lower j * hpThetaShiftOneBatch016Neg40WeightLower j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftOneBatch016Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftOneBatch016Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch016Lower j * hpThetaShiftOneBatch016Neg40WeightUpper j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftOneBatch016Neg40WeightUpper j) / 1600) ≤ (91713762713 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftOneBatch016Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (320 : ℝ) / 1600 = 16 / 80 by norm_num,
    show ((320 : ℝ) + 20) / 1600 = (16 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch016Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (12627809523 / 1000000000000 : ℝ)
  | 1 => (6332160567 / 500000000000 : ℝ)
  | 2 => (12700463063 / 1000000000000 : ℝ)
  | 3 => (12736231673 / 1000000000000 : ℝ)
  | 4 => (399113229 / 31250000000 : ℝ)
  | 5 => (6403317197 / 500000000000 : ℝ)
  | 6 => (12841261239 / 1000000000000 : ℝ)
  | 7 => (6437750117 / 500000000000 : ℝ)
  | 8 => (12909347751 / 1000000000000 : ℝ)
  | 9 => (6471400083 / 500000000000 : ℝ)
  | 10 => (12975853857 / 1000000000000 : ℝ)
  | 11 => (3252126301 / 250000000000 : ℝ)
  | 12 => (3183777 / 244140625 : ℝ)
  | 13 => (13072586407 / 1000000000000 : ℝ)
  | 14 => (6552004519 / 500000000000 : ℝ)
  | 15 => (6567507439 / 500000000000 : ℝ)
  | 16 => (3291400081 / 250000000000 : ℝ)
  | 17 => (527830471 / 40000000000 : ℝ)
  | 18 => (6612747817 / 500000000000 : ℝ)
  | 19 => (3313699577 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch016Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2532864227 / 200000000000 : ℝ)
  | 1 => (1587557883 / 125000000000 : ℝ)
  | 2 => (6368115837 / 500000000000 : ℝ)
  | 3 => (12771623329 / 1000000000000 : ℝ)
  | 4 => (2561326879 / 200000000000 : ℝ)
  | 5 => (321031531 / 25000000000 : ℝ)
  | 6 => (2575100047 / 200000000000 : ℝ)
  | 7 => (1613668469 / 125000000000 : ℝ)
  | 8 => (12942800167 / 1000000000000 : ℝ)
  | 9 => (6487926929 / 500000000000 : ℝ)
  | 10 => (2601701041 / 200000000000 : ℝ)
  | 11 => (13040750593 / 1000000000000 : ℝ)
  | 12 => (1634073301 / 125000000000 : ℝ)
  | 13 => (13104009039 / 1000000000000 : ℝ)
  | 14 => (13135014879 / 1000000000000 : ℝ)
  | 15 => (526624013 / 40000000000 : ℝ)
  | 16 => (824735111 / 62500000000 : ℝ)
  | 17 => (2645099127 / 200000000000 : ℝ)
  | 18 => (13254798309 / 1000000000000 : ℝ)
  | 19 => (415114569 / 31250000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch016Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((320 : ℝ) + (j.val : ℝ)) / 1600)
      (((320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch016Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch016Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((320 : ℝ) + (j.val : ℝ)) / 1600)
    (((320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch016Neg20WeightLower j.val) (hpThetaShiftOneBatch016Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch016Neg20WeightLower, hpThetaShiftOneBatch016Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch016Neg20_integral_bounds :
    (191249598881 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (16 / 80 : ℝ) ((16 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (19404030493 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch016Lower hpThetaJensenCellsBatch016Upper
    hpThetaShiftOneBatch016Neg20WeightLower hpThetaShiftOneBatch016Neg20WeightUpper hpThetaJensenCellsBatch016_bounds hpThetaShiftOneBatch016Neg20_weight_bounds
  have hl : (191249598881 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch016Lower j * hpThetaShiftOneBatch016Neg20WeightLower j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftOneBatch016Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftOneBatch016Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch016Lower j * hpThetaShiftOneBatch016Neg20WeightUpper j)
        (hpThetaJensenCellsBatch016Upper j * hpThetaShiftOneBatch016Neg20WeightUpper j) / 1600) ≤ (19404030493 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch016Lower, hpThetaJensenCellsBatch016Upper,
      hpThetaShiftOneBatch016Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (320 : ℝ) / 1600 = 16 / 80 by norm_num,
    show ((320 : ℝ) + 20) / 1600 = (16 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch016Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch016Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch016Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch016Neg20_integral_bounds
end HodgeProofHP
