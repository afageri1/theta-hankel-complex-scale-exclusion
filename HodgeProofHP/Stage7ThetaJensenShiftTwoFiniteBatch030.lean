/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch030

/-! Exact signed weight and batch integral certificates, batch 30 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch030Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-69793713 / 500000000000 : ℝ)
  | 1 => (-67634373 / 500000000000 : ℝ)
  | 2 => (-130841719 / 1000000000000 : ℝ)
  | 3 => (-6315261 / 50000000000 : ℝ)
  | 4 => (-7603633 / 62500000000 : ℝ)
  | 5 => (-58449659 / 500000000000 : ℝ)
  | 6 => (-28006917 / 250000000000 : ℝ)
  | 7 => (-107042053 / 1000000000000 : ℝ)
  | 8 => (-101941351 / 1000000000000 : ℝ)
  | 9 => (-48362219 / 500000000000 : ℝ)
  | 10 => (-91390193 / 1000000000000 : ℝ)
  | 11 => (-42968747 / 500000000000 : ℝ)
  | 12 => (-80365221 / 1000000000000 : ℝ)
  | 13 => (-14934451 / 200000000000 : ℝ)
  | 14 => (-68857479 / 1000000000000 : ℝ)
  | 15 => (-1966243 / 31250000000 : ℝ)
  | 16 => (-56858033 / 1000000000000 : ℝ)
  | 17 => (-50671137 / 1000000000000 : ℝ)
  | 18 => (-2217899 / 50000000000 : ℝ)
  | 19 => (-37917453 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch030Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-27053749 / 200000000000 : ℝ)
  | 1 => (-65420859 / 500000000000 : ℝ)
  | 2 => (-126305219 / 1000000000000 : ℝ)
  | 3 => (-121658127 / 1000000000000 : ℝ)
  | 4 => (-116899317 / 1000000000000 : ℝ)
  | 5 => (-112027667 / 1000000000000 : ℝ)
  | 6 => (-26760513 / 250000000000 : ℝ)
  | 7 => (-2038827 / 20000000000 : ℝ)
  | 8 => (-96724437 / 1000000000000 : ℝ)
  | 9 => (-5711887 / 62500000000 : ℝ)
  | 10 => (-85937493 / 1000000000000 : ℝ)
  | 11 => (-4018261 / 50000000000 : ℝ)
  | 12 => (-37336127 / 500000000000 : ℝ)
  | 13 => (-34428739 / 500000000000 : ℝ)
  | 14 => (-2516791 / 40000000000 : ℝ)
  | 15 => (-3553627 / 62500000000 : ℝ)
  | 16 => (-1583473 / 31250000000 : ℝ)
  | 17 => (-44357979 / 1000000000000 : ℝ)
  | 18 => (-9479363 / 250000000000 : ℝ)
  | 19 => (-7837113 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch030Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((600 : ℝ) + (j.val : ℝ)) / 1600)
      (((600 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch030Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch030Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((600 : ℝ) + (j.val : ℝ)) / 1600)
    (((600 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch030Neg100WeightLower j.val) (hpThetaShiftTwoBatch030Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch030Neg100WeightLower, hpThetaShiftTwoBatch030Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch030Neg100_integral_bounds :
    (-238050901 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-442190739 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (600 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch030Lower hpThetaJensenCellsBatch030Upper
    hpThetaShiftTwoBatch030Neg100WeightLower hpThetaShiftTwoBatch030Neg100WeightUpper hpThetaJensenCellsBatch030_bounds hpThetaShiftTwoBatch030Neg100_weight_bounds
  have hl : (-238050901 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch030Lower j * hpThetaShiftTwoBatch030Neg100WeightLower j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftTwoBatch030Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftTwoBatch030Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch030Lower j * hpThetaShiftTwoBatch030Neg100WeightUpper j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftTwoBatch030Neg100WeightUpper j) / 1600) ≤ (-442190739 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftTwoBatch030Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (600 : ℝ) / 1600 = 30 / 80 by norm_num,
    show ((600 : ℝ) + 20) / 1600 = (30 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch030Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-423190031 / 1000000000000 : ℝ)
  | 1 => (-426358559 / 1000000000000 : ℝ)
  | 2 => (-17180537 / 40000000000 : ℝ)
  | 3 => (-432654017 / 1000000000000 : ℝ)
  | 4 => (-435779713 / 1000000000000 : ℝ)
  | 5 => (-438889887 / 1000000000000 : ℝ)
  | 6 => (-13811997 / 31250000000 : ℝ)
  | 7 => (-445061123 / 1000000000000 : ℝ)
  | 8 => (-448120899 / 1000000000000 : ℝ)
  | 9 => (-28197661 / 62500000000 : ℝ)
  | 10 => (-90837099 / 200000000000 : ℝ)
  | 11 => (-457188987 / 1000000000000 : ℝ)
  | 12 => (-230086189 / 500000000000 : ℝ)
  | 13 => (-115783747 / 250000000000 : ℝ)
  | 14 => (-466076129 / 1000000000000 : ℝ)
  | 15 => (-234497553 / 500000000000 : ℝ)
  | 16 => (-235945609 / 500000000000 : ℝ)
  | 17 => (-474763757 / 1000000000000 : ℝ)
  | 18 => (-477612007 / 1000000000000 : ℝ)
  | 19 => (-30027203 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch030Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-420008449 / 1000000000000 : ℝ)
  | 1 => (-42319003 / 100000000000 : ℝ)
  | 2 => (-213179279 / 500000000000 : ℝ)
  | 3 => (-26844589 / 62500000000 : ℝ)
  | 4 => (-6760219 / 15625000000 : ℝ)
  | 5 => (-3404529 / 7812500000 : ℝ)
  | 6 => (-219444943 / 500000000000 : ℝ)
  | 7 => (-441983903 / 1000000000000 : ℝ)
  | 8 => (-222530561 / 500000000000 : ℝ)
  | 9 => (-224060449 / 500000000000 : ℝ)
  | 10 => (-18046503 / 40000000000 : ℝ)
  | 11 => (-227092747 / 500000000000 : ℝ)
  | 12 => (-228594493 / 500000000000 : ℝ)
  | 13 => (-460172377 / 1000000000000 : ℝ)
  | 14 => (-463134987 / 1000000000000 : ℝ)
  | 15 => (-14564879 / 31250000000 : ℝ)
  | 16 => (-93799021 / 200000000000 : ℝ)
  | 17 => (-471891217 / 1000000000000 : ℝ)
  | 18 => (-118690939 / 250000000000 : ℝ)
  | 19 => (-238806003 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch030Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((600 : ℝ) + (j.val : ℝ)) / 1600)
      (((600 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch030Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch030Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((600 : ℝ) + (j.val : ℝ)) / 1600)
    (((600 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch030Neg65WeightLower j.val) (hpThetaShiftTwoBatch030Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch030Neg65WeightLower, hpThetaShiftTwoBatch030Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch030Neg65_integral_bounds :
    (-289003473 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-2264119533 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (600 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch030Lower hpThetaJensenCellsBatch030Upper
    hpThetaShiftTwoBatch030Neg65WeightLower hpThetaShiftTwoBatch030Neg65WeightUpper hpThetaJensenCellsBatch030_bounds hpThetaShiftTwoBatch030Neg65_weight_bounds
  have hl : (-289003473 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch030Lower j * hpThetaShiftTwoBatch030Neg65WeightLower j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftTwoBatch030Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftTwoBatch030Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch030Lower j * hpThetaShiftTwoBatch030Neg65WeightUpper j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftTwoBatch030Neg65WeightUpper j) / 1600) ≤ (-2264119533 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftTwoBatch030Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (600 : ℝ) / 1600 = 30 / 80 by norm_num,
    show ((600 : ℝ) + 20) / 1600 = (30 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch030Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-236393587 / 1000000000000 : ℝ)
  | 1 => (-240640273 / 1000000000000 : ℝ)
  | 2 => (-244914001 / 1000000000000 : ℝ)
  | 3 => (-249214669 / 1000000000000 : ℝ)
  | 4 => (-63385543 / 250000000000 : ℝ)
  | 5 => (-257896403 / 1000000000000 : ℝ)
  | 6 => (-262277249 / 1000000000000 : ℝ)
  | 7 => (-133342297 / 500000000000 : ℝ)
  | 8 => (-271118319 / 1000000000000 : ℝ)
  | 9 => (-2755783 / 10000000000 : ℝ)
  | 10 => (-280064411 / 1000000000000 : ℝ)
  | 11 => (-142288261 / 500000000000 : ℝ)
  | 12 => (-2258707 / 7812500000 : ℝ)
  | 13 => (-293678197 / 1000000000000 : ℝ)
  | 14 => (-298267481 / 1000000000000 : ℝ)
  | 15 => (-302882203 / 1000000000000 : ℝ)
  | 16 => (-76880553 / 250000000000 : ℝ)
  | 17 => (-62437471 / 200000000000 : ℝ)
  | 18 => (-9902421 / 31250000000 : ℝ)
  | 19 => (-160796201 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch030Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5804351 / 25000000000 : ℝ)
  | 1 => (-118196793 / 500000000000 : ℝ)
  | 2 => (-15040017 / 62500000000 : ℝ)
  | 3 => (-122457 / 500000000 : ℝ)
  | 4 => (-62303667 / 250000000000 : ℝ)
  | 5 => (-253542171 / 1000000000000 : ℝ)
  | 6 => (-128948201 / 500000000000 : ℝ)
  | 7 => (-2049041 / 7812500000 : ℝ)
  | 8 => (-266684593 / 1000000000000 : ℝ)
  | 9 => (-135559159 / 500000000000 : ℝ)
  | 10 => (-275578299 / 1000000000000 : ℝ)
  | 11 => (-28006441 / 100000000000 : ℝ)
  | 12 => (-284576521 / 1000000000000 : ℝ)
  | 13 => (-57822899 / 200000000000 : ℝ)
  | 14 => (-73419549 / 250000000000 : ℝ)
  | 15 => (-7456687 / 25000000000 : ℝ)
  | 16 => (-151441101 / 500000000000 : ℝ)
  | 17 => (-307522211 / 1000000000000 : ℝ)
  | 18 => (-156093677 / 500000000000 : ℝ)
  | 19 => (-316877471 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch030Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((600 : ℝ) + (j.val : ℝ)) / 1600)
      (((600 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch030Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch030Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((600 : ℝ) + (j.val : ℝ)) / 1600)
    (((600 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch030Neg45WeightLower j.val) (hpThetaShiftTwoBatch030Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch030Neg45WeightLower, hpThetaShiftTwoBatch030Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch030Neg45_integral_bounds :
    (-35495303 / 25000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-1377225883 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (600 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch030Lower hpThetaJensenCellsBatch030Upper
    hpThetaShiftTwoBatch030Neg45WeightLower hpThetaShiftTwoBatch030Neg45WeightUpper hpThetaJensenCellsBatch030_bounds hpThetaShiftTwoBatch030Neg45_weight_bounds
  have hl : (-35495303 / 25000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch030Lower j * hpThetaShiftTwoBatch030Neg45WeightLower j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftTwoBatch030Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftTwoBatch030Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch030Lower j * hpThetaShiftTwoBatch030Neg45WeightUpper j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftTwoBatch030Neg45WeightUpper j) / 1600) ≤ (-1377225883 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftTwoBatch030Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (600 : ℝ) / 1600 = 30 / 80 by norm_num,
    show ((600 : ℝ) + 20) / 1600 = (30 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch030Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (158428553 / 500000000000 : ℝ)
  | 1 => (15788233 / 50000000000 : ℝ)
  | 2 => (3146427 / 10000000000 : ℝ)
  | 3 => (313491027 / 1000000000000 : ℝ)
  | 4 => (312309443 / 1000000000000 : ℝ)
  | 5 => (1244391 / 4000000000 : ℝ)
  | 6 => (309855751 / 1000000000000 : ℝ)
  | 7 => (308583247 / 1000000000000 : ℝ)
  | 8 => (307280041 / 1000000000000 : ℝ)
  | 9 => (61189187 / 200000000000 : ℝ)
  | 10 => (304580731 / 1000000000000 : ℝ)
  | 11 => (37898029 / 125000000000 : ℝ)
  | 12 => (150878121 / 500000000000 : ℝ)
  | 13 => (150148281 / 500000000000 : ℝ)
  | 14 => (298804997 / 1000000000000 : ℝ)
  | 15 => (74320337 / 250000000000 : ℝ)
  | 16 => (295725421 / 1000000000000 : ℝ)
  | 17 => (147068509 / 500000000000 : ℝ)
  | 18 => (36564493 / 125000000000 : ℝ)
  | 19 => (145431001 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch030Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (317920237 / 1000000000000 : ℝ)
  | 1 => (316857107 / 1000000000000 : ℝ)
  | 2 => (315764661 / 1000000000000 : ℝ)
  | 3 => (314642701 / 1000000000000 : ℝ)
  | 4 => (78372757 / 250000000000 : ℝ)
  | 5 => (78077361 / 250000000000 : ℝ)
  | 6 => (311097751 / 1000000000000 : ℝ)
  | 7 => (38731969 / 125000000000 : ℝ)
  | 8 => (19286453 / 62500000000 : ℝ)
  | 9 => (153640021 / 500000000000 : ℝ)
  | 10 => (19121621 / 62500000000 : ℝ)
  | 11 => (76145183 / 250000000000 : ℝ)
  | 12 => (303184233 / 1000000000000 : ℝ)
  | 13 => (301756243 / 1000000000000 : ℝ)
  | 14 => (300296563 / 1000000000000 : ℝ)
  | 15 => (149402499 / 500000000000 : ℝ)
  | 16 => (297281349 / 1000000000000 : ℝ)
  | 17 => (147862711 / 500000000000 : ℝ)
  | 18 => (294137019 / 1000000000000 : ℝ)
  | 19 => (58503189 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch030Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((600 : ℝ) + (j.val : ℝ)) / 1600)
      (((600 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch030Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch030Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((600 : ℝ) + (j.val : ℝ)) / 1600)
    (((600 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch030Neg25WeightLower j.val) (hpThetaShiftTwoBatch030Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch030Neg25WeightLower, hpThetaShiftTwoBatch030Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch030Neg25_integral_bounds :
    (192322969 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (1567511777 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (600 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch030Lower hpThetaJensenCellsBatch030Upper
    hpThetaShiftTwoBatch030Neg25WeightLower hpThetaShiftTwoBatch030Neg25WeightUpper hpThetaJensenCellsBatch030_bounds hpThetaShiftTwoBatch030Neg25_weight_bounds
  have hl : (192322969 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch030Lower j * hpThetaShiftTwoBatch030Neg25WeightLower j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftTwoBatch030Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftTwoBatch030Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch030Lower j * hpThetaShiftTwoBatch030Neg25WeightUpper j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftTwoBatch030Neg25WeightUpper j) / 1600) ≤ (1567511777 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftTwoBatch030Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (600 : ℝ) / 1600 = 30 / 80 by norm_num,
    show ((600 : ℝ) + 20) / 1600 = (30 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch030Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch030Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch030Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch030Neg25_integral_bounds
end HodgeProofHP
