/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch028

/-! Exact signed weight and batch integral certificates, batch 28 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch028Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (11619954427 / 1000000000000 : ℝ)
  | 1 => (12171115217 / 1000000000000 : ℝ)
  | 2 => (12728344929 / 1000000000000 : ℝ)
  | 3 => (13291648801 / 1000000000000 : ℝ)
  | 4 => (6930515677 / 500000000000 : ℝ)
  | 5 => (14436496379 / 1000000000000 : ℝ)
  | 6 => (15018046923 / 1000000000000 : ℝ)
  | 7 => (3121137057 / 200000000000 : ℝ)
  | 8 => (16199412999 / 1000000000000 : ℝ)
  | 9 => (8399615413 / 500000000000 : ℝ)
  | 10 => (8702569371 / 500000000000 : ℝ)
  | 11 => (18017135931 / 1000000000000 : ℝ)
  | 12 => (9317610383 / 500000000000 : ℝ)
  | 13 => (3851878161 / 200000000000 : ℝ)
  | 14 => (19889642777 / 1000000000000 : ℝ)
  | 15 => (20525972571 / 1000000000000 : ℝ)
  | 16 => (10584187611 / 500000000000 : ℝ)
  | 17 => (10908422453 / 500000000000 : ℝ)
  | 18 => (11235687461 / 500000000000 : ℝ)
  | 19 => (23131957681 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch028Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (6085557609 / 500000000000 : ℝ)
  | 1 => (1272834493 / 100000000000 : ℝ)
  | 2 => (6645824401 / 500000000000 : ℝ)
  | 3 => (2772206271 / 200000000000 : ℝ)
  | 4 => (721824819 / 50000000000 : ℝ)
  | 5 => (3754511731 / 250000000000 : ℝ)
  | 6 => (7802842643 / 500000000000 : ℝ)
  | 7 => (16199413 / 1000000000 : ℝ)
  | 8 => (16799230827 / 1000000000000 : ℝ)
  | 9 => (17405138743 / 1000000000000 : ℝ)
  | 10 => (4504283983 / 250000000000 : ℝ)
  | 11 => (18635220767 / 1000000000000 : ℝ)
  | 12 => (9629695403 / 500000000000 : ℝ)
  | 13 => (9944821389 / 500000000000 : ℝ)
  | 14 => (5131493143 / 250000000000 : ℝ)
  | 15 => (21168375223 / 1000000000000 : ℝ)
  | 16 => (21816844907 / 1000000000000 : ℝ)
  | 17 => (22471374923 / 1000000000000 : ℝ)
  | 18 => (11565978841 / 500000000000 : ℝ)
  | 19 => (237985847 / 10000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch028Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((560 : ℝ) + (j.val : ℝ)) / 1600)
      (((560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch028Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch028Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((560 : ℝ) + (j.val : ℝ)) / 1600)
    (((560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch028Neg100WeightLower j.val) (hpThetaShiftOneBatch028Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch028Neg100WeightLower, hpThetaShiftOneBatch028Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch028Neg100_integral_bounds :
    (105532717121 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (55403499731 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch028Lower hpThetaJensenCellsBatch028Upper
    hpThetaShiftOneBatch028Neg100WeightLower hpThetaShiftOneBatch028Neg100WeightUpper hpThetaJensenCellsBatch028_bounds hpThetaShiftOneBatch028Neg100_weight_bounds
  have hl : (105532717121 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch028Lower j * hpThetaShiftOneBatch028Neg100WeightLower j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftOneBatch028Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftOneBatch028Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch028Lower j * hpThetaShiftOneBatch028Neg100WeightUpper j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftOneBatch028Neg100WeightUpper j) / 1600) ≤ (55403499731 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftOneBatch028Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (560 : ℝ) / 1600 = 28 / 80 by norm_num,
    show ((560 : ℝ) + 20) / 1600 = (28 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch028Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5049109257 / 200000000000 : ℝ)
  | 1 => (-25212567709 / 1000000000000 : ℝ)
  | 2 => (-25176499351 / 1000000000000 : ℝ)
  | 3 => (-25137312261 / 1000000000000 : ℝ)
  | 4 => (-12547488733 / 500000000000 : ℝ)
  | 5 => (-12524732989 / 500000000000 : ℝ)
  | 6 => (-12500374397 / 500000000000 : ℝ)
  | 7 => (-249487969 / 10000000000 : ℝ)
  | 8 => (-24893581271 / 1000000000000 : ℝ)
  | 9 => (-3104384109 / 125000000000 : ℝ)
  | 10 => (-3096655333 / 125000000000 : ℝ)
  | 11 => (-6177015401 / 250000000000 : ℝ)
  | 12 => (-12319750323 / 500000000000 : ℝ)
  | 13 => (-3070941343 / 125000000000 : ℝ)
  | 14 => (-4898424571 / 200000000000 : ℝ)
  | 15 => (-24413247941 / 1000000000000 : ℝ)
  | 16 => (-24330876971 / 1000000000000 : ℝ)
  | 17 => (-12122490461 / 500000000000 : ℝ)
  | 18 => (-754860337 / 31250000000 : ℝ)
  | 19 => (-24062497559 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch028Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6303141927 / 250000000000 : ℝ)
  | 1 => (-503529987 / 20000000000 : ℝ)
  | 2 => (-1256865613 / 50000000000 : ℝ)
  | 3 => (-5018995493 / 200000000000 : ℝ)
  | 4 => (-25049465977 / 1000000000000 : ℝ)
  | 5 => (-25000748793 / 1000000000000 : ℝ)
  | 6 => (-24948796899 / 1000000000000 : ℝ)
  | 7 => (-2489358127 / 100000000000 : ℝ)
  | 8 => (-24835072871 / 1000000000000 : ℝ)
  | 9 => (-24773242663 / 1000000000000 : ℝ)
  | 10 => (-24708061603 / 1000000000000 : ℝ)
  | 11 => (-4927900129 / 200000000000 : ℝ)
  | 12 => (-24567530743 / 1000000000000 : ℝ)
  | 13 => (-12246061427 / 500000000000 : ℝ)
  | 14 => (-1220662397 / 50000000000 : ℝ)
  | 15 => (-2433087697 / 100000000000 : ℝ)
  | 16 => (-24244980921 / 1000000000000 : ℝ)
  | 17 => (-24155530783 / 1000000000000 : ℝ)
  | 18 => (-12031248779 / 500000000000 : ℝ)
  | 19 => (-4793170453 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch028Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((560 : ℝ) + (j.val : ℝ)) / 1600)
      (((560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch028Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch028Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((560 : ℝ) + (j.val : ℝ)) / 1600)
    (((560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch028Neg65WeightLower j.val) (hpThetaShiftOneBatch028Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch028Neg65WeightLower, hpThetaShiftOneBatch028Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch028Neg65_integral_bounds :
    (-77439140111 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-76179583213 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch028Lower hpThetaJensenCellsBatch028Upper
    hpThetaShiftOneBatch028Neg65WeightLower hpThetaShiftOneBatch028Neg65WeightUpper hpThetaJensenCellsBatch028_bounds hpThetaShiftOneBatch028Neg65_weight_bounds
  have hl : (-77439140111 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch028Lower j * hpThetaShiftOneBatch028Neg65WeightLower j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftOneBatch028Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftOneBatch028Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch028Lower j * hpThetaShiftOneBatch028Neg65WeightUpper j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftOneBatch028Neg65WeightUpper j) / 1600) ≤ (-76179583213 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftOneBatch028Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (560 : ℝ) / 1600 = 28 / 80 by norm_num,
    show ((560 : ℝ) + 20) / 1600 = (28 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch028Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4809643649 / 200000000000 : ℝ)
  | 1 => (-24235824471 / 1000000000000 : ℝ)
  | 2 => (-24423253141 / 1000000000000 : ℝ)
  | 3 => (-24610490719 / 1000000000000 : ℝ)
  | 4 => (-24797523581 / 1000000000000 : ℝ)
  | 5 => (-24984338017 / 1000000000000 : ℝ)
  | 6 => (-25170920233 / 1000000000000 : ℝ)
  | 7 => (-6339314087 / 250000000000 : ℝ)
  | 8 => (-25543332397 / 1000000000000 : ℝ)
  | 9 => (-25729134329 / 1000000000000 : ℝ)
  | 10 => (-3239331001 / 125000000000 : ℝ)
  | 11 => (-13049929607 / 500000000000 : ℝ)
  | 12 => (-26284753641 / 1000000000000 : ℝ)
  | 13 => (-26469316899 / 1000000000000 : ℝ)
  | 14 => (-1665845907 / 62500000000 : ℝ)
  | 15 => (-13418695961 / 500000000000 : ℝ)
  | 16 => (-13510437243 / 500000000000 : ℝ)
  | 17 => (-1088158699 / 40000000000 : ℝ)
  | 18 => (-13693328039 / 500000000000 : ℝ)
  | 19 => (-137844627 / 5000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch028Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5965111979 / 250000000000 : ℝ)
  | 1 => (-6012054561 / 250000000000 : ℝ)
  | 2 => (-2423582447 / 100000000000 : ℝ)
  | 3 => (-1221162657 / 50000000000 : ℝ)
  | 4 => (-12305245359 / 500000000000 : ℝ)
  | 5 => (-1239876179 / 50000000000 : ℝ)
  | 6 => (-780760563 / 31250000000 : ℝ)
  | 7 => (-3146365029 / 125000000000 : ℝ)
  | 8 => (-25357256347 / 1000000000000 : ℝ)
  | 9 => (-6385833099 / 250000000000 : ℝ)
  | 10 => (-3216141791 / 125000000000 : ℝ)
  | 11 => (-25914648007 / 1000000000000 : ℝ)
  | 12 => (-26099859213 / 1000000000000 : ℝ)
  | 13 => (-657118841 / 25000000000 : ℝ)
  | 14 => (-13234658449 / 500000000000 : ℝ)
  | 15 => (-26653534511 / 1000000000000 : ℝ)
  | 16 => (-26837391921 / 1000000000000 : ℝ)
  | 17 => (-5404174897 / 200000000000 : ℝ)
  | 18 => (-13601983737 / 500000000000 : ℝ)
  | 19 => (-27386656077 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch028Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((560 : ℝ) + (j.val : ℝ)) / 1600)
      (((560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch028Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch028Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((560 : ℝ) + (j.val : ℝ)) / 1600)
    (((560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch028Neg40WeightLower j.val) (hpThetaShiftOneBatch028Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch028Neg40WeightLower, hpThetaShiftOneBatch028Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch028Neg40_integral_bounds :
    (-161311085759 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-1579503063 / 10000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch028Lower hpThetaJensenCellsBatch028Upper
    hpThetaShiftOneBatch028Neg40WeightLower hpThetaShiftOneBatch028Neg40WeightUpper hpThetaJensenCellsBatch028_bounds hpThetaShiftOneBatch028Neg40_weight_bounds
  have hl : (-161311085759 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch028Lower j * hpThetaShiftOneBatch028Neg40WeightLower j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftOneBatch028Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftOneBatch028Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch028Lower j * hpThetaShiftOneBatch028Neg40WeightUpper j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftOneBatch028Neg40WeightUpper j) / 1600) ≤ (-1579503063 / 10000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftOneBatch028Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (560 : ℝ) / 1600 = 28 / 80 by norm_num,
    show ((560 : ℝ) + 20) / 1600 = (28 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch028Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (27144629 / 8000000000 : ℝ)
  | 1 => (1628079739 / 500000000000 : ℝ)
  | 2 => (3118327497 / 1000000000000 : ℝ)
  | 3 => (1489791507 / 500000000000 : ℝ)
  | 4 => (2839926391 / 1000000000000 : ℝ)
  | 5 => (107974321 / 40000000000 : ℝ)
  | 6 => (127893917 / 50000000000 : ℝ)
  | 7 => (1207743897 / 500000000000 : ℝ)
  | 8 => (3635499 / 1600000000 : ℝ)
  | 9 => (2127976103 / 1000000000000 : ℝ)
  | 10 => (198285603 / 100000000000 : ℝ)
  | 11 => (45920681 / 25000000000 : ℝ)
  | 12 => (1689890347 / 1000000000000 : ℝ)
  | 13 => (771023 / 500000000 : ℝ)
  | 14 => (1393294877 / 1000000000000 : ℝ)
  | 15 => (1243637689 / 1000000000000 : ℝ)
  | 16 => (1093075181 / 1000000000000 : ℝ)
  | 17 => (941608129 / 1000000000000 : ℝ)
  | 18 => (789237341 / 1000000000000 : ℝ)
  | 19 => (635963659 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch028Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (882271159 / 250000000000 : ℝ)
  | 1 => (1696539313 / 500000000000 : ℝ)
  | 2 => (3256159479 / 1000000000000 : ℝ)
  | 3 => (1559163749 / 500000000000 : ℝ)
  | 4 => (595916603 / 200000000000 : ℝ)
  | 5 => (354990799 / 125000000000 : ℝ)
  | 6 => (1349679013 / 500000000000 : ℝ)
  | 7 => (2557878341 / 1000000000000 : ℝ)
  | 8 => (483097559 / 200000000000 : ℝ)
  | 9 => (568046719 / 250000000000 : ℝ)
  | 10 => (265997013 / 125000000000 : ℝ)
  | 11 => (1982856031 / 1000000000000 : ℝ)
  | 12 => (1836827241 / 1000000000000 : ℝ)
  | 13 => (422472587 / 250000000000 : ℝ)
  | 14 => (1542046001 / 1000000000000 : ℝ)
  | 15 => (696647439 / 500000000000 : ℝ)
  | 16 => (124363769 / 100000000000 : ℝ)
  | 17 => (546537591 / 500000000000 : ℝ)
  | 18 => (94160813 / 100000000000 : ℝ)
  | 19 => (394618671 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch028Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((560 : ℝ) + (j.val : ℝ)) / 1600)
      (((560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch028Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch028Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((560 : ℝ) + (j.val : ℝ)) / 1600)
    (((560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch028Neg20WeightLower j.val) (hpThetaShiftOneBatch028Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch028Neg20WeightLower, hpThetaShiftOneBatch028Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch028Neg20_integral_bounds :
    (3182924023 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (28 / 80 : ℝ) ((28 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (1726592511 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch028Lower hpThetaJensenCellsBatch028Upper
    hpThetaShiftOneBatch028Neg20WeightLower hpThetaShiftOneBatch028Neg20WeightUpper hpThetaJensenCellsBatch028_bounds hpThetaShiftOneBatch028Neg20_weight_bounds
  have hl : (3182924023 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch028Lower j * hpThetaShiftOneBatch028Neg20WeightLower j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftOneBatch028Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftOneBatch028Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch028Lower j * hpThetaShiftOneBatch028Neg20WeightUpper j)
        (hpThetaJensenCellsBatch028Upper j * hpThetaShiftOneBatch028Neg20WeightUpper j) / 1600) ≤ (1726592511 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch028Lower, hpThetaJensenCellsBatch028Upper,
      hpThetaShiftOneBatch028Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (560 : ℝ) / 1600 = 28 / 80 by norm_num,
    show ((560 : ℝ) + 20) / 1600 = (28 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch028Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch028Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch028Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch028Neg20_integral_bounds
end HodgeProofHP
