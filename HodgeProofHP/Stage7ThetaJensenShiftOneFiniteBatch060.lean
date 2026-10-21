/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch060

/-! Exact signed weight and batch integral certificates, batch 60 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch060Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-11463363197071 / 500000000000 : ℝ)
  | 1 => (-11564809601647 / 500000000000 : ℝ)
  | 2 => (-23333985296049 / 1000000000000 : ℝ)
  | 3 => (-23539833381607 / 1000000000000 : ℝ)
  | 4 => (-1187358610513 / 50000000000 : ℝ)
  | 5 => (-2994501321693 / 125000000000 : ℝ)
  | 6 => (-377599332881 / 15625000000 : ℝ)
  | 7 => (-97512885109 / 4000000000 : ℝ)
  | 8 => (-12295805704151 / 500000000000 : ℝ)
  | 9 => (-12403268327773 / 500000000000 : ℝ)
  | 10 => (-25023006018981 / 1000000000000 : ℝ)
  | 11 => (-5048205708151 / 200000000000 : ℝ)
  | 12 => (-795644165791 / 31250000000 : ℝ)
  | 13 => (-401277647493 / 15625000000 : ℝ)
  | 14 => (-1619031632061 / 62500000000 : ℝ)
  | 15 => (-6532208134461 / 250000000000 : ℝ)
  | 16 => (-2635475796933 / 100000000000 : ℝ)
  | 17 => (-3322786463209 / 125000000000 : ℝ)
  | 18 => (-3351430386041 / 125000000000 : ℝ)
  | 19 => (-5408444300427 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch060Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-11362649100167 / 500000000000 : ℝ)
  | 1 => (-22926726394141 / 1000000000000 : ℝ)
  | 2 => (-23129619203293 / 1000000000000 : ℝ)
  | 3 => (-1458374081003 / 62500000000 : ℝ)
  | 4 => (-11769916690803 / 500000000000 : ℝ)
  | 5 => (-23747172210259 / 1000000000000 : ℝ)
  | 6 => (-23956010573543 / 1000000000000 : ℝ)
  | 7 => (-24166357304383 / 1000000000000 : ℝ)
  | 8 => (-24378221277249 / 1000000000000 : ℝ)
  | 9 => (-24591611408301 / 1000000000000 : ℝ)
  | 10 => (-4961307331109 / 200000000000 : ℝ)
  | 11 => (-1251150300949 / 50000000000 : ℝ)
  | 12 => (-12620514270377 / 500000000000 : ℝ)
  | 13 => (-25460613305311 / 1000000000000 : ℝ)
  | 14 => (-25681769439551 / 1000000000000 : ℝ)
  | 15 => (-1036180244519 / 40000000000 : ℝ)
  | 16 => (-26128832537843 / 1000000000000 : ℝ)
  | 17 => (-26354757969329 / 1000000000000 : ℝ)
  | 18 => (-26582291705671 / 1000000000000 : ℝ)
  | 19 => (-26811443088327 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch060Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1200 : ℝ) + (j.val : ℝ)) / 1600)
      (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch060Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch060Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1200 : ℝ) + (j.val : ℝ)) / 1600)
    (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch060Neg100WeightLower j.val) (hpThetaShiftOneBatch060Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch060Neg100WeightLower, hpThetaShiftOneBatch060Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch060Neg100_integral_bounds :
    (-431000058293 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-104345069981 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch060Lower hpThetaJensenCellsBatch060Upper
    hpThetaShiftOneBatch060Neg100WeightLower hpThetaShiftOneBatch060Neg100WeightUpper hpThetaJensenCellsBatch060_bounds hpThetaShiftOneBatch060Neg100_weight_bounds
  have hl : (-431000058293 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch060Lower j * hpThetaShiftOneBatch060Neg100WeightLower j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftOneBatch060Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftOneBatch060Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch060Lower j * hpThetaShiftOneBatch060Neg100WeightUpper j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftOneBatch060Neg100WeightUpper j) / 1600) ≤ (-104345069981 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftOneBatch060Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1200 : ℝ) / 1600 = 60 / 80 by norm_num,
    show ((1200 : ℝ) + 20) / 1600 = (60 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch060Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-245847514033 / 100000000000 : ℝ)
  | 1 => (-62267112917 / 25000000000 : ℝ)
  | 2 => (-78849532643 / 31250000000 : ℝ)
  | 3 => (-1277989348663 / 500000000000 : ℝ)
  | 4 => (-2589067458409 / 1000000000000 : ℝ)
  | 5 => (-2622453321517 / 1000000000000 : ℝ)
  | 6 => (-2656138290589 / 1000000000000 : ℝ)
  | 7 => (-1345062189927 / 500000000000 : ℝ)
  | 8 => (-2724413613869 / 1000000000000 : ℝ)
  | 9 => (-1379504013781 / 500000000000 : ℝ)
  | 10 => (-349238708283 / 125000000000 : ℝ)
  | 11 => (-2829120585757 / 1000000000000 : ℝ)
  | 12 => (-286464285231 / 100000000000 : ℝ)
  | 13 => (-1450239271359 / 500000000000 : ℝ)
  | 14 => (-587325948869 / 200000000000 : ℝ)
  | 15 => (-1486549277581 / 500000000000 : ℝ)
  | 16 => (-752471770947 / 250000000000 : ℝ)
  | 17 => (-304699744953 / 100000000000 : ℝ)
  | 18 => (-1542215891213 / 500000000000 : ℝ)
  | 19 => (-39027402791 / 12500000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch060Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-606638738087 / 250000000000 : ℝ)
  | 1 => (-2458475140329 / 1000000000000 : ℝ)
  | 2 => (-2490684516679 / 1000000000000 : ℝ)
  | 3 => (-100927401783 / 40000000000 : ℝ)
  | 4 => (-102239147893 / 40000000000 : ℝ)
  | 5 => (-323633432301 / 125000000000 : ℝ)
  | 6 => (-655613330379 / 250000000000 : ℝ)
  | 7 => (-664034572647 / 250000000000 : ℝ)
  | 8 => (-2690124379853 / 1000000000000 : ℝ)
  | 9 => (-681103403467 / 250000000000 : ℝ)
  | 10 => (-2759008027561 / 1000000000000 : ℝ)
  | 11 => (-2793909666263 / 1000000000000 : ℝ)
  | 12 => (-707280146439 / 250000000000 : ℝ)
  | 13 => (-2864642852309 / 1000000000000 : ℝ)
  | 14 => (-2900478542717 / 1000000000000 : ℝ)
  | 15 => (-367078718043 / 125000000000 : ℝ)
  | 16 => (-2973098555161 / 1000000000000 : ℝ)
  | 17 => (-3009887083787 / 1000000000000 : ℝ)
  | 18 => (-3046997449529 / 1000000000000 : ℝ)
  | 19 => (-123377271297 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch060Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1200 : ℝ) + (j.val : ℝ)) / 1600)
      (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch060Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch060Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1200 : ℝ) + (j.val : ℝ)) / 1600)
    (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch060Neg65WeightLower j.val) (hpThetaShiftOneBatch060Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch060Neg65WeightLower, hpThetaShiftOneBatch060Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch060Neg65_integral_bounds :
    (-23988281591 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-9255828373 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch060Lower hpThetaJensenCellsBatch060Upper
    hpThetaShiftOneBatch060Neg65WeightLower hpThetaShiftOneBatch060Neg65WeightUpper hpThetaJensenCellsBatch060_bounds hpThetaShiftOneBatch060Neg65_weight_bounds
  have hl : (-23988281591 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch060Lower j * hpThetaShiftOneBatch060Neg65WeightLower j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftOneBatch060Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftOneBatch060Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch060Lower j * hpThetaShiftOneBatch060Neg65WeightUpper j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftOneBatch060Neg65WeightUpper j) / 1600) ≤ (-9255828373 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftOneBatch060Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1200 : ℝ) / 1600 = 60 / 80 by norm_num,
    show ((1200 : ℝ) + 20) / 1600 = (60 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch060Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (211251395089 / 500000000000 : ℝ)
  | 1 => (105645457297 / 250000000000 : ℝ)
  | 2 => (422634599393 / 1000000000000 : ℝ)
  | 3 => (52832519443 / 125000000000 : ℝ)
  | 4 => (211316173897 / 500000000000 : ℝ)
  | 5 => (422577083827 / 1000000000000 : ℝ)
  | 6 => (211247030991 / 500000000000 : ℝ)
  | 7 => (13199468083 / 31250000000 : ℝ)
  | 8 => (422243528297 / 1000000000000 : ℝ)
  | 9 => (211037701699 / 500000000000 : ℝ)
  | 10 => (210939147241 / 500000000000 : ℝ)
  | 11 => (421651890103 / 1000000000000 : ℝ)
  | 12 => (105348969207 / 250000000000 : ℝ)
  | 13 => (105277484809 / 250000000000 : ℝ)
  | 14 => (13149804997 / 31250000000 : ℝ)
  | 15 => (420447019401 / 1000000000000 : ℝ)
  | 16 => (420069396281 / 1000000000000 : ℝ)
  | 17 => (419660567071 / 1000000000000 : ℝ)
  | 18 => (419220206263 / 1000000000000 : ℝ)
  | 19 => (104686996577 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch060Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (422581829189 / 1000000000000 : ℝ)
  | 1 => (211317299697 / 500000000000 : ℝ)
  | 2 => (422660806809 / 1000000000000 : ℝ)
  | 3 => (422664339351 / 1000000000000 : ℝ)
  | 4 => (84532031109 / 200000000000 : ℝ)
  | 5 => (84526469559 / 200000000000 : ℝ)
  | 6 => (105644270957 / 250000000000 : ℝ)
  | 7 => (422494061983 / 1000000000000 : ℝ)
  | 8 => (422382978657 / 1000000000000 : ℝ)
  | 9 => (211121764149 / 500000000000 : ℝ)
  | 10 => (422075403399 / 1000000000000 : ℝ)
  | 11 => (421878294483 / 1000000000000 : ℝ)
  | 12 => (52706486263 / 125000000000 : ℝ)
  | 13 => (421395876829 / 1000000000000 : ℝ)
  | 14 => (421109939237 / 1000000000000 : ℝ)
  | 15 => (84158751981 / 200000000000 : ℝ)
  | 16 => (210223509701 / 500000000000 : ℝ)
  | 17 => (210034698141 / 500000000000 : ℝ)
  | 18 => (13114392721 / 31250000000 : ℝ)
  | 19 => (52402525783 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch060Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1200 : ℝ) + (j.val : ℝ)) / 1600)
      (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch060Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch060Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1200 : ℝ) + (j.val : ℝ)) / 1600)
    (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch060Neg40WeightLower j.val) (hpThetaShiftOneBatch060Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch060Neg40WeightLower, hpThetaShiftOneBatch060Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch060Neg40_integral_bounds :
    (1429507929 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (7320126131 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch060Lower hpThetaJensenCellsBatch060Upper
    hpThetaShiftOneBatch060Neg40WeightLower hpThetaShiftOneBatch060Neg40WeightUpper hpThetaJensenCellsBatch060_bounds hpThetaShiftOneBatch060Neg40_weight_bounds
  have hl : (1429507929 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch060Lower j * hpThetaShiftOneBatch060Neg40WeightLower j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftOneBatch060Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftOneBatch060Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch060Lower j * hpThetaShiftOneBatch060Neg40WeightUpper j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftOneBatch060Neg40WeightUpper j) / 1600) ≤ (7320126131 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftOneBatch060Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1200 : ℝ) / 1600 = 60 / 80 by norm_num,
    show ((1200 : ℝ) + 20) / 1600 = (60 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch060Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2275739397 / 1000000000000 : ℝ)
  | 1 => (3194664613 / 1000000000000 : ℝ)
  | 2 => (4119345159 / 1000000000000 : ℝ)
  | 3 => (2524894909 / 500000000000 : ℝ)
  | 4 => (2993003637 / 500000000000 : ℝ)
  | 5 => (1385601223 / 200000000000 : ℝ)
  | 6 => (7875794829 / 1000000000000 : ℝ)
  | 7 => (1765876361 / 200000000000 : ℝ)
  | 8 => (2447193833 / 250000000000 : ℝ)
  | 9 => (10753983597 / 1000000000000 : ℝ)
  | 10 => (5862507343 / 500000000000 : ℝ)
  | 11 => (6350938291 / 500000000000 : ℝ)
  | 12 => (6842288583 / 500000000000 : ℝ)
  | 13 => (14673124213 / 1000000000000 : ℝ)
  | 14 => (979220337 / 62500000000 : ℝ)
  | 15 => (16667788271 / 1000000000000 : ℝ)
  | 16 => (3534784061 / 200000000000 : ℝ)
  | 17 => (9342964423 / 500000000000 : ℝ)
  | 18 => (1231488821 / 62500000000 : ℝ)
  | 19 => (5181901077 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch060Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1597332307 / 500000000000 : ℝ)
  | 1 => (102983629 / 25000000000 : ℝ)
  | 2 => (5049789819 / 1000000000000 : ℝ)
  | 3 => (239440291 / 40000000000 : ℝ)
  | 4 => (1732001529 / 250000000000 : ℝ)
  | 5 => (787579483 / 100000000000 : ℝ)
  | 6 => (4414690903 / 500000000000 : ℝ)
  | 7 => (9788775333 / 1000000000000 : ℝ)
  | 8 => (5376991799 / 500000000000 : ℝ)
  | 9 => (11725014687 / 1000000000000 : ℝ)
  | 10 => (12701876583 / 1000000000000 : ℝ)
  | 11 => (13684577167 / 1000000000000 : ℝ)
  | 12 => (7336562107 / 500000000000 : ℝ)
  | 13 => (15667525393 / 1000000000000 : ℝ)
  | 14 => (1041736767 / 62500000000 : ℝ)
  | 15 => (8836960153 / 500000000000 : ℝ)
  | 16 => (18685928847 / 1000000000000 : ℝ)
  | 17 => (19703821137 / 1000000000000 : ℝ)
  | 18 => (20727604309 / 1000000000000 : ℝ)
  | 19 => (21757285387 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch060Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1200 : ℝ) + (j.val : ℝ)) / 1600)
      (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch060Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch060Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1200 : ℝ) + (j.val : ℝ)) / 1600)
    (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch060Neg20WeightLower j.val) (hpThetaShiftOneBatch060Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch060Neg20WeightLower, hpThetaShiftOneBatch060Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch060Neg20_integral_bounds :
    (184061089 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (205287929 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch060Lower hpThetaJensenCellsBatch060Upper
    hpThetaShiftOneBatch060Neg20WeightLower hpThetaShiftOneBatch060Neg20WeightUpper hpThetaJensenCellsBatch060_bounds hpThetaShiftOneBatch060Neg20_weight_bounds
  have hl : (184061089 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch060Lower j * hpThetaShiftOneBatch060Neg20WeightLower j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftOneBatch060Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftOneBatch060Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch060Lower j * hpThetaShiftOneBatch060Neg20WeightUpper j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftOneBatch060Neg20WeightUpper j) / 1600) ≤ (205287929 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftOneBatch060Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1200 : ℝ) / 1600 = 60 / 80 by norm_num,
    show ((1200 : ℝ) + 20) / 1600 = (60 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch060Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch060Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch060Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch060Neg20_integral_bounds
end HodgeProofHP
