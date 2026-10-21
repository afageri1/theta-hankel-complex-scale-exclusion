/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch047

/-! Exact signed weight and batch integral certificates, batch 47 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch047Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-198515900307 / 200000000000 : ℝ)
  | 1 => (-1011509753727 / 1000000000000 : ℝ)
  | 2 => (-257667628937 / 250000000000 : ℝ)
  | 3 => (-131257980001 / 125000000000 : ℝ)
  | 4 => (-1069691792649 / 1000000000000 : ℝ)
  | 5 => (-68097278351 / 62500000000 : ℝ)
  | 6 => (-1109659916721 / 1000000000000 : ℝ)
  | 7 => (-282501072429 / 250000000000 : ℝ)
  | 8 => (-287647923589 / 250000000000 : ℝ)
  | 9 => (-292856066619 / 250000000000 : ℝ)
  | 10 => (-1192504156053 / 1000000000000 : ℝ)
  | 11 => (-606916763639 / 500000000000 : ℝ)
  | 12 => (-308853639657 / 250000000000 : ℝ)
  | 13 => (-1257249442933 / 1000000000000 : ℝ)
  | 14 => (-159917548431 / 125000000000 : ℝ)
  | 15 => (-1301689613923 / 1000000000000 : ℝ)
  | 16 => (-662149679337 / 500000000000 : ℝ)
  | 17 => (-1347171872653 / 1000000000000 : ℝ)
  | 18 => (-17128867769 / 12500000000 : ℝ)
  | 19 => (-278742857143 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch047Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-121734715053 / 125000000000 : ℝ)
  | 1 => (-496289750767 / 500000000000 : ℝ)
  | 2 => (-505754876863 / 500000000000 : ℝ)
  | 3 => (-1030670515747 / 1000000000000 : ℝ)
  | 4 => (-1050063840007 / 1000000000000 : ℝ)
  | 5 => (-133711474081 / 125000000000 : ℝ)
  | 6 => (-217911290723 / 200000000000 : ℝ)
  | 7 => (-13870748959 / 12500000000 : ℝ)
  | 8 => (-226000857943 / 200000000000 : ℝ)
  | 9 => (-230118338871 / 200000000000 : ℝ)
  | 10 => (-46856970659 / 40000000000 : ℝ)
  | 11 => (-298126039013 / 250000000000 : ℝ)
  | 12 => (-1213833527277 / 1000000000000 : ℝ)
  | 13 => (-1235414558627 / 1000000000000 : ℝ)
  | 14 => (-314312360733 / 250000000000 : ℝ)
  | 15 => (-1279340387447 / 1000000000000 : ℝ)
  | 16 => (-650844806961 / 500000000000 : ℝ)
  | 17 => (-1324299358673 / 1000000000000 : ℝ)
  | 18 => (-336792968163 / 250000000000 : ℝ)
  | 19 => (-1370309421519 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch047Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((940 : ℝ) + (j.val : ℝ)) / 1600)
      (((940 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch047Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch047Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((940 : ℝ) + (j.val : ℝ)) / 1600)
    (((940 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch047Neg100WeightLower j.val) (hpThetaShiftOneBatch047Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch047Neg100WeightLower, hpThetaShiftOneBatch047Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch047Neg100_integral_bounds :
    (-489177213069 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-58959468149 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (940 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch047Lower hpThetaJensenCellsBatch047Upper
    hpThetaShiftOneBatch047Neg100WeightLower hpThetaShiftOneBatch047Neg100WeightUpper hpThetaJensenCellsBatch047_bounds hpThetaShiftOneBatch047Neg100_weight_bounds
  have hl : (-489177213069 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch047Lower j * hpThetaShiftOneBatch047Neg100WeightLower j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftOneBatch047Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftOneBatch047Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch047Lower j * hpThetaShiftOneBatch047Neg100WeightUpper j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftOneBatch047Neg100WeightUpper j) / 1600) ≤ (-58959468149 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftOneBatch047Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (940 : ℝ) / 1600 = 47 / 80 by norm_num,
    show ((940 : ℝ) + 20) / 1600 = (47 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch047Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (51975977871 / 200000000000 : ℝ)
  | 1 => (129987120867 / 500000000000 : ℝ)
  | 2 => (260042749759 / 1000000000000 : ℝ)
  | 3 => (13004252093 / 50000000000 : ℝ)
  | 4 => (13004473829 / 50000000000 : ℝ)
  | 5 => (10402034423 / 40000000000 : ℝ)
  | 6 => (51996902273 / 200000000000 : ℝ)
  | 7 => (259890041793 / 1000000000000 : ℝ)
  | 8 => (259767061531 / 1000000000000 : ℝ)
  | 9 => (259615177067 / 1000000000000 : ℝ)
  | 10 => (129716995841 / 500000000000 : ℝ)
  | 11 => (51844621087 / 200000000000 : ℝ)
  | 12 => (258982115147 / 1000000000000 : ℝ)
  | 13 => (12935530719 / 50000000000 : ℝ)
  | 14 => (258408193421 / 1000000000000 : ℝ)
  | 15 => (51614887853 / 200000000000 : ℝ)
  | 16 => (128854467797 / 500000000000 : ℝ)
  | 17 => (257311262763 / 1000000000000 : ℝ)
  | 18 => (12844049889 / 50000000000 : ℝ)
  | 19 => (51283542857 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch047Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (51994848347 / 200000000000 : ℝ)
  | 1 => (812633593 / 3125000000 : ℝ)
  | 2 => (260085041861 / 1000000000000 : ℝ)
  | 3 => (52020148677 / 200000000000 : ℝ)
  | 4 => (130050514229 / 500000000000 : ℝ)
  | 5 => (260089476581 / 1000000000000 : ℝ)
  | 6 => (8126589393 / 31250000000 : ℝ)
  | 7 => (129992255683 / 500000000000 : ℝ)
  | 8 => (129945020897 / 500000000000 : ℝ)
  | 9 => (64941765383 / 250000000000 : ℝ)
  | 10 => (64903794267 / 250000000000 : ℝ)
  | 11 => (259433991683 / 1000000000000 : ℝ)
  | 12 => (64805776359 / 250000000000 : ℝ)
  | 13 => (64745528787 / 250000000000 : ℝ)
  | 14 => (258710614381 / 1000000000000 : ℝ)
  | 15 => (129204096711 / 500000000000 : ℝ)
  | 16 => (129037219633 / 500000000000 : ℝ)
  | 17 => (51541787119 / 200000000000 : ℝ)
  | 18 => (64327815691 / 250000000000 : ℝ)
  | 19 => (256880997781 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch047Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((940 : ℝ) + (j.val : ℝ)) / 1600)
      (((940 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch047Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch047Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((940 : ℝ) + (j.val : ℝ)) / 1600)
    (((940 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch047Neg65WeightLower j.val) (hpThetaShiftOneBatch047Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch047Neg65WeightLower, hpThetaShiftOneBatch047Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch047Neg65_integral_bounds :
    (4220325629 / 40000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (5377964169 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (940 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch047Lower hpThetaJensenCellsBatch047Upper
    hpThetaShiftOneBatch047Neg65WeightLower hpThetaShiftOneBatch047Neg65WeightUpper hpThetaJensenCellsBatch047_bounds hpThetaShiftOneBatch047Neg65_weight_bounds
  have hl : (4220325629 / 40000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch047Lower j * hpThetaShiftOneBatch047Neg65WeightLower j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftOneBatch047Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftOneBatch047Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch047Lower j * hpThetaShiftOneBatch047Neg65WeightUpper j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftOneBatch047Neg65WeightUpper j) / 1600) ≤ (5377964169 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftOneBatch047Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (940 : ℝ) / 1600 = 47 / 80 by norm_num,
    show ((940 : ℝ) + 20) / 1600 = (47 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch047Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (85355758601 / 1000000000000 : ℝ)
  | 1 => (86553475193 / 1000000000000 : ℝ)
  | 2 => (17551392951 / 200000000000 : ℝ)
  | 3 => (88966211107 / 1000000000000 : ℝ)
  | 4 => (90181197623 / 1000000000000 : ℝ)
  | 5 => (11425238403 / 125000000000 : ℝ)
  | 6 => (741026579 / 8000000000 : ℝ)
  | 7 => (93860425083 / 1000000000000 : ℝ)
  | 8 => (2971818653 / 31250000000 : ℝ)
  | 9 => (24085404723 / 250000000000 : ℝ)
  | 10 => (24397667921 / 250000000000 : ℝ)
  | 11 => (9884533541 / 100000000000 : ℝ)
  | 12 => (50052794867 / 500000000000 : ℝ)
  | 13 => (1267142673 / 12500000000 : ℝ)
  | 14 => (102642786431 / 1000000000000 : ℝ)
  | 15 => (2597992143 / 25000000000 : ℝ)
  | 16 => (52601044717 / 500000000000 : ℝ)
  | 17 => (53244987403 / 500000000000 : ℝ)
  | 18 => (10778331857 / 100000000000 : ℝ)
  | 19 => (109082096963 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch047Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (43276737597 / 500000000000 : ℝ)
  | 1 => (21939241189 / 250000000000 : ℝ)
  | 2 => (22241552777 / 250000000000 : ℝ)
  | 3 => (11272649703 / 125000000000 : ℝ)
  | 4 => (3656076289 / 40000000000 : ℝ)
  | 5 => (11578540297 / 125000000000 : ℝ)
  | 6 => (23465106271 / 250000000000 : ℝ)
  | 7 => (95098196897 / 1000000000000 : ℝ)
  | 8 => (96341618893 / 1000000000000 : ℝ)
  | 9 => (19518134337 / 200000000000 : ℝ)
  | 10 => (98845335411 / 1000000000000 : ℝ)
  | 11 => (20021117947 / 200000000000 : ℝ)
  | 12 => (101371413841 / 1000000000000 : ℝ)
  | 13 => (801896769 / 7812500000 : ℝ)
  | 14 => (103919685721 / 1000000000000 : ℝ)
  | 15 => (21040417887 / 200000000000 : ℝ)
  | 16 => (106489974807 / 1000000000000 : ℝ)
  | 17 => (107783318571 / 1000000000000 : ℝ)
  | 18 => (27270524241 / 250000000000 : ℝ)
  | 19 => (22077257143 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch047Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((940 : ℝ) + (j.val : ℝ)) / 1600)
      (((940 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch047Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch047Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((940 : ℝ) + (j.val : ℝ)) / 1600)
    (((940 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch047Neg40WeightLower j.val) (hpThetaShiftOneBatch047Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch047Neg40WeightLower, hpThetaShiftOneBatch047Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch047Neg40_integral_bounds :
    (491987551 / 12500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (10153466467 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (940 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch047Lower hpThetaJensenCellsBatch047Upper
    hpThetaShiftOneBatch047Neg40WeightLower hpThetaShiftOneBatch047Neg40WeightUpper hpThetaJensenCellsBatch047_bounds hpThetaShiftOneBatch047Neg40_weight_bounds
  have hl : (491987551 / 12500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch047Lower j * hpThetaShiftOneBatch047Neg40WeightLower j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftOneBatch047Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftOneBatch047Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch047Lower j * hpThetaShiftOneBatch047Neg40WeightUpper j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftOneBatch047Neg40WeightUpper j) / 1600) ≤ (10153466467 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftOneBatch047Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (940 : ℝ) / 1600 = 47 / 80 by norm_num,
    show ((940 : ℝ) + 20) / 1600 = (47 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch047Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-79592692317 / 1000000000000 : ℝ)
  | 1 => (-7970779811 / 100000000000 : ℝ)
  | 2 => (-79820895509 / 1000000000000 : ℝ)
  | 3 => (-79931969593 / 1000000000000 : ℝ)
  | 4 => (-10005125677 / 125000000000 : ℝ)
  | 5 => (-80147988009 / 1000000000000 : ℝ)
  | 6 => (-80252902377 / 1000000000000 : ℝ)
  | 7 => (-160711467 / 2000000000 : ℝ)
  | 8 => (-16091293267 / 200000000000 : ℝ)
  | 9 => (-80555085813 / 1000000000000 : ℝ)
  | 10 => (-40325788421 / 500000000000 : ℝ)
  | 11 => (-80745924309 / 1000000000000 : ℝ)
  | 12 => (-5052382067 / 62500000000 : ℝ)
  | 13 => (-20232031993 / 250000000000 : ℝ)
  | 14 => (-40507976911 / 500000000000 : ℝ)
  | 15 => (-16220315083 / 200000000000 : ℝ)
  | 16 => (-81184977521 / 1000000000000 : ℝ)
  | 17 => (-10158268111 / 125000000000 : ℝ)
  | 18 => (-40672531121 / 500000000000 : ℝ)
  | 19 => (-40710857143 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch047Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-79475593021 / 1000000000000 : ℝ)
  | 1 => (-19898173079 / 250000000000 : ℝ)
  | 2 => (-79707798109 / 1000000000000 : ℝ)
  | 3 => (-19955223877 / 250000000000 : ℝ)
  | 4 => (-9991496199 / 125000000000 : ℝ)
  | 5 => (-16008201083 / 200000000000 : ℝ)
  | 6 => (-10018498501 / 125000000000 : ℝ)
  | 7 => (-10031612797 / 125000000000 : ℝ)
  | 8 => (-80355733499 / 1000000000000 : ℝ)
  | 9 => (-40228233167 / 500000000000 : ℝ)
  | 10 => (-20138771453 / 250000000000 : ℝ)
  | 11 => (-80651576841 / 1000000000000 : ℝ)
  | 12 => (-20186481077 / 250000000000 : ℝ)
  | 13 => (-80838113071 / 1000000000000 : ℝ)
  | 14 => (-80928127971 / 1000000000000 : ℝ)
  | 15 => (-81015953821 / 1000000000000 : ℝ)
  | 16 => (-40550787707 / 500000000000 : ℝ)
  | 17 => (-1014812219 / 12500000000 : ℝ)
  | 18 => (-81266144887 / 1000000000000 : ℝ)
  | 19 => (-81345062241 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch047Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((940 : ℝ) + (j.val : ℝ)) / 1600)
      (((940 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch047Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch047Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((940 : ℝ) + (j.val : ℝ)) / 1600)
    (((940 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch047Neg20WeightLower j.val) (hpThetaShiftOneBatch047Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch047Neg20WeightLower, hpThetaShiftOneBatch047Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch047Neg20_integral_bounds :
    (-33410532903 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (47 / 80 : ℝ) ((47 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-3275717723 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (940 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch047Lower hpThetaJensenCellsBatch047Upper
    hpThetaShiftOneBatch047Neg20WeightLower hpThetaShiftOneBatch047Neg20WeightUpper hpThetaJensenCellsBatch047_bounds hpThetaShiftOneBatch047Neg20_weight_bounds
  have hl : (-33410532903 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch047Lower j * hpThetaShiftOneBatch047Neg20WeightLower j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftOneBatch047Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftOneBatch047Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch047Lower j * hpThetaShiftOneBatch047Neg20WeightUpper j)
        (hpThetaJensenCellsBatch047Upper j * hpThetaShiftOneBatch047Neg20WeightUpper j) / 1600) ≤ (-3275717723 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch047Lower, hpThetaJensenCellsBatch047Upper,
      hpThetaShiftOneBatch047Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (940 : ℝ) / 1600 = 47 / 80 by norm_num,
    show ((940 : ℝ) + 20) / 1600 = (47 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch047Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch047Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch047Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch047Neg20_integral_bounds
end HodgeProofHP
