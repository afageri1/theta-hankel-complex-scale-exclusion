/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch034

/-! Exact signed weight and batch integral certificates, batch 34 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch034Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (127200131 / 200000000000 : ℝ)
  | 1 => (326105497 / 500000000000 : ℝ)
  | 2 => (334300433 / 500000000000 : ℝ)
  | 3 => (685170571 / 1000000000000 : ℝ)
  | 4 => (701920381 / 1000000000000 : ℝ)
  | 5 => (143770109 / 200000000000 : ℝ)
  | 6 => (367980641 / 500000000000 : ℝ)
  | 7 => (150650557 / 200000000000 : ℝ)
  | 8 => (24085163 / 31250000000 : ℝ)
  | 9 => (98547339 / 125000000000 : ℝ)
  | 10 => (403106689 / 500000000000 : ℝ)
  | 11 => (824229291 / 1000000000000 : ℝ)
  | 12 => (168485299 / 200000000000 : ℝ)
  | 13 => (430402503 / 500000000000 : ℝ)
  | 14 => (175872961 / 200000000000 : ℝ)
  | 15 => (898105843 / 1000000000000 : ℝ)
  | 16 => (458514019 / 500000000000 : ℝ)
  | 17 => (468065637 / 500000000000 : ℝ)
  | 18 => (4777077 / 5000000000 : ℝ)
  | 19 => (974880233 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch034Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (130442199 / 200000000000 : ℝ)
  | 1 => (668600867 / 1000000000000 : ℝ)
  | 2 => (171292643 / 250000000000 : ℝ)
  | 3 => (350960191 / 500000000000 : ℝ)
  | 4 => (359425273 / 500000000000 : ℝ)
  | 5 => (735961283 / 1000000000000 : ℝ)
  | 6 => (376626393 / 500000000000 : ℝ)
  | 7 => (770725217 / 1000000000000 : ℝ)
  | 8 => (788378713 / 1000000000000 : ℝ)
  | 9 => (806213379 / 1000000000000 : ℝ)
  | 10 => (206057323 / 250000000000 : ℝ)
  | 11 => (6581457 / 7812500000 : ℝ)
  | 12 => (860805007 / 1000000000000 : ℝ)
  | 13 => (439682403 / 500000000000 : ℝ)
  | 14 => (224526461 / 250000000000 : ℝ)
  | 15 => (917028039 / 1000000000000 : ℝ)
  | 16 => (37445251 / 40000000000 : ℝ)
  | 17 => (955415401 / 1000000000000 : ℝ)
  | 18 => (487440117 / 500000000000 : ℝ)
  | 19 => (497262777 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch034Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((680 : ℝ) + (j.val : ℝ)) / 1600)
      (((680 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch034Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch034Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((680 : ℝ) + (j.val : ℝ)) / 1600)
    (((680 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch034Neg100WeightLower j.val) (hpThetaShiftTwoBatch034Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch034Neg100WeightLower, hpThetaShiftTwoBatch034Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch034Neg100_integral_bounds :
    (50911181 / 20000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (1321122221 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (680 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch034Lower hpThetaJensenCellsBatch034Upper
    hpThetaShiftTwoBatch034Neg100WeightLower hpThetaShiftTwoBatch034Neg100WeightUpper hpThetaJensenCellsBatch034_bounds hpThetaShiftTwoBatch034Neg100_weight_bounds
  have hl : (50911181 / 20000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch034Lower j * hpThetaShiftTwoBatch034Neg100WeightLower j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftTwoBatch034Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftTwoBatch034Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch034Lower j * hpThetaShiftTwoBatch034Neg100WeightUpper j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftTwoBatch034Neg100WeightUpper j) / 1600) ≤ (1321122221 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftTwoBatch034Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (680 : ℝ) / 1600 = 34 / 80 by norm_num,
    show ((680 : ℝ) + 20) / 1600 = (34 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch034Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-286326693 / 500000000000 : ℝ)
  | 1 => (-286156289 / 500000000000 : ℝ)
  | 2 => (-571888627 / 1000000000000 : ℝ)
  | 3 => (-142845097 / 250000000000 : ℝ)
  | 4 => (-570786709 / 1000000000000 : ℝ)
  | 5 => (-570106433 / 1000000000000 : ℝ)
  | 6 => (-569338397 / 1000000000000 : ℝ)
  | 7 => (-56848143 / 100000000000 : ℝ)
  | 8 => (-567534359 / 1000000000000 : ℝ)
  | 9 => (-566496001 / 1000000000000 : ℝ)
  | 10 => (-565365171 / 1000000000000 : ℝ)
  | 11 => (-282070337 / 500000000000 : ℝ)
  | 12 => (-281410657 / 500000000000 : ℝ)
  | 13 => (-561405887 / 1000000000000 : ℝ)
  | 14 => (-559893183 / 1000000000000 : ℝ)
  | 15 => (-558281987 / 1000000000000 : ℝ)
  | 16 => (-278285539 / 500000000000 : ℝ)
  | 17 => (-8668113 / 15625000000 : ℝ)
  | 18 => (-17276413 / 31250000000 : ℝ)
  | 19 => (-110165559 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch034Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-572312577 / 1000000000000 : ℝ)
  | 1 => (-285944313 / 500000000000 : ℝ)
  | 2 => (-571380387 / 1000000000000 : ℝ)
  | 3 => (-142696677 / 250000000000 : ℝ)
  | 4 => (-8907913 / 15625000000 : ℝ)
  | 5 => (-142334599 / 250000000000 : ℝ)
  | 6 => (-568481429 / 1000000000000 : ℝ)
  | 7 => (-283767179 / 500000000000 : ℝ)
  | 8 => (-17703 / 31250000 : ℝ)
  | 9 => (-56536517 / 100000000000 : ℝ)
  | 10 => (-564140673 / 1000000000000 : ℝ)
  | 11 => (-562821313 / 1000000000000 : ℝ)
  | 12 => (-280702943 / 500000000000 : ℝ)
  | 13 => (-279946591 / 500000000000 : ℝ)
  | 14 => (-279140993 / 500000000000 : ℝ)
  | 15 => (-556571077 / 1000000000000 : ℝ)
  | 16 => (-554759231 / 1000000000000 : ℝ)
  | 17 => (-110569043 / 200000000000 : ℝ)
  | 18 => (-275413897 / 500000000000 : ℝ)
  | 19 => (-274352863 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch034Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((680 : ℝ) + (j.val : ℝ)) / 1600)
      (((680 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch034Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch034Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((680 : ℝ) + (j.val : ℝ)) / 1600)
    (((680 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch034Neg65WeightLower j.val) (hpThetaShiftTwoBatch034Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch034Neg65WeightLower, hpThetaShiftTwoBatch034Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch034Neg65_integral_bounds :
    (-1831621797 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-1800476437 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (680 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch034Lower hpThetaJensenCellsBatch034Upper
    hpThetaShiftTwoBatch034Neg65WeightLower hpThetaShiftTwoBatch034Neg65WeightUpper hpThetaJensenCellsBatch034_bounds hpThetaShiftTwoBatch034Neg65_weight_bounds
  have hl : (-1831621797 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch034Lower j * hpThetaShiftTwoBatch034Neg65WeightLower j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftTwoBatch034Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftTwoBatch034Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch034Lower j * hpThetaShiftTwoBatch034Neg65WeightUpper j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftTwoBatch034Neg65WeightUpper j) / 1600) ≤ (-1800476437 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftTwoBatch034Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (680 : ℝ) / 1600 = 34 / 80 by norm_num,
    show ((680 : ℝ) + 20) / 1600 = (34 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch034Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-323446741 / 500000000000 : ℝ)
  | 1 => (-326321603 / 500000000000 : ℝ)
  | 2 => (-26335927 / 40000000000 : ℝ)
  | 3 => (-66415791 / 100000000000 : ℝ)
  | 4 => (-669921929 / 1000000000000 : ℝ)
  | 5 => (-33784487 / 50000000000 : ℝ)
  | 6 => (-681460849 / 1000000000000 : ℝ)
  | 7 => (-343617377 / 500000000000 : ℝ)
  | 8 => (-693010947 / 1000000000000 : ℝ)
  | 9 => (-174697229 / 250000000000 : ℝ)
  | 10 => (-704568139 / 1000000000000 : ℝ)
  | 11 => (-355174047 / 500000000000 : ℝ)
  | 12 => (-89516031 / 125000000000 : ℝ)
  | 13 => (-721908063 / 1000000000000 : ℝ)
  | 14 => (-727686997 / 1000000000000 : ℝ)
  | 15 => (-733464501 / 1000000000000 : ℝ)
  | 16 => (-369620009 / 500000000000 : ℝ)
  | 17 => (-745012987 / 1000000000000 : ℝ)
  | 18 => (-750782841 / 1000000000000 : ℝ)
  | 19 => (-378274503 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch034Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-25645979 / 40000000000 : ℝ)
  | 1 => (-646893481 / 1000000000000 : ℝ)
  | 2 => (-130528641 / 200000000000 : ℝ)
  | 3 => (-329199087 / 500000000000 : ℝ)
  | 4 => (-664157909 / 1000000000000 : ℝ)
  | 5 => (-83740241 / 125000000000 : ℝ)
  | 6 => (-675689739 / 1000000000000 : ℝ)
  | 7 => (-42591303 / 62500000000 : ℝ)
  | 8 => (-687234753 / 1000000000000 : ℝ)
  | 9 => (-346505473 / 500000000000 : ℝ)
  | 10 => (-139757783 / 200000000000 : ℝ)
  | 11 => (-352284069 / 500000000000 : ℝ)
  | 12 => (-710348093 / 1000000000000 : ℝ)
  | 13 => (-716128247 / 1000000000000 : ℝ)
  | 14 => (-360954031 / 500000000000 : ℝ)
  | 15 => (-181921749 / 250000000000 : ℝ)
  | 16 => (-1466929 / 2000000000 : ℝ)
  | 17 => (-739240017 / 1000000000000 : ℝ)
  | 18 => (-372506493 / 500000000000 : ℝ)
  | 19 => (-18769571 / 25000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch034Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((680 : ℝ) + (j.val : ℝ)) / 1600)
      (((680 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch034Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch034Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((680 : ℝ) + (j.val : ℝ)) / 1600)
    (((680 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch034Neg45WeightLower j.val) (hpThetaShiftTwoBatch034Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch034Neg45WeightLower, hpThetaShiftTwoBatch034Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch034Neg45_integral_bounds :
    (-2272415633 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-1110000111 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (680 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch034Lower hpThetaJensenCellsBatch034Upper
    hpThetaShiftTwoBatch034Neg45WeightLower hpThetaShiftTwoBatch034Neg45WeightUpper hpThetaJensenCellsBatch034_bounds hpThetaShiftTwoBatch034Neg45_weight_bounds
  have hl : (-2272415633 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch034Lower j * hpThetaShiftTwoBatch034Neg45WeightLower j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftTwoBatch034Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftTwoBatch034Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch034Lower j * hpThetaShiftTwoBatch034Neg45WeightUpper j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftTwoBatch034Neg45WeightUpper j) / 1600) ≤ (-1110000111 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftTwoBatch034Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (680 : ℝ) / 1600 = 34 / 80 by norm_num,
    show ((680 : ℝ) + 20) / 1600 = (34 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch034Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (120293543 / 1000000000000 : ℝ)
  | 1 => (7264851 / 62500000000 : ℝ)
  | 2 => (28034379 / 250000000000 : ℝ)
  | 3 => (107993089 / 1000000000000 : ℝ)
  | 4 => (12975523 / 125000000000 : ℝ)
  | 5 => (1991413 / 20000000000 : ℝ)
  | 6 => (5955771 / 62500000000 : ℝ)
  | 7 => (90969093 / 1000000000000 : ℝ)
  | 8 => (10825097 / 125000000000 : ℝ)
  | 9 => (20546809 / 250000000000 : ℝ)
  | 10 => (7772833 / 100000000000 : ℝ)
  | 11 => (36611957 / 500000000000 : ℝ)
  | 12 => (17168461 / 250000000000 : ℝ)
  | 13 => (64077981 / 1000000000000 : ℝ)
  | 14 => (7429523 / 125000000000 : ℝ)
  | 15 => (27374157 / 500000000000 : ℝ)
  | 16 => (10002847 / 200000000000 : ℝ)
  | 17 => (4523381 / 100000000000 : ℝ)
  | 18 => (20203453 / 500000000000 : ℝ)
  | 19 => (35533389 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch034Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (31076363 / 250000000000 : ℝ)
  | 1 => (15036693 / 125000000000 : ℝ)
  | 2 => (116237617 / 1000000000000 : ℝ)
  | 3 => (112137517 / 1000000000000 : ℝ)
  | 4 => (10799309 / 100000000000 : ℝ)
  | 5 => (20760837 / 200000000000 : ℝ)
  | 6 => (99570651 / 1000000000000 : ℝ)
  | 7 => (95292337 / 1000000000000 : ℝ)
  | 8 => (45484547 / 500000000000 : ℝ)
  | 9 => (86600777 / 1000000000000 : ℝ)
  | 10 => (82187237 / 1000000000000 : ℝ)
  | 11 => (77728331 / 1000000000000 : ℝ)
  | 12 => (14644783 / 200000000000 : ℝ)
  | 13 => (13734769 / 200000000000 : ℝ)
  | 14 => (32038991 / 500000000000 : ℝ)
  | 15 => (11887237 / 200000000000 : ℝ)
  | 16 => (10949663 / 200000000000 : ℝ)
  | 17 => (12503559 / 250000000000 : ℝ)
  | 18 => (45233811 / 1000000000000 : ℝ)
  | 19 => (40406907 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch034Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((680 : ℝ) + (j.val : ℝ)) / 1600)
      (((680 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch034Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch034Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((680 : ℝ) + (j.val : ℝ)) / 1600)
    (((680 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch034Neg25WeightLower j.val) (hpThetaShiftTwoBatch034Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch034Neg25WeightLower, hpThetaShiftTwoBatch034Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch034Neg25_integral_bounds :
    (256032609 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (34 / 80 : ℝ) ((34 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (274281347 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (680 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch034Lower hpThetaJensenCellsBatch034Upper
    hpThetaShiftTwoBatch034Neg25WeightLower hpThetaShiftTwoBatch034Neg25WeightUpper hpThetaJensenCellsBatch034_bounds hpThetaShiftTwoBatch034Neg25_weight_bounds
  have hl : (256032609 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch034Lower j * hpThetaShiftTwoBatch034Neg25WeightLower j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftTwoBatch034Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftTwoBatch034Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch034Lower j * hpThetaShiftTwoBatch034Neg25WeightUpper j)
        (hpThetaJensenCellsBatch034Upper j * hpThetaShiftTwoBatch034Neg25WeightUpper j) / 1600) ≤ (274281347 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch034Lower, hpThetaJensenCellsBatch034Upper,
      hpThetaShiftTwoBatch034Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (680 : ℝ) / 1600 = 34 / 80 by norm_num,
    show ((680 : ℝ) + 20) / 1600 = (34 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch034Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch034Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch034Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch034Neg25_integral_bounds
end HodgeProofHP
