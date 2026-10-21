/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch032

/-! Exact signed weight and batch integral certificates, batch 32 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch032Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1005291 / 7812500000 : ℝ)
  | 1 => (138191863 / 1000000000000 : ℝ)
  | 2 => (36964513 / 250000000000 : ℝ)
  | 3 => (31535357 / 200000000000 : ℝ)
  | 4 => (6705961 / 40000000000 : ℝ)
  | 5 => (88887861 / 500000000000 : ℝ)
  | 6 => (9402891 / 50000000000 : ℝ)
  | 7 => (24812031 / 125000000000 : ℝ)
  | 8 => (209091929 / 1000000000000 : ℝ)
  | 9 => (54961443 / 250000000000 : ℝ)
  | 10 => (9230347 / 40000000000 : ℝ)
  | 11 => (241831527 / 1000000000000 : ℝ)
  | 12 => (126532601 / 500000000000 : ℝ)
  | 13 => (264460563 / 1000000000000 : ℝ)
  | 14 => (276018459 / 1000000000000 : ℝ)
  | 15 => (17983733 / 62500000000 : ℝ)
  | 16 => (299625193 / 1000000000000 : ℝ)
  | 17 => (19479729 / 62500000000 : ℝ)
  | 18 => (10121623 / 31250000000 : ℝ)
  | 19 => (336274789 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch032Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (17273983 / 125000000000 : ℝ)
  | 1 => (147858053 / 1000000000000 : ℝ)
  | 2 => (78838393 / 500000000000 : ℝ)
  | 3 => (83824513 / 500000000000 : ℝ)
  | 4 => (177775723 / 1000000000000 : ℝ)
  | 5 => (188057821 / 1000000000000 : ℝ)
  | 6 => (198496249 / 1000000000000 : ℝ)
  | 7 => (20909193 / 100000000000 : ℝ)
  | 8 => (219845773 / 1000000000000 : ℝ)
  | 9 => (57689669 / 250000000000 : ℝ)
  | 10 => (30228941 / 125000000000 : ℝ)
  | 11 => (253065203 / 1000000000000 : ℝ)
  | 12 => (66115141 / 250000000000 : ℝ)
  | 13 => (13800923 / 50000000000 : ℝ)
  | 14 => (287739729 / 1000000000000 : ℝ)
  | 15 => (149812597 / 500000000000 : ℝ)
  | 16 => (62335133 / 200000000000 : ℝ)
  | 17 => (323891937 / 1000000000000 : ℝ)
  | 18 => (33627479 / 100000000000 : ℝ)
  | 19 => (10900781 / 31250000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch032Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((640 : ℝ) + (j.val : ℝ)) / 1600)
      (((640 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch032Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch032Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((640 : ℝ) + (j.val : ℝ)) / 1600)
    (((640 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch032Neg100WeightLower j.val) (hpThetaShiftTwoBatch032Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch032Neg100WeightLower, hpThetaShiftTwoBatch032Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch032Neg100_integral_bounds :
    (915290867 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (973934793 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (640 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch032Lower hpThetaJensenCellsBatch032Upper
    hpThetaShiftTwoBatch032Neg100WeightLower hpThetaShiftTwoBatch032Neg100WeightUpper hpThetaJensenCellsBatch032_bounds hpThetaShiftTwoBatch032Neg100_weight_bounds
  have hl : (915290867 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch032Lower j * hpThetaShiftTwoBatch032Neg100WeightLower j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftTwoBatch032Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftTwoBatch032Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch032Lower j * hpThetaShiftTwoBatch032Neg100WeightUpper j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftTwoBatch032Neg100WeightUpper j) / 1600) ≤ (973934793 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftTwoBatch032Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (640 : ℝ) / 1600 = 32 / 80 by norm_num,
    show ((640 : ℝ) + 20) / 1600 = (32 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch032Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-66574303 / 125000000000 : ℝ)
  | 1 => (-534670867 / 1000000000000 : ℝ)
  | 2 => (-536703793 / 1000000000000 : ℝ)
  | 3 => (-269346157 / 500000000000 : ℝ)
  | 4 => (-108127107 / 200000000000 : ℝ)
  | 5 => (-108506511 / 200000000000 : ℝ)
  | 6 => (-108876493 / 200000000000 : ℝ)
  | 7 => (-546184349 / 1000000000000 : ℝ)
  | 8 => (-547937287 / 1000000000000 : ℝ)
  | 9 => (-137410087 / 250000000000 : ℝ)
  | 10 => (-137823149 / 250000000000 : ℝ)
  | 11 => (-552893089 / 1000000000000 : ℝ)
  | 12 => (-138610219 / 250000000000 : ℝ)
  | 13 => (-277967501 / 500000000000 : ℝ)
  | 14 => (-278687251 / 500000000000 : ℝ)
  | 15 => (-69844801 / 125000000000 : ℝ)
  | 16 => (-560085741 / 1000000000000 : ℝ)
  | 17 => (-561355517 / 1000000000000 : ℝ)
  | 18 => (-140641687 / 250000000000 : ℝ)
  | 19 => (-281859217 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch032Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-530475343 / 1000000000000 : ℝ)
  | 1 => (-532594423 / 1000000000000 : ℝ)
  | 2 => (-267335433 / 500000000000 : ℝ)
  | 3 => (-33543987 / 62500000000 : ℝ)
  | 4 => (-538692313 / 1000000000000 : ℝ)
  | 5 => (-270317767 / 500000000000 : ℝ)
  | 6 => (-271266277 / 500000000000 : ℝ)
  | 7 => (-1063247 / 1953125000 : ℝ)
  | 8 => (-136546087 / 250000000000 : ℝ)
  | 9 => (-273968643 / 500000000000 : ℝ)
  | 10 => (-549640347 / 1000000000000 : ℝ)
  | 11 => (-110258519 / 200000000000 : ℝ)
  | 12 => (-17277909 / 31250000000 : ℝ)
  | 13 => (-4435527 / 8000000000 : ℝ)
  | 14 => (-555935001 / 1000000000000 : ℝ)
  | 15 => (-557374501 / 1000000000000 : ℝ)
  | 16 => (-558758407 / 1000000000000 : ℝ)
  | 17 => (-28004287 / 50000000000 : ℝ)
  | 18 => (-140338879 / 250000000000 : ℝ)
  | 19 => (-562566747 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch032Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((640 : ℝ) + (j.val : ℝ)) / 1600)
      (((640 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch032Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch032Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((640 : ℝ) + (j.val : ℝ)) / 1600)
    (((640 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch032Neg65WeightLower j.val) (hpThetaShiftTwoBatch032Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch032Neg65WeightLower, hpThetaShiftTwoBatch032Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch032Neg65_integral_bounds :
    (-141177381 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-22192559 / 10000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (640 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch032Lower hpThetaJensenCellsBatch032Upper
    hpThetaShiftTwoBatch032Neg65WeightLower hpThetaShiftTwoBatch032Neg65WeightUpper hpThetaJensenCellsBatch032_bounds hpThetaShiftTwoBatch032Neg65_weight_bounds
  have hl : (-141177381 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch032Lower j * hpThetaShiftTwoBatch032Neg65WeightLower j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftTwoBatch032Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftTwoBatch032Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch032Lower j * hpThetaShiftTwoBatch032Neg65WeightUpper j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftTwoBatch032Neg65WeightUpper j) / 1600) ≤ (-22192559 / 10000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftTwoBatch032Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (640 : ℝ) / 1600 = 32 / 80 by norm_num,
    show ((640 : ℝ) + 20) / 1600 = (32 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch032Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-213003181 / 500000000000 : ℝ)
  | 1 => (-431217657 / 1000000000000 : ℝ)
  | 2 => (-218224429 / 500000000000 : ℝ)
  | 3 => (-441699701 / 1000000000000 : ℝ)
  | 4 => (-446969911 / 1000000000000 : ℝ)
  | 5 => (-452259213 / 1000000000000 : ℝ)
  | 6 => (-18302693 / 40000000000 : ℝ)
  | 7 => (-11572349 / 25000000000 : ℝ)
  | 8 => (-468238827 / 1000000000000 : ℝ)
  | 9 => (-473601631 / 1000000000000 : ℝ)
  | 10 => (-478982069 / 1000000000000 : ℝ)
  | 11 => (-121094959 / 250000000000 : ℝ)
  | 12 => (-489794621 / 1000000000000 : ℝ)
  | 13 => (-495226107 / 1000000000000 : ℝ)
  | 14 => (-20026959 / 40000000000 : ℝ)
  | 15 => (-506137897 / 1000000000000 : ℝ)
  | 16 => (-511617543 / 1000000000000 : ℝ)
  | 17 => (-517112577 / 1000000000000 : ℝ)
  | 18 => (-8165979 / 15625000000 : ℝ)
  | 19 => (-105629487 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch032Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-210407619 / 500000000000 : ℝ)
  | 1 => (-426006361 / 1000000000000 : ℝ)
  | 2 => (-53902207 / 125000000000 : ℝ)
  | 3 => (-436448857 / 1000000000000 : ℝ)
  | 4 => (-4416997 / 10000000000 : ℝ)
  | 5 => (-44696991 / 100000000000 : ℝ)
  | 6 => (-113064803 / 250000000000 : ℝ)
  | 7 => (-114391831 / 250000000000 : ℝ)
  | 8 => (-462893959 / 1000000000000 : ℝ)
  | 9 => (-234119413 / 500000000000 : ℝ)
  | 10 => (-47360163 / 100000000000 : ℝ)
  | 11 => (-119745517 / 250000000000 : ℝ)
  | 12 => (-96875967 / 200000000000 : ℝ)
  | 13 => (-24489731 / 50000000000 : ℝ)
  | 14 => (-247613053 / 500000000000 : ℝ)
  | 15 => (-250336987 / 500000000000 : ℝ)
  | 16 => (-63267237 / 125000000000 : ℝ)
  | 17 => (-255808771 / 500000000000 : ℝ)
  | 18 => (-2019971 / 3906250000 : ℝ)
  | 19 => (-104524531 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch032Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((640 : ℝ) + (j.val : ℝ)) / 1600)
      (((640 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch032Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch032Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((640 : ℝ) + (j.val : ℝ)) / 1600)
    (((640 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch032Neg45WeightLower j.val) (hpThetaShiftTwoBatch032Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch032Neg45WeightLower, hpThetaShiftTwoBatch032Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch032Neg45_integral_bounds :
    (-488895347 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-952719331 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (640 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch032Lower hpThetaJensenCellsBatch032Upper
    hpThetaShiftTwoBatch032Neg45WeightLower hpThetaShiftTwoBatch032Neg45WeightUpper hpThetaJensenCellsBatch032_bounds hpThetaShiftTwoBatch032Neg45_weight_bounds
  have hl : (-488895347 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch032Lower j * hpThetaShiftTwoBatch032Neg45WeightLower j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftTwoBatch032Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftTwoBatch032Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch032Lower j * hpThetaShiftTwoBatch032Neg45WeightUpper j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftTwoBatch032Neg45WeightUpper j) / 1600) ≤ (-952719331 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftTwoBatch032Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (640 : ℝ) / 1600 = 32 / 80 by norm_num,
    show ((640 : ℝ) + 20) / 1600 = (32 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch032Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (62048289 / 250000000000 : ℝ)
  | 1 => (24576721 / 100000000000 : ℝ)
  | 2 => (15206499 / 62500000000 : ℝ)
  | 3 => (60200823 / 250000000000 : ℝ)
  | 4 => (59566237 / 250000000000 : ℝ)
  | 5 => (235688767 / 1000000000000 : ℝ)
  | 6 => (58268641 / 250000000000 : ℝ)
  | 7 => (230422153 / 1000000000000 : ℝ)
  | 8 => (227731353 / 1000000000000 : ℝ)
  | 9 => (225001979 / 1000000000000 : ℝ)
  | 10 => (4444677 / 20000000000 : ℝ)
  | 11 => (219426783 / 1000000000000 : ℝ)
  | 12 => (216580597 / 1000000000000 : ℝ)
  | 13 => (213695113 / 1000000000000 : ℝ)
  | 14 => (210770149 / 1000000000000 : ℝ)
  | 15 => (25975691 / 125000000000 : ℝ)
  | 16 => (20480107 / 100000000000 : ℝ)
  | 17 => (201756599 / 1000000000000 : ℝ)
  | 18 => (3104249 / 15625000000 : ℝ)
  | 19 => (195546907 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch032Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (250582011 / 1000000000000 : ℝ)
  | 1 => (248193157 / 1000000000000 : ℝ)
  | 2 => (245767211 / 1000000000000 : ℝ)
  | 3 => (48660797 / 200000000000 : ℝ)
  | 4 => (240803293 / 1000000000000 : ℝ)
  | 5 => (238264949 / 1000000000000 : ℝ)
  | 6 => (3682637 / 15625000000 : ℝ)
  | 7 => (46614913 / 200000000000 : ℝ)
  | 8 => (115211077 / 500000000000 : ℝ)
  | 9 => (113865677 / 500000000000 : ℝ)
  | 10 => (11250099 / 50000000000 : ℝ)
  | 11 => (222233851 / 1000000000000 : ℝ)
  | 12 => (6857087 / 31250000000 : ℝ)
  | 13 => (108290299 / 500000000000 : ℝ)
  | 14 => (106847557 / 500000000000 : ℝ)
  | 15 => (4215403 / 20000000000 : ℝ)
  | 16 => (207805529 / 1000000000000 : ℝ)
  | 17 => (204801071 / 1000000000000 : ℝ)
  | 18 => (1008783 / 5000000000 : ℝ)
  | 19 => (198671937 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch032Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((640 : ℝ) + (j.val : ℝ)) / 1600)
      (((640 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch032Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch032Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((640 : ℝ) + (j.val : ℝ)) / 1600)
    (((640 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch032Neg25WeightLower j.val) (hpThetaShiftTwoBatch032Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch032Neg25WeightLower, hpThetaShiftTwoBatch032Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch032Neg25_integral_bounds :
    (181145311 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (32 / 80 : ℝ) ((32 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (232588929 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (640 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch032Lower hpThetaJensenCellsBatch032Upper
    hpThetaShiftTwoBatch032Neg25WeightLower hpThetaShiftTwoBatch032Neg25WeightUpper hpThetaJensenCellsBatch032_bounds hpThetaShiftTwoBatch032Neg25_weight_bounds
  have hl : (181145311 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch032Lower j * hpThetaShiftTwoBatch032Neg25WeightLower j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftTwoBatch032Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftTwoBatch032Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch032Lower j * hpThetaShiftTwoBatch032Neg25WeightUpper j)
        (hpThetaJensenCellsBatch032Upper j * hpThetaShiftTwoBatch032Neg25WeightUpper j) / 1600) ≤ (232588929 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch032Lower, hpThetaJensenCellsBatch032Upper,
      hpThetaShiftTwoBatch032Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (640 : ℝ) / 1600 = 32 / 80 by norm_num,
    show ((640 : ℝ) + 20) / 1600 = (32 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch032Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch032Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch032Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch032Neg25_integral_bounds
end HodgeProofHP
