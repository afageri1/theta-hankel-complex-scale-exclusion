/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch063

/-! Exact signed weight and batch integral certificates, batch 63 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch063Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-19183488787 / 1000000000000 : ℝ)
  | 1 => (-3887630079 / 200000000000 : ℝ)
  | 2 => (-9847856627 / 500000000000 : ℝ)
  | 3 => (-19956205951 / 1000000000000 : ℝ)
  | 4 => (-505491433 / 25000000000 : ℝ)
  | 5 => (-10243048219 / 500000000000 : ℝ)
  | 6 => (-2594444079 / 125000000000 : ℝ)
  | 7 => (-841122219 / 40000000000 : ℝ)
  | 8 => (-21303634793 / 1000000000000 : ℝ)
  | 9 => (-2697790083 / 125000000000 : ℝ)
  | 10 => (-1093207171 / 50000000000 : ℝ)
  | 11 => (-22149133651 / 1000000000000 : ℝ)
  | 12 => (-22437322203 / 1000000000000 : ℝ)
  | 13 => (-4545748037 / 200000000000 : ℝ)
  | 14 => (-11511709483 / 500000000000 : ℝ)
  | 15 => (-11660695089 / 500000000000 : ℝ)
  | 16 => (-23622685723 / 1000000000000 : ℝ)
  | 17 => (-11963668883 / 500000000000 : ℝ)
  | 18 => (-3029422343 / 125000000000 : ℝ)
  | 19 => (-24546841367 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch063Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-18931700081 / 1000000000000 : ℝ)
  | 1 => (-9591744393 / 500000000000 : ℝ)
  | 2 => (-9719075197 / 500000000000 : ℝ)
  | 3 => (-19695713253 / 1000000000000 : ℝ)
  | 4 => (-399124119 / 20000000000 : ℝ)
  | 5 => (-20219657319 / 1000000000000 : ℝ)
  | 6 => (-20486096437 / 1000000000000 : ℝ)
  | 7 => (-20755552631 / 1000000000000 : ℝ)
  | 8 => (-10514027737 / 500000000000 : ℝ)
  | 9 => (-2662954349 / 125000000000 : ℝ)
  | 10 => (-21582320663 / 1000000000000 : ℝ)
  | 11 => (-21864143419 / 1000000000000 : ℝ)
  | 12 => (-442982673 / 20000000000 : ℝ)
  | 13 => (-11218661101 / 500000000000 : ℝ)
  | 14 => (-2841092523 / 125000000000 : ℝ)
  | 15 => (-4604683793 / 200000000000 : ℝ)
  | 16 => (-23321390177 / 1000000000000 : ℝ)
  | 17 => (-11811342861 / 500000000000 : ℝ)
  | 18 => (-4785467553 / 200000000000 : ℝ)
  | 19 => (-24235378743 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch063Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1260 : ℝ) + (j.val : ℝ)) / 1600)
      (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch063Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch063Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1260 : ℝ) + (j.val : ℝ)) / 1600)
    (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch063Neg100WeightLower j.val) (hpThetaShiftThreeBatch063Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch063Neg100WeightLower, hpThetaShiftThreeBatch063Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch063Neg100_integral_bounds :
    (-73902833 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-142325713 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch063Lower hpThetaJensenCellsBatch063Upper
    hpThetaShiftThreeBatch063Neg100WeightLower hpThetaShiftThreeBatch063Neg100WeightUpper hpThetaJensenCellsBatch063_bounds hpThetaShiftThreeBatch063Neg100_weight_bounds
  have hl : (-73902833 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch063Lower j * hpThetaShiftThreeBatch063Neg100WeightLower j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftThreeBatch063Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftThreeBatch063Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch063Lower j * hpThetaShiftThreeBatch063Neg100WeightUpper j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftThreeBatch063Neg100WeightUpper j) / 1600) ≤ (-142325713 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftThreeBatch063Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1260 : ℝ) / 1600 = 63 / 80 by norm_num,
    show ((1260 : ℝ) + 20) / 1600 = (63 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch063Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1273661493 / 1000000000000 : ℝ)
  | 1 => (-130781441 / 100000000000 : ℝ)
  | 2 => (-671252693 / 500000000000 : ℝ)
  | 3 => (-275548173 / 200000000000 : ℝ)
  | 4 => (-282705471 / 200000000000 : ℝ)
  | 5 => (-724935713 / 500000000000 : ℝ)
  | 6 => (-23230933 / 15625000000 : ℝ)
  | 7 => (-1524258911 / 1000000000000 : ℝ)
  | 8 => (-781157893 / 500000000000 : ℝ)
  | 9 => (-320191433 / 200000000000 : ℝ)
  | 10 => (-1640189941 / 1000000000000 : ℝ)
  | 11 => (-67200843 / 40000000000 : ℝ)
  | 12 => (-1720457593 / 1000000000000 : ℝ)
  | 13 => (-440376647 / 250000000000 : ℝ)
  | 14 => (-1803175223 / 1000000000000 : ℝ)
  | 15 => (-1845470727 / 1000000000000 : ℝ)
  | 16 => (-1888400399 / 1000000000000 : ℝ)
  | 17 => (-1931971607 / 1000000000000 : ℝ)
  | 18 => (-197619179 / 100000000000 : ℝ)
  | 19 => (-252633557 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch063Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1240040251 / 1000000000000 : ℝ)
  | 1 => (-318415373 / 250000000000 : ℝ)
  | 2 => (-1307814409 / 1000000000000 : ℝ)
  | 3 => (-268501077 / 200000000000 : ℝ)
  | 4 => (-21527201 / 15625000000 : ℝ)
  | 5 => (-706763677 / 500000000000 : ℝ)
  | 6 => (-57994857 / 40000000000 : ℝ)
  | 7 => (-1486779711 / 1000000000000 : ℝ)
  | 8 => (-152425891 / 100000000000 : ℝ)
  | 9 => (-312463157 / 200000000000 : ℝ)
  | 10 => (-400239291 / 250000000000 : ℝ)
  | 11 => (-82009497 / 50000000000 : ℝ)
  | 12 => (-840010537 / 500000000000 : ℝ)
  | 13 => (-215057199 / 125000000000 : ℝ)
  | 14 => (-1761506587 / 1000000000000 : ℝ)
  | 15 => (-901587611 / 500000000000 : ℝ)
  | 16 => (-922735363 / 500000000000 : ℝ)
  | 17 => (-944200199 / 500000000000 : ℝ)
  | 18 => (-965985803 / 500000000000 : ℝ)
  | 19 => (-1976191789 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch063Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1260 : ℝ) + (j.val : ℝ)) / 1600)
      (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch063Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch063Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1260 : ℝ) + (j.val : ℝ)) / 1600)
    (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch063Neg70WeightLower j.val) (hpThetaShiftThreeBatch063Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch063Neg70WeightLower, hpThetaShiftThreeBatch063Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch063Neg70_integral_bounds :
    (-1099989 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-5236091 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch063Lower hpThetaJensenCellsBatch063Upper
    hpThetaShiftThreeBatch063Neg70WeightLower hpThetaShiftThreeBatch063Neg70WeightUpper hpThetaJensenCellsBatch063_bounds hpThetaShiftThreeBatch063Neg70_weight_bounds
  have hl : (-1099989 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch063Lower j * hpThetaShiftThreeBatch063Neg70WeightLower j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftThreeBatch063Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftThreeBatch063Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch063Lower j * hpThetaShiftThreeBatch063Neg70WeightUpper j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftThreeBatch063Neg70WeightUpper j) / 1600) ≤ (-5236091 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftThreeBatch063Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1260 : ℝ) / 1600 = 63 / 80 by norm_num,
    show ((1260 : ℝ) + 20) / 1600 = (63 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch063Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (11524589 / 15625000000 : ℝ)
  | 1 => (23238237 / 31250000000 : ℝ)
  | 2 => (749688191 / 1000000000000 : ℝ)
  | 3 => (755767119 / 1000000000000 : ℝ)
  | 4 => (190464991 / 250000000000 : ℝ)
  | 5 => (95995789 / 125000000000 : ℝ)
  | 6 => (774085743 / 1000000000000 : ℝ)
  | 7 => (195054457 / 250000000000 : ℝ)
  | 8 => (78636213 / 100000000000 : ℝ)
  | 9 => (198129551 / 250000000000 : ℝ)
  | 10 => (798685597 / 1000000000000 : ℝ)
  | 11 => (804863847 / 1000000000000 : ℝ)
  | 12 => (405526243 / 500000000000 : ℝ)
  | 13 => (408625517 / 500000000000 : ℝ)
  | 14 => (411729503 / 500000000000 : ℝ)
  | 15 => (165935181 / 200000000000 : ℝ)
  | 16 => (835901227 / 1000000000000 : ℝ)
  | 17 => (42106723 / 50000000000 : ℝ)
  | 18 => (848375081 / 1000000000000 : ℝ)
  | 19 => (5341391 / 6250000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch063Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (148724717 / 200000000000 : ℝ)
  | 1 => (5856939 / 7812500000 : ℝ)
  | 2 => (9447089 / 12500000000 : ℝ)
  | 3 => (152371993 / 200000000000 : ℝ)
  | 4 => (767966313 / 1000000000000 : ℝ)
  | 5 => (48380359 / 62500000000 : ℝ)
  | 6 => (780217829 / 1000000000000 : ℝ)
  | 7 => (786362131 / 1000000000000 : ℝ)
  | 8 => (158503641 / 200000000000 : ℝ)
  | 9 => (399342799 / 500000000000 : ℝ)
  | 10 => (100607981 / 125000000000 : ℝ)
  | 11 => (811052487 / 1000000000000 : ℝ)
  | 12 => (163450207 / 200000000000 : ℝ)
  | 13 => (823459007 / 1000000000000 : ℝ)
  | 14 => (414837953 / 500000000000 : ℝ)
  | 15 => (208975307 / 250000000000 : ℝ)
  | 16 => (842134461 / 1000000000000 : ℝ)
  | 17 => (424187541 / 500000000000 : ℝ)
  | 18 => (854622561 / 1000000000000 : ℝ)
  | 19 => (860876357 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch063Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1260 : ℝ) + (j.val : ℝ)) / 1600)
      (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch063Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch063Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1260 : ℝ) + (j.val : ℝ)) / 1600)
    (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch063Neg45WeightLower j.val) (hpThetaShiftThreeBatch063Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch063Neg45WeightLower, hpThetaShiftThreeBatch063Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch063Neg45_integral_bounds :
    (2642121 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (2729479 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch063Lower hpThetaJensenCellsBatch063Upper
    hpThetaShiftThreeBatch063Neg45WeightLower hpThetaShiftThreeBatch063Neg45WeightUpper hpThetaJensenCellsBatch063_bounds hpThetaShiftThreeBatch063Neg45_weight_bounds
  have hl : (2642121 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch063Lower j * hpThetaShiftThreeBatch063Neg45WeightLower j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftThreeBatch063Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftThreeBatch063Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch063Lower j * hpThetaShiftThreeBatch063Neg45WeightUpper j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftThreeBatch063Neg45WeightUpper j) / 1600) ≤ (2729479 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftThreeBatch063Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1260 : ℝ) / 1600 = 63 / 80 by norm_num,
    show ((1260 : ℝ) + 20) / 1600 = (63 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch063Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-264200201 / 1000000000000 : ℝ)
  | 1 => (-66055423 / 250000000000 : ℝ)
  | 2 => (-132113621 / 500000000000 : ℝ)
  | 3 => (-264226851 / 1000000000000 : ℝ)
  | 4 => (-528431 / 2000000000 : ℝ)
  | 5 => (-132093731 / 500000000000 : ℝ)
  | 6 => (-132071277 / 500000000000 : ℝ)
  | 7 => (-132040299 / 500000000000 : ℝ)
  | 8 => (-264001411 / 1000000000000 : ℝ)
  | 9 => (-263904809 / 1000000000000 : ℝ)
  | 10 => (-263790611 / 1000000000000 : ℝ)
  | 11 => (-263658629 / 1000000000000 : ℝ)
  | 12 => (-6587717 / 25000000000 : ℝ)
  | 13 => (-8229393 / 31250000000 : ℝ)
  | 14 => (-26315413 / 100000000000 : ℝ)
  | 15 => (-8217161 / 31250000000 : ℝ)
  | 16 => (-52545091 / 200000000000 : ℝ)
  | 17 => (-131241423 / 500000000000 : ℝ)
  | 18 => (-52444227 / 200000000000 : ℝ)
  | 19 => (-261940129 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch063Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-52832511 / 200000000000 : ℝ)
  | 1 => (-1321001 / 5000000000 : ℝ)
  | 2 => (-264221691 / 1000000000000 : ℝ)
  | 3 => (-264215499 / 1000000000000 : ℝ)
  | 4 => (-264187461 / 1000000000000 : ℝ)
  | 5 => (-264142553 / 1000000000000 : ℝ)
  | 6 => (-264080597 / 1000000000000 : ℝ)
  | 7 => (-26400141 / 100000000000 : ℝ)
  | 8 => (-32988101 / 125000000000 : ℝ)
  | 9 => (-26379061 / 100000000000 : ℝ)
  | 10 => (-65914657 / 250000000000 : ℝ)
  | 11 => (-263508679 / 1000000000000 : ℝ)
  | 12 => (-10533623 / 40000000000 : ℝ)
  | 13 => (-263154129 / 1000000000000 : ℝ)
  | 14 => (-262949151 / 1000000000000 : ℝ)
  | 15 => (-131362727 / 500000000000 : ℝ)
  | 16 => (-52496569 / 200000000000 : ℝ)
  | 17 => (-131110567 / 500000000000 : ℝ)
  | 18 => (-8185629 / 31250000000 : ℝ)
  | 19 => (-130819817 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch063Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1260 : ℝ) + (j.val : ℝ)) / 1600)
      (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch063Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch063Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1260 : ℝ) + (j.val : ℝ)) / 1600)
    (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch063Neg25WeightLower j.val) (hpThetaShiftThreeBatch063Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch063Neg25WeightLower, hpThetaShiftThreeBatch063Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch063Neg25_integral_bounds :
    (-1801977 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-351409 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch063Lower hpThetaJensenCellsBatch063Upper
    hpThetaShiftThreeBatch063Neg25WeightLower hpThetaShiftThreeBatch063Neg25WeightUpper hpThetaJensenCellsBatch063_bounds hpThetaShiftThreeBatch063Neg25_weight_bounds
  have hl : (-1801977 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch063Lower j * hpThetaShiftThreeBatch063Neg25WeightLower j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftThreeBatch063Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftThreeBatch063Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch063Lower j * hpThetaShiftThreeBatch063Neg25WeightUpper j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftThreeBatch063Neg25WeightUpper j) / 1600) ≤ (-351409 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftThreeBatch063Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1260 : ℝ) / 1600 = 63 / 80 by norm_num,
    show ((1260 : ℝ) + 20) / 1600 = (63 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch063Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch063Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch063Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch063Neg25_integral_bounds
end HodgeProofHP
