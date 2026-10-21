/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch074

/-! Exact signed weight and batch integral certificates, batch 74 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch074Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-11377358261 / 50000000000 : ℝ)
  | 1 => (-229780483811 / 1000000000000 : ℝ)
  | 2 => (-232033327113 / 1000000000000 : ℝ)
  | 3 => (-234305846519 / 1000000000000 : ℝ)
  | 4 => (-118299097229 / 500000000000 : ℝ)
  | 5 => (-238910524397 / 1000000000000 : ℝ)
  | 6 => (-60310747713 / 250000000000 : ℝ)
  | 7 => (-60898937347 / 250000000000 : ℝ)
  | 8 => (-245968956631 / 1000000000000 : ℝ)
  | 9 => (-248362770271 / 1000000000000 : ℝ)
  | 10 => (-25077734907 / 100000000000 : ℝ)
  | 11 => (-63303213217 / 250000000000 : ℝ)
  | 12 => (-63917360647 / 250000000000 : ℝ)
  | 13 => (-258147280243 / 1000000000000 : ℝ)
  | 14 => (-16290408059 / 62500000000 : ℝ)
  | 15 => (-131583676453 / 500000000000 : ℝ)
  | 16 => (-265709917451 / 1000000000000 : ℝ)
  | 17 => (-268274389021 / 1000000000000 : ℝ)
  | 18 => (-135430467589 / 500000000000 : ℝ)
  | 19 => (-54693944923 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch074Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-56333305243 / 250000000000 : ℝ)
  | 1 => (-227547165219 / 1000000000000 : ℝ)
  | 2 => (-22978048381 / 100000000000 : ℝ)
  | 3 => (-29004165889 / 125000000000 : ℝ)
  | 4 => (-117152923259 / 500000000000 : ℝ)
  | 5 => (-236598194457 / 1000000000000 : ℝ)
  | 6 => (-59727631099 / 250000000000 : ℝ)
  | 7 => (-241242990851 / 1000000000000 : ℝ)
  | 8 => (-243595749387 / 1000000000000 : ℝ)
  | 9 => (-24596895663 / 100000000000 : ℝ)
  | 10 => (-24836277027 / 100000000000 : ℝ)
  | 11 => (-250777349069 / 1000000000000 : ℝ)
  | 12 => (-253212852867 / 1000000000000 : ℝ)
  | 13 => (-255669442587 / 1000000000000 : ℝ)
  | 14 => (-129073640121 / 500000000000 : ℝ)
  | 15 => (-260646528943 / 1000000000000 : ℝ)
  | 16 => (-52633470581 / 200000000000 : ℝ)
  | 17 => (-5314198349 / 20000000000 : ℝ)
  | 18 => (-13413719451 / 50000000000 : ℝ)
  | 19 => (-270860935177 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch074Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1480 : ℝ) + (j.val : ℝ)) / 1600)
      (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch074Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch074Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1480 : ℝ) + (j.val : ℝ)) / 1600)
    (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch074Neg100WeightLower j.val) (hpThetaShiftThreeBatch074Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch074Neg100WeightLower, hpThetaShiftThreeBatch074Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch074Neg100_integral_bounds :
    (-25106853 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-12054863 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch074Lower hpThetaJensenCellsBatch074Upper
    hpThetaShiftThreeBatch074Neg100WeightLower hpThetaShiftThreeBatch074Neg100WeightUpper hpThetaJensenCellsBatch074_bounds hpThetaShiftThreeBatch074Neg100_weight_bounds
  have hl : (-25106853 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch074Lower j * hpThetaShiftThreeBatch074Neg100WeightLower j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftThreeBatch074Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftThreeBatch074Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch074Lower j * hpThetaShiftThreeBatch074Neg100WeightUpper j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftThreeBatch074Neg100WeightUpper j) / 1600) ≤ (-12054863 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftThreeBatch074Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1480 : ℝ) / 1600 = 74 / 80 by norm_num,
    show ((1480 : ℝ) + 20) / 1600 = (74 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch074Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-41628078241 / 1000000000000 : ℝ)
  | 1 => (-42110128391 / 1000000000000 : ℝ)
  | 2 => (-21298465613 / 500000000000 : ℝ)
  | 3 => (-43088527087 / 1000000000000 : ℝ)
  | 4 => (-43584956613 / 1000000000000 : ℝ)
  | 5 => (-44086260739 / 1000000000000 : ℝ)
  | 6 => (-44592480697 / 1000000000000 : ℝ)
  | 7 => (-22551829011 / 500000000000 : ℝ)
  | 8 => (-5702479319 / 125000000000 : ℝ)
  | 9 => (-11535263107 / 250000000000 : ℝ)
  | 10 => (-466673541 / 10000000000 : ℝ)
  | 11 => (-11799695581 / 250000000000 : ℝ)
  | 12 => (-47735380169 / 1000000000000 : ℝ)
  | 13 => (-24138595507 / 500000000000 : ℝ)
  | 14 => (-48824258553 / 1000000000000 : ℝ)
  | 15 => (-49376626797 / 1000000000000 : ℝ)
  | 16 => (-24967170037 / 500000000000 : ℝ)
  | 17 => (-10099488607 / 200000000000 : ℝ)
  | 18 => (-51065980649 / 1000000000000 : ℝ)
  | 19 => (-51639998213 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch074Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-20575370363 / 500000000000 : ℝ)
  | 1 => (-260175489 / 6250000000 : ℝ)
  | 2 => (-4211012839 / 100000000000 : ℝ)
  | 3 => (-1703877249 / 40000000000 : ℝ)
  | 4 => (-21544263543 / 500000000000 : ℝ)
  | 5 => (-10896239153 / 250000000000 : ℝ)
  | 6 => (-22043130369 / 500000000000 : ℝ)
  | 7 => (-5574060087 / 125000000000 : ℝ)
  | 8 => (-45103658021 / 1000000000000 : ℝ)
  | 9 => (-45619834551 / 1000000000000 : ℝ)
  | 10 => (-46141052427 / 1000000000000 : ℝ)
  | 11 => (-46667354099 / 1000000000000 : ℝ)
  | 12 => (-47198782323 / 1000000000000 : ℝ)
  | 13 => (-5966922521 / 125000000000 : ℝ)
  | 14 => (-48277191013 / 1000000000000 : ℝ)
  | 15 => (-6103032319 / 125000000000 : ℝ)
  | 16 => (-12344156699 / 250000000000 : ℝ)
  | 17 => (-49934340073 / 1000000000000 : ℝ)
  | 18 => (-25248721517 / 500000000000 : ℝ)
  | 19 => (-6383247581 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch074Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1480 : ℝ) + (j.val : ℝ)) / 1600)
      (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch074Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch074Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1480 : ℝ) + (j.val : ℝ)) / 1600)
    (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch074Neg70WeightLower j.val) (hpThetaShiftThreeBatch074Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch074Neg70WeightLower, hpThetaShiftThreeBatch074Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch074Neg70_integral_bounds :
    (-2332271 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-558973 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch074Lower hpThetaJensenCellsBatch074Upper
    hpThetaShiftThreeBatch074Neg70WeightLower hpThetaShiftThreeBatch074Neg70WeightUpper hpThetaJensenCellsBatch074_bounds hpThetaShiftThreeBatch074Neg70_weight_bounds
  have hl : (-2332271 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch074Lower j * hpThetaShiftThreeBatch074Neg70WeightLower j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftThreeBatch074Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftThreeBatch074Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch074Lower j * hpThetaShiftThreeBatch074Neg70WeightUpper j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftThreeBatch074Neg70WeightUpper j) / 1600) ≤ (-558973 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftThreeBatch074Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1480 : ℝ) / 1600 = 74 / 80 by norm_num,
    show ((1480 : ℝ) + 20) / 1600 = (74 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch074Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (50788299 / 100000000000 : ℝ)
  | 1 => (241109087 / 500000000000 : ℝ)
  | 2 => (456058771 / 1000000000000 : ℝ)
  | 3 => (429398959 / 1000000000000 : ℝ)
  | 4 => (80446573 / 200000000000 : ℝ)
  | 5 => (374554561 / 1000000000000 : ℝ)
  | 6 => (86589517 / 250000000000 : ℝ)
  | 7 => (158818677 / 500000000000 : ℝ)
  | 8 => (288386331 / 1000000000000 : ℝ)
  | 9 => (258598861 / 1000000000000 : ℝ)
  | 10 => (228268747 / 1000000000000 : ℝ)
  | 11 => (197389741 / 1000000000000 : ℝ)
  | 12 => (82977769 / 500000000000 : ℝ)
  | 13 => (66979889 / 500000000000 : ℝ)
  | 14 => (25349011 / 250000000000 : ℝ)
  | 15 => (13651573 / 200000000000 : ℝ)
  | 16 => (34538711 / 1000000000000 : ℝ)
  | 17 => (46399 / 200000000000 : ℝ)
  | 18 => (-17334463 / 500000000000 : ℝ)
  | 19 => (-35085377 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch074Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (53305899 / 100000000000 : ℝ)
  | 1 => (507882991 / 1000000000000 : ℝ)
  | 2 => (19288727 / 40000000000 : ℝ)
  | 3 => (114014693 / 250000000000 : ℝ)
  | 4 => (5367487 / 12500000000 : ℝ)
  | 5 => (201116433 / 500000000000 : ℝ)
  | 6 => (187277281 / 500000000000 : ℝ)
  | 7 => (346358069 / 1000000000000 : ℝ)
  | 8 => (63527471 / 200000000000 : ℝ)
  | 9 => (72096583 / 250000000000 : ℝ)
  | 10 => (129299431 / 500000000000 : ℝ)
  | 11 => (57067187 / 250000000000 : ℝ)
  | 12 => (98694871 / 500000000000 : ℝ)
  | 13 => (165955539 / 1000000000000 : ℝ)
  | 14 => (133959779 / 1000000000000 : ℝ)
  | 15 => (20279209 / 200000000000 : ℝ)
  | 16 => (34128933 / 500000000000 : ℝ)
  | 17 => (4317339 / 125000000000 : ℝ)
  | 18 => (57999 / 250000000000 : ℝ)
  | 19 => (-1386757 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch074Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1480 : ℝ) + (j.val : ℝ)) / 1600)
      (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch074Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch074Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1480 : ℝ) + (j.val : ℝ)) / 1600)
    (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch074Neg45WeightLower j.val) (hpThetaShiftThreeBatch074Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch074Neg45WeightLower, hpThetaShiftThreeBatch074Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch074Neg45_integral_bounds :
    (25193 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (29009 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch074Lower hpThetaJensenCellsBatch074Upper
    hpThetaShiftThreeBatch074Neg45WeightLower hpThetaShiftThreeBatch074Neg45WeightUpper hpThetaJensenCellsBatch074_bounds hpThetaShiftThreeBatch074Neg45_weight_bounds
  have hl : (25193 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch074Lower j * hpThetaShiftThreeBatch074Neg45WeightLower j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftThreeBatch074Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftThreeBatch074Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch074Lower j * hpThetaShiftThreeBatch074Neg45WeightUpper j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftThreeBatch074Neg45WeightUpper j) / 1600) ≤ (29009 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftThreeBatch074Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1480 : ℝ) / 1600 = 74 / 80 by norm_num,
    show ((1480 : ℝ) + 20) / 1600 = (74 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch074Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (255797697 / 500000000000 : ℝ)
  | 1 => (520860767 / 1000000000000 : ℝ)
  | 2 => (106039829 / 200000000000 : ℝ)
  | 3 => (134902701 / 250000000000 : ℝ)
  | 4 => (274548009 / 500000000000 : ℝ)
  | 5 => (27932753 / 50000000000 : ℝ)
  | 6 => (568288199 / 1000000000000 : ℝ)
  | 7 => (577995709 / 1000000000000 : ℝ)
  | 8 => (587777857 / 1000000000000 : ℝ)
  | 9 => (18676091 / 31250000000 : ℝ)
  | 10 => (303783571 / 500000000000 : ℝ)
  | 11 => (617574813 / 1000000000000 : ℝ)
  | 12 => (156914547 / 250000000000 : ℝ)
  | 13 => (637817533 / 1000000000000 : ℝ)
  | 14 => (648053109 / 1000000000000 : ℝ)
  | 15 => (329182589 / 500000000000 : ℝ)
  | 16 => (668753999 / 1000000000000 : ℝ)
  | 17 => (679219831 / 1000000000000 : ℝ)
  | 18 => (689762931 / 1000000000000 : ℝ)
  | 19 => (140076711 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch074Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (16276899 / 31250000000 : ℝ)
  | 1 => (265099573 / 500000000000 : ℝ)
  | 2 => (107922161 / 200000000000 : ℝ)
  | 3 => (549096019 / 1000000000000 : ℝ)
  | 4 => (558655061 / 1000000000000 : ℝ)
  | 5 => (2841441 / 5000000000 : ℝ)
  | 6 => (57799571 / 100000000000 : ℝ)
  | 7 => (293888929 / 500000000000 : ℝ)
  | 8 => (597634913 / 1000000000000 : ℝ)
  | 9 => (607567143 / 1000000000000 : ℝ)
  | 10 => (308787407 / 500000000000 : ℝ)
  | 11 => (627658189 / 1000000000000 : ℝ)
  | 12 => (318908767 / 500000000000 : ℝ)
  | 13 => (64805311 / 100000000000 : ℝ)
  | 14 => (658365179 / 1000000000000 : ℝ)
  | 15 => (334377 / 500000000 : ℝ)
  | 16 => (84902479 / 125000000000 : ℝ)
  | 17 => (172440733 / 250000000000 : ℝ)
  | 18 => (175095889 / 250000000000 : ℝ)
  | 19 => (355540979 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch074Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1480 : ℝ) + (j.val : ℝ)) / 1600)
      (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch074Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch074Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1480 : ℝ) + (j.val : ℝ)) / 1600)
    (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch074Neg25WeightLower j.val) (hpThetaShiftThreeBatch074Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch074Neg25WeightLower, hpThetaShiftThreeBatch074Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch074Neg25_integral_bounds :
    (58523 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (61361 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch074Lower hpThetaJensenCellsBatch074Upper
    hpThetaShiftThreeBatch074Neg25WeightLower hpThetaShiftThreeBatch074Neg25WeightUpper hpThetaJensenCellsBatch074_bounds hpThetaShiftThreeBatch074Neg25_weight_bounds
  have hl : (58523 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch074Lower j * hpThetaShiftThreeBatch074Neg25WeightLower j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftThreeBatch074Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftThreeBatch074Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch074Lower j * hpThetaShiftThreeBatch074Neg25WeightUpper j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftThreeBatch074Neg25WeightUpper j) / 1600) ≤ (61361 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftThreeBatch074Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1480 : ℝ) / 1600 = 74 / 80 by norm_num,
    show ((1480 : ℝ) + 20) / 1600 = (74 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch074Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch074Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch074Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch074Neg25_integral_bounds
end HodgeProofHP
