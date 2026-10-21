/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch023

/-! Exact signed weight and batch integral certificates, batch 23 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch023Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-13825093 / 100000000000 : ℝ)
  | 1 => (-5599769 / 40000000000 : ℝ)
  | 2 => (-141738387 / 1000000000000 : ℝ)
  | 3 => (-71741533 / 500000000000 : ℝ)
  | 4 => (-145227909 / 1000000000000 : ℝ)
  | 5 => (-29394511 / 200000000000 : ℝ)
  | 6 => (-148716639 / 1000000000000 : ℝ)
  | 7 => (-37614947 / 250000000000 : ℝ)
  | 8 => (-19025203 / 125000000000 : ℝ)
  | 9 => (-153941761 / 1000000000000 : ℝ)
  | 10 => (-15567981 / 100000000000 : ℝ)
  | 11 => (-78707687 / 500000000000 : ℝ)
  | 12 => (-159148049 / 1000000000000 : ℝ)
  | 13 => (-160877427 / 1000000000000 : ℝ)
  | 14 => (-162603091 / 1000000000000 : ℝ)
  | 15 => (-164324619 / 1000000000000 : ℝ)
  | 16 => (-10377599 / 62500000000 : ℝ)
  | 17 => (-167753549 / 1000000000000 : ℝ)
  | 18 => (-42365019 / 250000000000 : ℝ)
  | 19 => (-34232143 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch023Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-68254421 / 500000000000 : ℝ)
  | 1 => (-138250929 / 1000000000000 : ℝ)
  | 2 => (-8749639 / 62500000000 : ℝ)
  | 3 => (-70869193 / 500000000000 : ℝ)
  | 4 => (-28696613 / 200000000000 : ℝ)
  | 5 => (-36306977 / 250000000000 : ℝ)
  | 6 => (-73486277 / 500000000000 : ℝ)
  | 7 => (-74358319 / 500000000000 : ℝ)
  | 8 => (-150459787 / 1000000000000 : ℝ)
  | 9 => (-152201623 / 1000000000000 : ℝ)
  | 10 => (-120267 / 781250000 : ℝ)
  | 11 => (-155679809 / 1000000000000 : ℝ)
  | 12 => (-157415373 / 1000000000000 : ℝ)
  | 13 => (-9946753 / 62500000000 : ℝ)
  | 14 => (-80438713 / 500000000000 : ℝ)
  | 15 => (-16260309 / 100000000000 : ℝ)
  | 16 => (-82162309 / 500000000000 : ℝ)
  | 17 => (-166041583 / 1000000000000 : ℝ)
  | 18 => (-41938387 / 250000000000 : ℝ)
  | 19 => (-6778403 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch023Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((460 : ℝ) + (j.val : ℝ)) / 1600)
      (((460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch023Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch023Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((460 : ℝ) + (j.val : ℝ)) / 1600)
    (((460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch023Neg100WeightLower j.val) (hpThetaShiftTwoBatch023Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch023Neg100WeightLower, hpThetaShiftTwoBatch023Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch023Neg100_integral_bounds :
    (-742623239 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-724837917 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch023Lower hpThetaJensenCellsBatch023Upper
    hpThetaShiftTwoBatch023Neg100WeightLower hpThetaShiftTwoBatch023Neg100WeightUpper hpThetaJensenCellsBatch023_bounds hpThetaShiftTwoBatch023Neg100_weight_bounds
  have hl : (-742623239 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch023Lower j * hpThetaShiftTwoBatch023Neg100WeightLower j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftTwoBatch023Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftTwoBatch023Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch023Lower j * hpThetaShiftTwoBatch023Neg100WeightUpper j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftTwoBatch023Neg100WeightUpper j) / 1600) ≤ (-724837917 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftTwoBatch023Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (460 : ℝ) / 1600 = 23 / 80 by norm_num,
    show ((460 : ℝ) + 20) / 1600 = (23 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch023Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-164307 / 5000000000 : ℝ)
  | 1 => (-34546541 / 1000000000000 : ℝ)
  | 2 => (-7250253 / 200000000000 : ℝ)
  | 3 => (-94939 / 2500000000 : ℝ)
  | 4 => (-39719573 / 1000000000000 : ℝ)
  | 5 => (-5185401 / 125000000000 : ℝ)
  | 6 => (-43266527 / 1000000000000 : ℝ)
  | 7 => (-901391 / 20000000000 : ℝ)
  | 8 => (-23446147 / 500000000000 : ℝ)
  | 9 => (-48734773 / 1000000000000 : ℝ)
  | 10 => (-50597 / 1000000000 : ℝ)
  | 11 => (-6559873 / 125000000000 : ℝ)
  | 12 => (-13595183 / 250000000000 : ℝ)
  | 13 => (-56302249 / 1000000000000 : ℝ)
  | 14 => (-58243537 / 1000000000000 : ℝ)
  | 15 => (-12040919 / 200000000000 : ℝ)
  | 16 => (-62185419 / 1000000000000 : ℝ)
  | 17 => (-16046501 / 250000000000 : ℝ)
  | 18 => (-66206341 / 1000000000000 : ℝ)
  | 19 => (-34123209 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch023Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-31195809 / 1000000000000 : ℝ)
  | 1 => (-32861399 / 1000000000000 : ℝ)
  | 2 => (-1727327 / 50000000000 : ℝ)
  | 3 => (-283213 / 7812500000 : ℝ)
  | 4 => (-37975599 / 1000000000000 : ℝ)
  | 5 => (-9929893 / 250000000000 : ℝ)
  | 6 => (-41483207 / 1000000000000 : ℝ)
  | 7 => (-21633263 / 500000000000 : ℝ)
  | 8 => (-45069549 / 1000000000000 : ℝ)
  | 9 => (-46892293 / 1000000000000 : ℝ)
  | 10 => (-12183693 / 250000000000 : ℝ)
  | 11 => (-50596999 / 1000000000000 : ℝ)
  | 12 => (-52478983 / 1000000000000 : ℝ)
  | 13 => (-54380731 / 1000000000000 : ℝ)
  | 14 => (-7037781 / 125000000000 : ℝ)
  | 15 => (-3640221 / 62500000000 : ℝ)
  | 16 => (-30102297 / 500000000000 : ℝ)
  | 17 => (-31092709 / 500000000000 : ℝ)
  | 18 => (-64186003 / 1000000000000 : ℝ)
  | 19 => (-3310317 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch023Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((460 : ℝ) + (j.val : ℝ)) / 1600)
      (((460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch023Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch023Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((460 : ℝ) + (j.val : ℝ)) / 1600)
    (((460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch023Neg65WeightLower j.val) (hpThetaShiftTwoBatch023Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch023Neg65WeightLower, hpThetaShiftTwoBatch023Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch023Neg65_integral_bounds :
    (-119538799 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-454442741 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch023Lower hpThetaJensenCellsBatch023Upper
    hpThetaShiftTwoBatch023Neg65WeightLower hpThetaShiftTwoBatch023Neg65WeightUpper hpThetaJensenCellsBatch023_bounds hpThetaShiftTwoBatch023Neg65_weight_bounds
  have hl : (-119538799 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch023Lower j * hpThetaShiftTwoBatch023Neg65WeightLower j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftTwoBatch023Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftTwoBatch023Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch023Lower j * hpThetaShiftTwoBatch023Neg65WeightUpper j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftTwoBatch023Neg65WeightUpper j) / 1600) ≤ (-454442741 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftTwoBatch023Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (460 : ℝ) / 1600 = 23 / 80 by norm_num,
    show ((460 : ℝ) + 20) / 1600 = (23 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch023Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (11316991 / 125000000000 : ℝ)
  | 1 => (22463897 / 250000000000 : ℝ)
  | 2 => (44578449 / 500000000000 : ℝ)
  | 3 => (88439711 / 1000000000000 : ℝ)
  | 4 => (87703883 / 1000000000000 : ℝ)
  | 5 => (21737317 / 250000000000 : ℝ)
  | 6 => (86175721 / 1000000000000 : ℝ)
  | 7 => (85383099 / 1000000000000 : ℝ)
  | 8 => (84571257 / 1000000000000 : ℝ)
  | 9 => (83740051 / 1000000000000 : ℝ)
  | 10 => (82889339 / 1000000000000 : ℝ)
  | 11 => (2563093 / 31250000000 : ℝ)
  | 12 => (81128821 / 1000000000000 : ℝ)
  | 13 => (80218731 / 1000000000000 : ℝ)
  | 14 => (15857713 / 200000000000 : ℝ)
  | 15 => (39169091 / 500000000000 : ℝ)
  | 16 => (967093 / 12500000000 : ℝ)
  | 17 => (76376199 / 1000000000000 : ℝ)
  | 18 => (75364319 / 1000000000000 : ℝ)
  | 19 => (37165831 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch023Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5699879 / 62500000000 : ℝ)
  | 1 => (90535929 / 1000000000000 : ℝ)
  | 2 => (89855589 / 1000000000000 : ℝ)
  | 3 => (89156899 / 1000000000000 : ℝ)
  | 4 => (2763741 / 31250000000 : ℝ)
  | 5 => (21925971 / 250000000000 : ℝ)
  | 6 => (86949269 / 1000000000000 : ℝ)
  | 7 => (43087861 / 500000000000 : ℝ)
  | 8 => (853831 / 10000000000 : ℝ)
  | 9 => (42285629 / 500000000000 : ℝ)
  | 10 => (20935013 / 250000000000 : ℝ)
  | 11 => (4144467 / 50000000000 : ℝ)
  | 12 => (82018977 / 1000000000000 : ℝ)
  | 13 => (40564411 / 500000000000 : ℝ)
  | 14 => (20054683 / 250000000000 : ℝ)
  | 15 => (39644283 / 500000000000 : ℝ)
  | 16 => (78338183 / 1000000000000 : ℝ)
  | 17 => (77367441 / 1000000000000 : ℝ)
  | 18 => (381881 / 5000000000 : ℝ)
  | 19 => (471027 / 6250000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch023Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((460 : ℝ) + (j.val : ℝ)) / 1600)
      (((460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch023Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch023Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((460 : ℝ) + (j.val : ℝ)) / 1600)
    (((460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch023Neg45WeightLower j.val) (hpThetaShiftTwoBatch023Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch023Neg45WeightLower, hpThetaShiftTwoBatch023Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch023Neg45_integral_bounds :
    (394147149 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (806657319 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch023Lower hpThetaJensenCellsBatch023Upper
    hpThetaShiftTwoBatch023Neg45WeightLower hpThetaShiftTwoBatch023Neg45WeightUpper hpThetaJensenCellsBatch023_bounds hpThetaShiftTwoBatch023Neg45_weight_bounds
  have hl : (394147149 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch023Lower j * hpThetaShiftTwoBatch023Neg45WeightLower j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftTwoBatch023Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftTwoBatch023Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch023Lower j * hpThetaShiftTwoBatch023Neg45WeightUpper j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftTwoBatch023Neg45WeightUpper j) / 1600) ≤ (806657319 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftTwoBatch023Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (460 : ℝ) / 1600 = 23 / 80 by norm_num,
    show ((460 : ℝ) + 20) / 1600 = (23 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch023Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (53298851 / 200000000000 : ℝ)
  | 1 => (267701621 / 1000000000000 : ℝ)
  | 2 => (67226011 / 250000000000 : ℝ)
  | 3 => (270101393 / 1000000000000 : ℝ)
  | 4 => (271293537 / 1000000000000 : ℝ)
  | 5 => (272480343 / 1000000000000 : ℝ)
  | 6 => (273661677 / 1000000000000 : ℝ)
  | 7 => (137418703 / 500000000000 : ℝ)
  | 8 => (55201479 / 200000000000 : ℝ)
  | 9 => (277171509 / 1000000000000 : ℝ)
  | 10 => (27832961 / 100000000000 : ℝ)
  | 11 => (139740781 / 500000000000 : ℝ)
  | 12 => (280627227 / 1000000000000 : ℝ)
  | 13 => (56353293 / 200000000000 : ℝ)
  | 14 => (141449569 / 500000000000 : ℝ)
  | 15 => (56805021 / 200000000000 : ℝ)
  | 16 => (11405769 / 40000000000 : ℝ)
  | 17 => (71564089 / 250000000000 : ℝ)
  | 18 => (57472271 / 200000000000 : ℝ)
  | 19 => (7211477 / 25000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch023Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (133850811 / 500000000000 : ℝ)
  | 1 => (53780809 / 200000000000 : ℝ)
  | 2 => (135050697 / 500000000000 : ℝ)
  | 3 => (135646769 / 500000000000 : ℝ)
  | 4 => (34060043 / 125000000000 : ℝ)
  | 5 => (136830839 / 500000000000 : ℝ)
  | 6 => (274837407 / 1000000000000 : ℝ)
  | 7 => (69001849 / 250000000000 : ℝ)
  | 8 => (27717151 / 100000000000 : ℝ)
  | 9 => (278329611 / 1000000000000 : ℝ)
  | 10 => (279481563 / 1000000000000 : ℝ)
  | 11 => (70156807 / 250000000000 : ℝ)
  | 12 => (140883233 / 500000000000 : ℝ)
  | 13 => (282899139 / 1000000000000 : ℝ)
  | 14 => (142012553 / 500000000000 : ℝ)
  | 15 => (142572113 / 500000000000 : ℝ)
  | 16 => (286256357 / 1000000000000 : ℝ)
  | 17 => (71840339 / 250000000000 : ℝ)
  | 18 => (288459081 / 1000000000000 : ℝ)
  | 19 => (289549387 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch023Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((460 : ℝ) + (j.val : ℝ)) / 1600)
      (((460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch023Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch023Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((460 : ℝ) + (j.val : ℝ)) / 1600)
    (((460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch023Neg25WeightLower j.val) (hpThetaShiftTwoBatch023Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch023Neg25WeightLower, hpThetaShiftTwoBatch023Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch023Neg25_integral_bounds :
    (2632442581 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (23 / 80 : ℝ) ((23 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (2677875613 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch023Lower hpThetaJensenCellsBatch023Upper
    hpThetaShiftTwoBatch023Neg25WeightLower hpThetaShiftTwoBatch023Neg25WeightUpper hpThetaJensenCellsBatch023_bounds hpThetaShiftTwoBatch023Neg25_weight_bounds
  have hl : (2632442581 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch023Lower j * hpThetaShiftTwoBatch023Neg25WeightLower j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftTwoBatch023Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftTwoBatch023Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch023Lower j * hpThetaShiftTwoBatch023Neg25WeightUpper j)
        (hpThetaJensenCellsBatch023Upper j * hpThetaShiftTwoBatch023Neg25WeightUpper j) / 1600) ≤ (2677875613 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch023Lower, hpThetaJensenCellsBatch023Upper,
      hpThetaShiftTwoBatch023Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (460 : ℝ) / 1600 = 23 / 80 by norm_num,
    show ((460 : ℝ) + 20) / 1600 = (23 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch023Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch023Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch023Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch023Neg25_integral_bounds
end HodgeProofHP
