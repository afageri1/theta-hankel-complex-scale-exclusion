/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch074

/-! Exact signed weight and batch integral certificates, batch 74 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch074Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-90720735968983 / 500000000000 : ℝ)
  | 1 => (-182589154638293 / 1000000000000 : ℝ)
  | 2 => (-45935750912989 / 250000000000 : ℝ)
  | 3 => (-18490304663451 / 100000000000 : ℝ)
  | 4 => (-9303465567121 / 50000000000 : ℝ)
  | 5 => (-3744836512667 / 20000000000 : ℝ)
  | 6 => (-47105154366613 / 250000000000 : ℝ)
  | 7 => (-37921142980531 / 200000000000 : ℝ)
  | 8 => (-47699286526239 / 250000000000 : ℝ)
  | 9 => (-47998734834677 / 250000000000 : ℝ)
  | 10 => (-38639824594383 / 200000000000 : ℝ)
  | 11 => (-607530392111 / 3125000000 : ℝ)
  | 12 => (-1956267754237 / 10000000000 : ℝ)
  | 13 => (-196850301494159 / 1000000000000 : ℝ)
  | 14 => (-198080332468417 / 1000000000000 : ℝ)
  | 15 => (-99658448616057 / 500000000000 : ℝ)
  | 16 => (-50140006193823 / 250000000000 : ℝ)
  | 17 => (-3153277253011 / 15625000000 : ℝ)
  | 18 => (-203066084684097 / 1000000000000 : ℝ)
  | 19 => (-204329075554519 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch074Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-36059985599209 / 200000000000 : ℝ)
  | 1 => (-36288294387593 / 200000000000 : ℝ)
  | 2 => (-45647288659573 / 250000000000 : ℝ)
  | 3 => (-36748600730391 / 200000000000 : ℝ)
  | 4 => (-184903046634509 / 1000000000000 : ℝ)
  | 5 => (-186069311342419 / 1000000000000 : ℝ)
  | 6 => (-187241825633349 / 1000000000000 : ℝ)
  | 7 => (-188420617466451 / 1000000000000 : ℝ)
  | 8 => (-94802857451327 / 500000000000 : ℝ)
  | 9 => (-38159429220991 / 200000000000 : ℝ)
  | 10 => (-191994939338707 / 1000000000000 : ℝ)
  | 11 => (-96599561485957 / 500000000000 : ℝ)
  | 12 => (-194409725475519 / 1000000000000 : ℝ)
  | 13 => (-195626775423699 / 1000000000000 : ℝ)
  | 14 => (-98425150747079 / 500000000000 : ℝ)
  | 15 => (-3095005194819 / 15625000000 : ℝ)
  | 16 => (-199316897232113 / 1000000000000 : ℝ)
  | 17 => (-200560024775291 / 1000000000000 : ℝ)
  | 18 => (-201809744192703 / 1000000000000 : ℝ)
  | 19 => (-3172907573189 / 15625000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch074Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1480 : ℝ) + (j.val : ℝ)) / 1600)
      (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch074Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch074Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1480 : ℝ) + (j.val : ℝ)) / 1600)
    (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch074Neg100WeightLower j.val) (hpThetaShiftOneBatch074Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch074Neg100WeightLower, hpThetaShiftOneBatch074Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch074Neg100_integral_bounds :
    (-9704273951 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-116886033 / 6250000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch074Lower hpThetaJensenCellsBatch074Upper
    hpThetaShiftOneBatch074Neg100WeightLower hpThetaShiftOneBatch074Neg100WeightUpper hpThetaJensenCellsBatch074_bounds hpThetaShiftOneBatch074Neg100_weight_bounds
  have hl : (-9704273951 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch074Lower j * hpThetaShiftOneBatch074Neg100WeightLower j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftOneBatch074Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftOneBatch074Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch074Lower j * hpThetaShiftOneBatch074Neg100WeightUpper j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftOneBatch074Neg100WeightUpper j) / 1600) ≤ (-116886033 / 6250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftOneBatch074Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1480 : ℝ) / 1600 = 74 / 80 by norm_num,
    show ((1480 : ℝ) + 20) / 1600 = (74 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch074Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3315526129979 / 100000000000 : ℝ)
  | 1 => (-1669714576619 / 50000000000 : ℝ)
  | 2 => (-16817366882081 / 500000000000 : ℝ)
  | 3 => (-33876594779443 / 1000000000000 : ℝ)
  | 4 => (-34119881388531 / 1000000000000 : ℝ)
  | 5 => (-34364600427811 / 1000000000000 : ℝ)
  | 6 => (-34610758759827 / 1000000000000 : ℝ)
  | 7 => (-8714590818339 / 250000000000 : ℝ)
  | 8 => (-35107420883483 / 1000000000000 : ℝ)
  | 9 => (-7071587706337 / 200000000000 : ℝ)
  | 10 => (-35609923185901 / 1000000000000 : ℝ)
  | 11 => (-17931690920307 / 500000000000 : ℝ)
  | 12 => (-36118321516931 / 1000000000000 : ℝ)
  | 13 => (-18187374631327 / 500000000000 : ℝ)
  | 14 => (-36632672152367 / 1000000000000 : ℝ)
  | 15 => (-18446048643753 / 500000000000 : ℝ)
  | 16 => (-7430606359289 / 200000000000 : ℝ)
  | 17 => (-3741548283457 / 100000000000 : ℝ)
  | 18 => (-941986439609 / 25000000000 : ℝ)
  | 19 => (-37944963255463 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch074Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-32917636308013 / 1000000000000 : ℝ)
  | 1 => (-33155261299789 / 1000000000000 : ℝ)
  | 2 => (-33394291532379 / 1000000000000 : ℝ)
  | 3 => (-33634733764161 / 1000000000000 : ℝ)
  | 4 => (-16938297389721 / 500000000000 : ℝ)
  | 5 => (-3411988138853 / 100000000000 : ℝ)
  | 6 => (-3436460042781 / 100000000000 : ℝ)
  | 7 => (-17305379379913 / 500000000000 : ℝ)
  | 8 => (-6971672654671 / 200000000000 : ℝ)
  | 9 => (-17553710441741 / 500000000000 : ℝ)
  | 10 => (-8839484632921 / 250000000000 : ℝ)
  | 11 => (-356099231859 / 10000000000 : ℝ)
  | 12 => (-35863381840613 / 1000000000000 : ℝ)
  | 13 => (-3611832151693 / 100000000000 : ℝ)
  | 14 => (-36374749262653 / 1000000000000 : ℝ)
  | 15 => (-18316336076183 / 500000000000 : ℝ)
  | 16 => (-7378419457501 / 200000000000 : ℝ)
  | 17 => (-9288257949111 / 250000000000 : ℝ)
  | 18 => (-37415482834569 / 1000000000000 : ℝ)
  | 19 => (-37679457584359 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch074Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1480 : ℝ) + (j.val : ℝ)) / 1600)
      (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch074Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch074Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1480 : ℝ) + (j.val : ℝ)) / 1600)
    (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch074Neg65WeightLower j.val) (hpThetaShiftOneBatch074Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch074Neg65WeightLower, hpThetaShiftOneBatch074Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch074Neg65_integral_bounds :
    (-357404493 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-344095511 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch074Lower hpThetaJensenCellsBatch074Upper
    hpThetaShiftOneBatch074Neg65WeightLower hpThetaShiftOneBatch074Neg65WeightUpper hpThetaJensenCellsBatch074_bounds hpThetaShiftOneBatch074Neg65_weight_bounds
  have hl : (-357404493 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch074Lower j * hpThetaShiftOneBatch074Neg65WeightLower j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftOneBatch074Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftOneBatch074Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch074Lower j * hpThetaShiftOneBatch074Neg65WeightUpper j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftOneBatch074Neg65WeightUpper j) / 1600) ≤ (-344095511 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftOneBatch074Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1480 : ℝ) / 1600 = 74 / 80 by norm_num,
    show ((1480 : ℝ) + 20) / 1600 = (74 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch074Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-570726371831 / 250000000000 : ℝ)
  | 1 => (-2311230271451 / 1000000000000 : ℝ)
  | 2 => (-46795521971 / 20000000000 : ℝ)
  | 3 => (-473708844973 / 200000000000 : ℝ)
  | 4 => (-479507182399 / 200000000000 : ℝ)
  | 5 => (-606688106729 / 250000000000 : ℝ)
  | 6 => (-307024380249 / 125000000000 : ℝ)
  | 7 => (-1242932517497 / 500000000000 : ℝ)
  | 8 => (-2515763689119 / 1000000000000 : ℝ)
  | 9 => (-636473073251 / 250000000000 : ℝ)
  | 10 => (-322031517593 / 125000000000 : ℝ)
  | 11 => (-325855566489 / 125000000000 : ℝ)
  | 12 => (-659417692893 / 250000000000 : ℝ)
  | 13 => (-1334366085149 / 500000000000 : ℝ)
  | 14 => (-2700030044193 / 1000000000000 : ℝ)
  | 15 => (-1365782857451 / 500000000000 : ℝ)
  | 16 => (-552668101927 / 200000000000 : ℝ)
  | 17 => (-2795355761177 / 1000000000000 : ℝ)
  | 18 => (-565522561583 / 200000000000 : ℝ)
  | 19 => (-572022598769 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch074Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1127400247631 / 500000000000 : ℝ)
  | 1 => (-2282905487323 / 1000000000000 : ℝ)
  | 2 => (-46224605429 / 20000000000 : ℝ)
  | 3 => (-2339776098549 / 1000000000000 : ℝ)
  | 4 => (-74017007027 / 31250000000 : ℝ)
  | 5 => (-1198767955997 / 500000000000 : ℝ)
  | 6 => (-485350485383 / 200000000000 : ℝ)
  | 7 => (-2456195041991 / 1000000000000 : ℝ)
  | 8 => (-2485865034993 / 1000000000000 : ℝ)
  | 9 => (-1257881844559 / 500000000000 : ℝ)
  | 10 => (-2545892293003 / 1000000000000 : ℝ)
  | 11 => (-2576252140743 / 1000000000000 : ℝ)
  | 12 => (-2606844531911 / 1000000000000 : ℝ)
  | 13 => (-2637670771571 / 1000000000000 : ℝ)
  | 14 => (-2668732170297 / 1000000000000 : ℝ)
  | 15 => (-84375938881 / 31250000000 : ℝ)
  | 16 => (-2731565714901 / 1000000000000 : ℝ)
  | 17 => (-1381670254817 / 500000000000 : ℝ)
  | 18 => (-349419470147 / 125000000000 : ℝ)
  | 19 => (-1413806403957 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch074Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1480 : ℝ) + (j.val : ℝ)) / 1600)
      (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch074Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch074Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1480 : ℝ) + (j.val : ℝ)) / 1600)
    (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch074Neg40WeightLower j.val) (hpThetaShiftOneBatch074Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch074Neg40WeightLower, hpThetaShiftOneBatch074Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch074Neg40_integral_bounds :
    (-257257011 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-246490903 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch074Lower hpThetaJensenCellsBatch074Upper
    hpThetaShiftOneBatch074Neg40WeightLower hpThetaShiftOneBatch074Neg40WeightUpper hpThetaJensenCellsBatch074_bounds hpThetaShiftOneBatch074Neg40_weight_bounds
  have hl : (-257257011 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch074Lower j * hpThetaShiftOneBatch074Neg40WeightLower j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftOneBatch074Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftOneBatch074Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch074Lower j * hpThetaShiftOneBatch074Neg40WeightUpper j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftOneBatch074Neg40WeightUpper j) / 1600) ≤ (-246490903 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftOneBatch074Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1480 : ℝ) / 1600 = 74 / 80 by norm_num,
    show ((1480 : ℝ) + 20) / 1600 = (74 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch074Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (479123093609 / 1000000000000 : ℝ)
  | 1 => (481407328453 / 1000000000000 : ℝ)
  | 2 => (483692382683 / 1000000000000 : ℝ)
  | 3 => (485978195879 / 1000000000000 : ℝ)
  | 4 => (488264707177 / 1000000000000 : ℝ)
  | 5 => (245275927631 / 500000000000 : ℝ)
  | 6 => (246419789187 / 500000000000 : ℝ)
  | 7 => (247563907149 / 500000000000 : ℝ)
  | 8 => (49741650037 / 100000000000 : ℝ)
  | 9 => (49970557347 / 100000000000 : ℝ)
  | 10 => (25099748501 / 50000000000 : ℝ)
  | 11 => (504284625987 / 1000000000000 : ℝ)
  | 12 => (253287238437 / 500000000000 : ℝ)
  | 13 => (508864457727 / 1000000000000 : ℝ)
  | 14 => (163569441 / 320000000 : ℝ)
  | 15 => (513444547181 / 1000000000000 : ℝ)
  | 16 => (64466815443 / 125000000000 : ℝ)
  | 17 => (51802436539 / 100000000000 : ℝ)
  | 18 => (520314005427 / 1000000000000 : ℝ)
  | 19 => (32662710993 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch074Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (240703664227 / 500000000000 : ℝ)
  | 1 => (120923095671 / 250000000000 : ℝ)
  | 2 => (12149454897 / 25000000000 : ℝ)
  | 3 => (244132353589 / 500000000000 : ℝ)
  | 4 => (490551855263 / 1000000000000 : ℝ)
  | 5 => (3942716627 / 8000000000 : ℝ)
  | 6 => (495127814299 / 1000000000000 : ℝ)
  | 7 => (497416500371 / 1000000000000 : ℝ)
  | 8 => (499705573471 / 1000000000000 : ℝ)
  | 9 => (501994970021 / 1000000000000 : ℝ)
  | 10 => (126071156497 / 250000000000 : ℝ)
  | 11 => (810519163 / 1600000000 : ℝ)
  | 12 => (496937947 / 976562500 : ℝ)
  | 13 => (255577251563 / 500000000000 : ℝ)
  | 14 => (256722273591 / 500000000000 : ℝ)
  | 15 => (103146904709 / 200000000000 : ℝ)
  | 16 => (518024365391 / 1000000000000 : ℝ)
  | 17 => (130078501357 / 250000000000 : ℝ)
  | 18 => (522603375889 / 1000000000000 : ℝ)
  | 19 => (262446204267 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch074Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1480 : ℝ) + (j.val : ℝ)) / 1600)
      (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch074Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch074Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1480 : ℝ) + (j.val : ℝ)) / 1600)
    (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch074Neg20WeightLower j.val) (hpThetaShiftOneBatch074Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch074Neg20WeightLower, hpThetaShiftOneBatch074Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch074Neg20_integral_bounds :
    (24487083 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (25369681 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch074Lower hpThetaJensenCellsBatch074Upper
    hpThetaShiftOneBatch074Neg20WeightLower hpThetaShiftOneBatch074Neg20WeightUpper hpThetaJensenCellsBatch074_bounds hpThetaShiftOneBatch074Neg20_weight_bounds
  have hl : (24487083 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch074Lower j * hpThetaShiftOneBatch074Neg20WeightLower j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftOneBatch074Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftOneBatch074Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch074Lower j * hpThetaShiftOneBatch074Neg20WeightUpper j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftOneBatch074Neg20WeightUpper j) / 1600) ≤ (25369681 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftOneBatch074Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1480 : ℝ) / 1600 = 74 / 80 by norm_num,
    show ((1480 : ℝ) + 20) / 1600 = (74 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch074Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch074Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch074Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch074Neg20_integral_bounds
end HodgeProofHP
