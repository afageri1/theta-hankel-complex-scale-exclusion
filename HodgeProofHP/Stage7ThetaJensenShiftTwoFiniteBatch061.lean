/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch061

/-! Exact signed weight and batch integral certificates, batch 61 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch061Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-626611495083 / 1000000000000 : ℝ)
  | 1 => (-633662278049 / 1000000000000 : ℝ)
  | 2 => (-640779867803 / 1000000000000 : ℝ)
  | 3 => (-647964798873 / 1000000000000 : ℝ)
  | 4 => (-327608804687 / 500000000000 : ℝ)
  | 5 => (-662538841033 / 1000000000000 : ℝ)
  | 6 => (-133985807841 / 200000000000 : ℝ)
  | 7 => (-135477750579 / 200000000000 : ℝ)
  | 8 => (-684918534779 / 1000000000000 : ℝ)
  | 9 => (-346259470611 / 500000000000 : ℝ)
  | 10 => (-700190532299 / 1000000000000 : ℝ)
  | 11 => (-35396693591 / 50000000000 : ℝ)
  | 12 => (-357874763671 / 500000000000 : ℝ)
  | 13 => (-180909517549 / 250000000000 : ℝ)
  | 14 => (-182900018877 / 250000000000 : ℝ)
  | 15 => (-92454515277 / 125000000000 : ℝ)
  | 16 => (-373873396547 / 500000000000 : ℝ)
  | 17 => (-755932674771 / 1000000000000 : ℝ)
  | 18 => (-382097178877 / 500000000000 : ℝ)
  | 19 => (-772532436449 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch061Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-619626987947 / 1000000000000 : ℝ)
  | 1 => (-313305747541 / 500000000000 : ℝ)
  | 2 => (-19801946189 / 31250000000 : ℝ)
  | 3 => (-320389933901 / 500000000000 : ℝ)
  | 4 => (-80995599859 / 125000000000 : ℝ)
  | 5 => (-655217609373 / 1000000000000 : ℝ)
  | 6 => (-82817355129 / 125000000000 : ℝ)
  | 7 => (-167482259801 / 250000000000 : ℝ)
  | 8 => (-338694376447 / 500000000000 : ℝ)
  | 9 => (-342459267389 / 500000000000 : ℝ)
  | 10 => (-692518941221 / 1000000000000 : ℝ)
  | 11 => (-350095266149 / 500000000000 : ℝ)
  | 12 => (-707933871819 / 1000000000000 : ℝ)
  | 13 => (-715749527341 / 1000000000000 : ℝ)
  | 14 => (-144727614039 / 200000000000 : ℝ)
  | 15 => (-731600075507 / 1000000000000 : ℝ)
  | 16 => (-147927224443 / 200000000000 : ℝ)
  | 17 => (-747746793093 / 1000000000000 : ℝ)
  | 18 => (-75593267477 / 100000000000 : ℝ)
  | 19 => (-764194357753 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch061Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1220 : ℝ) + (j.val : ℝ)) / 1600)
      (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch061Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch061Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1220 : ℝ) + (j.val : ℝ)) / 1600)
    (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch061Neg100WeightLower j.val) (hpThetaShiftTwoBatch061Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch061Neg100WeightLower, hpThetaShiftTwoBatch061Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch061Neg100_integral_bounds :
    (-4453257793 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-8601119427 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch061Lower hpThetaJensenCellsBatch061Upper
    hpThetaShiftTwoBatch061Neg100WeightLower hpThetaShiftTwoBatch061Neg100WeightUpper hpThetaJensenCellsBatch061_bounds hpThetaShiftTwoBatch061Neg100_weight_bounds
  have hl : (-4453257793 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch061Lower j * hpThetaShiftTwoBatch061Neg100WeightLower j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftTwoBatch061Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftTwoBatch061Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch061Lower j * hpThetaShiftTwoBatch061Neg100WeightUpper j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftTwoBatch061Neg100WeightUpper j) / 1600) ≤ (-8601119427 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftTwoBatch061Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1220 : ℝ) / 1600 = 61 / 80 by norm_num,
    show ((1220 : ℝ) + 20) / 1600 = (61 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch061Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-33207935077 / 1000000000000 : ℝ)
  | 1 => (-6798796153 / 200000000000 : ℝ)
  | 2 => (-17395242589 / 500000000000 : ℝ)
  | 3 => (-35597550697 / 1000000000000 : ℝ)
  | 4 => (-36415280487 / 1000000000000 : ℝ)
  | 5 => (-18621889251 / 500000000000 : ℝ)
  | 6 => (-3808314949 / 100000000000 : ℝ)
  | 7 => (-38933499001 / 1000000000000 : ℝ)
  | 8 => (-4974366673 / 125000000000 : ℝ)
  | 9 => (-40667559801 / 1000000000000 : ℝ)
  | 10 => (-2596967889 / 62500000000 : ℝ)
  | 11 => (-42446821447 / 1000000000000 : ℝ)
  | 12 => (-21676837543 / 500000000000 : ℝ)
  | 13 => (-44272157583 / 1000000000000 : ℝ)
  | 14 => (-45202380217 / 1000000000000 : ℝ)
  | 15 => (-46144455103 / 1000000000000 : ℝ)
  | 16 => (-23549247601 / 500000000000 : ℝ)
  | 17 => (-48064614319 / 1000000000000 : ℝ)
  | 18 => (-49042927117 / 1000000000000 : ℝ)
  | 19 => (-12508387279 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch061Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2027015407 / 62500000000 : ℝ)
  | 1 => (-8301983769 / 250000000000 : ℝ)
  | 2 => (-8498495191 / 250000000000 : ℝ)
  | 3 => (-34790485177 / 1000000000000 : ℝ)
  | 4 => (-4449693837 / 125000000000 : ℝ)
  | 5 => (-18207640243 / 500000000000 : ℝ)
  | 6 => (-37243778501 / 1000000000000 : ℝ)
  | 7 => (-38083149489 / 1000000000000 : ℝ)
  | 8 => (-38933499 / 1000000000 : ℝ)
  | 9 => (-39794933383 / 1000000000000 : ℝ)
  | 10 => (-203337799 / 5000000000 : ℝ)
  | 11 => (-41551486223 / 1000000000000 : ℝ)
  | 12 => (-21223410723 / 500000000000 : ℝ)
  | 13 => (-8670735017 / 200000000000 : ℝ)
  | 14 => (-22136078791 / 500000000000 : ℝ)
  | 15 => (-5650297527 / 125000000000 : ℝ)
  | 16 => (-23072227551 / 500000000000 : ℝ)
  | 17 => (-47098495201 / 1000000000000 : ℝ)
  | 18 => (-24032307159 / 500000000000 : ℝ)
  | 19 => (-12260731779 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch061Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1220 : ℝ) + (j.val : ℝ)) / 1600)
      (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch061Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch061Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1220 : ℝ) + (j.val : ℝ)) / 1600)
    (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch061Neg65WeightLower j.val) (hpThetaShiftTwoBatch061Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch061Neg65WeightLower, hpThetaShiftTwoBatch061Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch061Neg65_integral_bounds :
    (-20979973 / 40000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-62645853 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch061Lower hpThetaJensenCellsBatch061Upper
    hpThetaShiftTwoBatch061Neg65WeightLower hpThetaShiftTwoBatch061Neg65WeightUpper hpThetaJensenCellsBatch061_bounds hpThetaShiftTwoBatch061Neg65_weight_bounds
  have hl : (-20979973 / 40000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch061Lower j * hpThetaShiftTwoBatch061Neg65WeightLower j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftTwoBatch061Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftTwoBatch061Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch061Lower j * hpThetaShiftTwoBatch061Neg65WeightUpper j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftTwoBatch061Neg65WeightUpper j) / 1600) ≤ (-62645853 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftTwoBatch061Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1220 : ℝ) / 1600 = 61 / 80 by norm_num,
    show ((1220 : ℝ) + 20) / 1600 = (61 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch061Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (20068202597 / 1000000000000 : ℝ)
  | 1 => (4028262711 / 200000000000 : ℝ)
  | 2 => (126335117 / 6250000000 : ℝ)
  | 3 => (20285100663 / 1000000000000 : ℝ)
  | 4 => (5088935443 / 250000000000 : ℝ)
  | 5 => (20425524257 / 1000000000000 : ℝ)
  | 6 => (20494430143 / 1000000000000 : ℝ)
  | 7 => (2056244127 / 100000000000 : ℝ)
  | 8 => (4125907859 / 200000000000 : ℝ)
  | 9 => (20695705687 / 1000000000000 : ℝ)
  | 10 => (830436869 / 40000000000 : ℝ)
  | 11 => (10412584251 / 500000000000 : ℝ)
  | 12 => (10444213459 / 500000000000 : ℝ)
  | 13 => (20950677681 / 1000000000000 : ℝ)
  | 14 => (10505950653 / 500000000000 : ℝ)
  | 15 => (21072078113 / 1000000000000 : ℝ)
  | 16 => (21131188227 / 1000000000000 : ℝ)
  | 17 => (21189211573 / 1000000000000 : ℝ)
  | 18 => (21246127879 / 1000000000000 : ℝ)
  | 19 => (20802653 / 976562500 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch061Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5035328389 / 250000000000 : ℝ)
  | 1 => (20213618721 / 1000000000000 : ℝ)
  | 2 => (2535637583 / 125000000000 : ℝ)
  | 3 => (20355741773 / 1000000000000 : ℝ)
  | 4 => (10212762129 / 500000000000 : ℝ)
  | 5 => (320225471 / 15625000000 : ℝ)
  | 6 => (20562441271 / 1000000000000 : ℝ)
  | 7 => (644673103 / 31250000000 : ℝ)
  | 8 => (2586963211 / 125000000000 : ℝ)
  | 9 => (10380460863 / 500000000000 : ℝ)
  | 10 => (20825168503 / 1000000000000 : ℝ)
  | 11 => (20888426919 / 1000000000000 : ℝ)
  | 12 => (10475338841 / 500000000000 : ℝ)
  | 13 => (21011901307 / 1000000000000 : ℝ)
  | 14 => (10536039057 / 500000000000 : ℝ)
  | 15 => (5282797057 / 250000000000 : ℝ)
  | 16 => (10594605787 / 500000000000 : ℝ)
  | 17 => (531153197 / 25000000000 : ℝ)
  | 18 => (21301916673 / 1000000000000 : ℝ)
  | 19 => (10678278639 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch061Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1220 : ℝ) + (j.val : ℝ)) / 1600)
      (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch061Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch061Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1220 : ℝ) + (j.val : ℝ)) / 1600)
    (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch061Neg45WeightLower j.val) (hpThetaShiftTwoBatch061Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch061Neg45WeightLower, hpThetaShiftTwoBatch061Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch061Neg45_integral_bounds :
    (259270371 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (8323841 / 31250000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch061Lower hpThetaJensenCellsBatch061Upper
    hpThetaShiftTwoBatch061Neg45WeightLower hpThetaShiftTwoBatch061Neg45WeightUpper hpThetaJensenCellsBatch061_bounds hpThetaShiftTwoBatch061Neg45_weight_bounds
  have hl : (259270371 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch061Lower j * hpThetaShiftTwoBatch061Neg45WeightLower j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftTwoBatch061Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftTwoBatch061Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch061Lower j * hpThetaShiftTwoBatch061Neg45WeightUpper j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftTwoBatch061Neg45WeightUpper j) / 1600) ≤ (8323841 / 31250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftTwoBatch061Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1220 : ℝ) / 1600 = 61 / 80 by norm_num,
    show ((1220 : ℝ) + 20) / 1600 = (61 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch061Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1462243077 / 1000000000000 : ℝ)
  | 1 => (-1418859513 / 1000000000000 : ℝ)
  | 2 => (-1374999893 / 1000000000000 : ℝ)
  | 3 => (-1330661977 / 1000000000000 : ℝ)
  | 4 => (-1285843527 / 1000000000000 : ℝ)
  | 5 => (-38766947 / 31250000000 : ℝ)
  | 6 => (-1194756073 / 1000000000000 : ℝ)
  | 7 => (-5742413 / 5000000000 : ℝ)
  | 8 => (-1101719651 / 1000000000000 : ℝ)
  | 9 => (-1054464997 / 1000000000000 : ℝ)
  | 10 => (-125839551 / 125000000000 : ℝ)
  | 11 => (-119808957 / 125000000000 : ℝ)
  | 12 => (-909728517 / 1000000000000 : ℝ)
  | 13 => (-860484769 / 1000000000000 : ℝ)
  | 14 => (-81073819 / 100000000000 : ℝ)
  | 15 => (-380243281 / 500000000000 : ℝ)
  | 16 => (-70972767 / 100000000000 : ℝ)
  | 17 => (-658459301 / 1000000000000 : ℝ)
  | 18 => (-151669811 / 250000000000 : ℝ)
  | 19 => (-138596323 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch061Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-177357439 / 125000000000 : ℝ)
  | 1 => (-343749973 / 250000000000 : ℝ)
  | 2 => (-166332747 / 125000000000 : ℝ)
  | 3 => (-642921763 / 500000000000 : ℝ)
  | 4 => (-1240542303 / 1000000000000 : ℝ)
  | 5 => (-149344509 / 125000000000 : ℝ)
  | 6 => (-1148482599 / 1000000000000 : ℝ)
  | 7 => (-22034393 / 20000000000 : ℝ)
  | 8 => (-263616249 / 250000000000 : ℝ)
  | 9 => (-1006716407 / 1000000000000 : ℝ)
  | 10 => (-191694331 / 200000000000 : ℝ)
  | 11 => (-227432129 / 250000000000 : ℝ)
  | 12 => (-26890149 / 31250000000 : ℝ)
  | 13 => (-810738189 / 1000000000000 : ℝ)
  | 14 => (-760486561 / 1000000000000 : ℝ)
  | 15 => (-709727669 / 1000000000000 : ℝ)
  | 16 => (-6584593 / 10000000000 : ℝ)
  | 17 => (-606679243 / 1000000000000 : ℝ)
  | 18 => (-554385291 / 1000000000000 : ℝ)
  | 19 => (-501575241 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch061Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1220 : ℝ) + (j.val : ℝ)) / 1600)
      (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch061Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch061Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1220 : ℝ) + (j.val : ℝ)) / 1600)
    (((1220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch061Neg25WeightLower j.val) (hpThetaShiftTwoBatch061Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch061Neg25WeightLower, hpThetaShiftTwoBatch061Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch061Neg25_integral_bounds :
    (-6719747 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (61 / 80 : ℝ) ((61 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-782757 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch061Lower hpThetaJensenCellsBatch061Upper
    hpThetaShiftTwoBatch061Neg25WeightLower hpThetaShiftTwoBatch061Neg25WeightUpper hpThetaJensenCellsBatch061_bounds hpThetaShiftTwoBatch061Neg25_weight_bounds
  have hl : (-6719747 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch061Lower j * hpThetaShiftTwoBatch061Neg25WeightLower j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftTwoBatch061Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftTwoBatch061Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch061Lower j * hpThetaShiftTwoBatch061Neg25WeightUpper j)
        (hpThetaJensenCellsBatch061Upper j * hpThetaShiftTwoBatch061Neg25WeightUpper j) / 1600) ≤ (-782757 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch061Lower, hpThetaJensenCellsBatch061Upper,
      hpThetaShiftTwoBatch061Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1220 : ℝ) / 1600 = 61 / 80 by norm_num,
    show ((1220 : ℝ) + 20) / 1600 = (61 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch061Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch061Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch061Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch061Neg25_integral_bounds
end HodgeProofHP
