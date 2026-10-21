/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch029

/-! Exact signed weight and batch integral certificates, batch 29 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch029Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-204926029 / 1000000000000 : ℝ)
  | 1 => (-202540659 / 1000000000000 : ℝ)
  | 2 => (-200069057 / 1000000000000 : ℝ)
  | 3 => (-197510141 / 1000000000000 : ℝ)
  | 4 => (-97431413 / 500000000000 : ℝ)
  | 5 => (-24015753 / 125000000000 : ℝ)
  | 6 => (-37859729 / 200000000000 : ℝ)
  | 7 => (-37275919 / 200000000000 : ℝ)
  | 8 => (-5730243 / 31250000000 : ℝ)
  | 9 => (-180262089 / 1000000000000 : ℝ)
  | 10 => (-22132679 / 125000000000 : ℝ)
  | 11 => (-173764699 / 1000000000000 : ℝ)
  | 12 => (-34074157 / 200000000000 : ℝ)
  | 13 => (-8343929 / 50000000000 : ℝ)
  | 14 => (-163286973 / 1000000000000 : ℝ)
  | 15 => (-159594849 / 1000000000000 : ℝ)
  | 16 => (-19475137 / 125000000000 : ℝ)
  | 17 => (-30380919 / 200000000000 : ℝ)
  | 18 => (-14790423 / 100000000000 : ℝ)
  | 19 => (-898743 / 6250000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch029Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-101270329 / 500000000000 : ℝ)
  | 1 => (-3126079 / 15625000000 : ℝ)
  | 2 => (-9875507 / 50000000000 : ℝ)
  | 3 => (-7794513 / 40000000000 : ℝ)
  | 4 => (-192126023 / 1000000000000 : ℝ)
  | 5 => (-47324661 / 250000000000 : ℝ)
  | 6 => (-93189797 / 500000000000 : ℝ)
  | 7 => (-7334711 / 40000000000 : ℝ)
  | 8 => (-22532761 / 125000000000 : ℝ)
  | 9 => (-177061431 / 1000000000000 : ℝ)
  | 10 => (-86882349 / 500000000000 : ℝ)
  | 11 => (-5324087 / 31250000000 : ℝ)
  | 12 => (-166878579 / 1000000000000 : ℝ)
  | 13 => (-40821743 / 250000000000 : ℝ)
  | 14 => (-4987339 / 31250000000 : ℝ)
  | 15 => (-31160219 / 200000000000 : ℝ)
  | 16 => (-75952297 / 500000000000 : ℝ)
  | 17 => (-147904229 / 1000000000000 : ℝ)
  | 18 => (-143798879 / 1000000000000 : ℝ)
  | 19 => (-5583497 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch029Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((580 : ℝ) + (j.val : ℝ)) / 1600)
      (((580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch029Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch029Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((580 : ℝ) + (j.val : ℝ)) / 1600)
    (((580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch029Neg100WeightLower j.val) (hpThetaShiftTwoBatch029Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch029Neg100WeightLower, hpThetaShiftTwoBatch029Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch029Neg100_integral_bounds :
    (-503551331 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-974907763 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch029Lower hpThetaJensenCellsBatch029Upper
    hpThetaShiftTwoBatch029Neg100WeightLower hpThetaShiftTwoBatch029Neg100WeightUpper hpThetaJensenCellsBatch029_bounds hpThetaShiftTwoBatch029Neg100_weight_bounds
  have hl : (-503551331 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch029Lower j * hpThetaShiftTwoBatch029Neg100WeightLower j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftTwoBatch029Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftTwoBatch029Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch029Lower j * hpThetaShiftTwoBatch029Neg100WeightUpper j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftTwoBatch029Neg100WeightUpper j) / 1600) ≤ (-974907763 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftTwoBatch029Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (580 : ℝ) / 1600 = 29 / 80 by norm_num,
    show ((580 : ℝ) + 20) / 1600 = (29 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch029Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-178919077 / 500000000000 : ℝ)
  | 1 => (-5643141 / 15625000000 : ℝ)
  | 2 => (-364481149 / 1000000000000 : ℝ)
  | 3 => (-91949511 / 250000000000 : ℝ)
  | 4 => (-23194451 / 62500000000 : ℝ)
  | 5 => (-374420167 / 1000000000000 : ℝ)
  | 6 => (-188862197 / 500000000000 : ℝ)
  | 7 => (-190511693 / 500000000000 : ℝ)
  | 8 => (-3074533 / 8000000000 : ℝ)
  | 9 => (-38760359 / 100000000000 : ℝ)
  | 10 => (-312707 / 800000000 : ℝ)
  | 11 => (-394156569 / 1000000000000 : ℝ)
  | 12 => (-198710753 / 500000000000 : ℝ)
  | 13 => (-400678011 / 1000000000000 : ℝ)
  | 14 => (-40392553 / 100000000000 : ℝ)
  | 15 => (-407163501 / 1000000000000 : ℝ)
  | 16 => (-410391357 / 1000000000000 : ℝ)
  | 17 => (-206804261 / 500000000000 : ℝ)
  | 18 => (-83362883 / 200000000000 : ℝ)
  | 19 => (-8400169 / 20000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch029Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-44314127 / 125000000000 : ℝ)
  | 1 => (-357838153 / 1000000000000 : ℝ)
  | 2 => (-361161023 / 1000000000000 : ℝ)
  | 3 => (-91120287 / 250000000000 : ℝ)
  | 4 => (-367798043 / 1000000000000 : ℝ)
  | 5 => (-74222243 / 200000000000 : ℝ)
  | 6 => (-187210083 / 500000000000 : ℝ)
  | 7 => (-377724393 / 1000000000000 : ℝ)
  | 8 => (-76204677 / 200000000000 : ℝ)
  | 9 => (-24019789 / 62500000000 : ℝ)
  | 10 => (-387603589 / 1000000000000 : ℝ)
  | 11 => (-390883749 / 1000000000000 : ℝ)
  | 12 => (-49269571 / 125000000000 : ℝ)
  | 13 => (-79484301 / 200000000000 : ℝ)
  | 14 => (-40067801 / 100000000000 : ℝ)
  | 15 => (-403925529 / 1000000000000 : ℝ)
  | 16 => (-814327 / 2000000000 : ℝ)
  | 17 => (-102597839 / 250000000000 : ℝ)
  | 18 => (-413608521 / 1000000000000 : ℝ)
  | 19 => (-208407207 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch029Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((580 : ℝ) + (j.val : ℝ)) / 1600)
      (((580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch029Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch029Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((580 : ℝ) + (j.val : ℝ)) / 1600)
    (((580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch029Neg65WeightLower j.val) (hpThetaShiftTwoBatch029Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch029Neg65WeightLower, hpThetaShiftTwoBatch029Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch029Neg65_integral_bounds :
    (-1101611919 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-2154219699 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch029Lower hpThetaJensenCellsBatch029Upper
    hpThetaShiftTwoBatch029Neg65WeightLower hpThetaShiftTwoBatch029Neg65WeightUpper hpThetaJensenCellsBatch029_bounds hpThetaShiftTwoBatch029Neg65_weight_bounds
  have hl : (-1101611919 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch029Lower j * hpThetaShiftTwoBatch029Neg65WeightLower j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftTwoBatch029Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftTwoBatch029Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch029Lower j * hpThetaShiftTwoBatch029Neg65WeightUpper j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftTwoBatch029Neg65WeightUpper j) / 1600) ≤ (-2154219699 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftTwoBatch029Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (580 : ℝ) / 1600 = 29 / 80 by norm_num,
    show ((580 : ℝ) + 20) / 1600 = (29 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch029Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-78631989 / 500000000000 : ℝ)
  | 1 => (-80476921 / 500000000000 : ℝ)
  | 2 => (-164672063 / 1000000000000 : ℝ)
  | 3 => (-33683721 / 200000000000 : ℝ)
  | 4 => (-172193431 / 1000000000000 : ℝ)
  | 5 => (-87998249 / 500000000000 : ℝ)
  | 6 => (-89913881 / 500000000000 : ℝ)
  | 7 => (-7347487 / 40000000000 : ℝ)
  | 8 => (-187574687 / 1000000000000 : ℝ)
  | 9 => (-191490243 / 1000000000000 : ℝ)
  | 10 => (-97716893 / 500000000000 : ℝ)
  | 11 => (-24925657 / 125000000000 : ℝ)
  | 12 => (-50851147 / 250000000000 : ℝ)
  | 13 => (-207431717 / 1000000000000 : ℝ)
  | 14 => (-52871643 / 250000000000 : ℝ)
  | 15 => (-215569079 / 1000000000000 : ℝ)
  | 16 => (-109839581 / 500000000000 : ℝ)
  | 17 => (-223816739 / 1000000000000 : ℝ)
  | 18 => (-7124429 / 31250000000 : ℝ)
  | 19 => (-232174041 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch029Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-153602503 / 1000000000000 : ℝ)
  | 1 => (-157263977 / 1000000000000 : ℝ)
  | 2 => (-160953841 / 1000000000000 : ℝ)
  | 3 => (-82336031 / 500000000000 : ℝ)
  | 4 => (-42104651 / 250000000000 : ℝ)
  | 5 => (-17219343 / 100000000000 : ℝ)
  | 6 => (-175996497 / 1000000000000 : ℝ)
  | 7 => (-179827761 / 1000000000000 : ℝ)
  | 8 => (-91843587 / 500000000000 : ℝ)
  | 9 => (-93787343 / 500000000000 : ℝ)
  | 10 => (-95745121 / 500000000000 : ℝ)
  | 11 => (-39086757 / 200000000000 : ℝ)
  | 12 => (-39881051 / 200000000000 : ℝ)
  | 13 => (-203404587 / 1000000000000 : ℝ)
  | 14 => (-51857929 / 250000000000 : ℝ)
  | 15 => (-211486571 / 1000000000000 : ℝ)
  | 16 => (-107784539 / 500000000000 : ℝ)
  | 17 => (-219679161 / 1000000000000 : ℝ)
  | 18 => (-111908369 / 500000000000 : ℝ)
  | 19 => (-227981727 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch029Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((580 : ℝ) + (j.val : ℝ)) / 1600)
      (((580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch029Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch029Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((580 : ℝ) + (j.val : ℝ)) / 1600)
    (((580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch029Neg45WeightLower j.val) (hpThetaShiftTwoBatch029Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch029Neg45WeightLower, hpThetaShiftTwoBatch029Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch029Neg45_integral_bounds :
    (-547900053 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-132324273 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch029Lower hpThetaJensenCellsBatch029Upper
    hpThetaShiftTwoBatch029Neg45WeightLower hpThetaShiftTwoBatch029Neg45WeightUpper hpThetaJensenCellsBatch029_bounds hpThetaShiftTwoBatch029Neg45_weight_bounds
  have hl : (-547900053 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch029Lower j * hpThetaShiftTwoBatch029Neg45WeightLower j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftTwoBatch029Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftTwoBatch029Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch029Lower j * hpThetaShiftTwoBatch029Neg45WeightUpper j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftTwoBatch029Neg45WeightUpper j) / 1600) ≤ (-132324273 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftTwoBatch029Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (580 : ℝ) / 1600 = 29 / 80 by norm_num,
    show ((580 : ℝ) + 20) / 1600 = (29 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch029Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (83203313 / 250000000000 : ℝ)
  | 1 => (332269479 / 1000000000000 : ℝ)
  | 2 => (41462519 / 125000000000 : ℝ)
  | 3 => (165552537 / 500000000000 : ℝ)
  | 4 => (165242023 / 500000000000 : ℝ)
  | 5 => (41229609 / 125000000000 : ℝ)
  | 6 => (164581677 / 500000000000 : ℝ)
  | 7 => (65692659 / 200000000000 : ℝ)
  | 8 => (20483531 / 62500000000 : ℝ)
  | 9 => (326982759 / 1000000000000 : ℝ)
  | 10 => (326201887 / 1000000000000 : ℝ)
  | 11 => (325393681 / 1000000000000 : ℝ)
  | 12 => (324557943 / 1000000000000 : ℝ)
  | 13 => (12947779 / 40000000000 : ℝ)
  | 14 => (322803079 / 1000000000000 : ℝ)
  | 15 => (321883557 / 1000000000000 : ℝ)
  | 16 => (32093571 / 100000000000 : ℝ)
  | 17 => (319959339 / 1000000000000 : ℝ)
  | 18 => (318954247 / 1000000000000 : ℝ)
  | 19 => (79480059 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch029Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (333331669 / 1000000000000 : ℝ)
  | 1 => (332813253 / 1000000000000 : ℝ)
  | 2 => (8306737 / 25000000000 : ℝ)
  | 3 => (331700153 / 1000000000000 : ℝ)
  | 4 => (13244203 / 40000000000 : ℝ)
  | 5 => (330484047 / 1000000000000 : ℝ)
  | 6 => (329836873 / 1000000000000 : ℝ)
  | 7 => (65832671 / 200000000000 : ℝ)
  | 8 => (5132239 / 15625000000 : ℝ)
  | 9 => (327736497 / 1000000000000 : ℝ)
  | 10 => (8174569 / 25000000000 : ℝ)
  | 11 => (10193809 / 31250000000 : ℝ)
  | 12 => (162696841 / 500000000000 : ℝ)
  | 13 => (40569743 / 125000000000 : ℝ)
  | 14 => (80923619 / 250000000000 : ℝ)
  | 15 => (8070077 / 25000000000 : ℝ)
  | 16 => (160941779 / 500000000000 : ℝ)
  | 17 => (320935711 / 1000000000000 : ℝ)
  | 18 => (15997967 / 50000000000 : ℝ)
  | 19 => (39869281 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch029Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((580 : ℝ) + (j.val : ℝ)) / 1600)
      (((580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch029Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch029Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((580 : ℝ) + (j.val : ℝ)) / 1600)
    (((580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch029Neg25WeightLower j.val) (hpThetaShiftTwoBatch029Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch029Neg25WeightLower, hpThetaShiftTwoBatch029Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch029Neg25_integral_bounds :
    (1824190403 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (29 / 80 : ℝ) ((29 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (1854295317 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch029Lower hpThetaJensenCellsBatch029Upper
    hpThetaShiftTwoBatch029Neg25WeightLower hpThetaShiftTwoBatch029Neg25WeightUpper hpThetaJensenCellsBatch029_bounds hpThetaShiftTwoBatch029Neg25_weight_bounds
  have hl : (1824190403 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch029Lower j * hpThetaShiftTwoBatch029Neg25WeightLower j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftTwoBatch029Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftTwoBatch029Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch029Lower j * hpThetaShiftTwoBatch029Neg25WeightUpper j)
        (hpThetaJensenCellsBatch029Upper j * hpThetaShiftTwoBatch029Neg25WeightUpper j) / 1600) ≤ (1854295317 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch029Lower, hpThetaJensenCellsBatch029Upper,
      hpThetaShiftTwoBatch029Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (580 : ℝ) / 1600 = 29 / 80 by norm_num,
    show ((580 : ℝ) + 20) / 1600 = (29 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch029Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch029Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch029Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch029Neg25_integral_bounds
end HodgeProofHP
