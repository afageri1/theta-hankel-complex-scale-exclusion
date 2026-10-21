/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch024

/-! Exact signed weight and batch integral certificates, batch 24 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch024Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-14303571429 / 1000000000000 : ℝ)
  | 1 => (-2834858483 / 200000000000 : ℝ)
  | 2 => (-3510224067 / 250000000000 : ℝ)
  | 3 => (-1737918497 / 125000000000 : ℝ)
  | 4 => (-3440403157 / 250000000000 : ℝ)
  | 5 => (-6807827711 / 500000000000 : ℝ)
  | 6 => (-2693088333 / 200000000000 : ℝ)
  | 7 => (-13310936787 / 1000000000000 : ℝ)
  | 8 => (-13152106337 / 1000000000000 : ℝ)
  | 9 => (-3247228999 / 250000000000 : ℝ)
  | 10 => (-12821331577 / 1000000000000 : ℝ)
  | 11 => (-6324659517 / 500000000000 : ℝ)
  | 12 => (-12472844469 / 1000000000000 : ℝ)
  | 13 => (-12291874133 / 1000000000000 : ℝ)
  | 14 => (-2421274887 / 200000000000 : ℝ)
  | 15 => (-5958155973 / 500000000000 : ℝ)
  | 16 => (-366301669 / 31250000000 : ℝ)
  | 17 => (-11522365737 / 1000000000000 : ℝ)
  | 18 => (-1131841603 / 100000000000 : ℝ)
  | 19 => (-2777442893 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch024Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-7087146207 / 500000000000 : ℝ)
  | 1 => (-14040896267 / 1000000000000 : ℝ)
  | 2 => (-556133919 / 40000000000 : ℝ)
  | 3 => (-13761612627 / 1000000000000 : ℝ)
  | 4 => (-13615655421 / 1000000000000 : ℝ)
  | 5 => (-105198763 / 7812500000 : ℝ)
  | 6 => (-6655468393 / 500000000000 : ℝ)
  | 7 => (-411003323 / 31250000000 : ℝ)
  | 8 => (-2597783199 / 200000000000 : ℝ)
  | 9 => (-1602666447 / 125000000000 : ℝ)
  | 10 => (-12649319033 / 1000000000000 : ℝ)
  | 11 => (-3118211117 / 250000000000 : ℝ)
  | 12 => (-3072968533 / 250000000000 : ℝ)
  | 13 => (-6053187217 / 500000000000 : ℝ)
  | 14 => (-2383262389 / 200000000000 : ℝ)
  | 15 => (-11721653407 / 1000000000000 : ℝ)
  | 16 => (-1440295717 / 125000000000 : ℝ)
  | 17 => (-11318416029 / 1000000000000 : ℝ)
  | 18 => (-11109771571 / 1000000000000 : ℝ)
  | 19 => (-5448199919 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch024Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((480 : ℝ) + (j.val : ℝ)) / 1600)
      (((480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch024Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch024Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((480 : ℝ) + (j.val : ℝ)) / 1600)
    (((480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch024Neg100WeightLower j.val) (hpThetaShiftOneBatch024Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch024Neg100WeightLower, hpThetaShiftOneBatch024Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch024Neg100_integral_bounds :
    (-114276198531 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-6956053051 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch024Lower hpThetaJensenCellsBatch024Upper
    hpThetaShiftOneBatch024Neg100WeightLower hpThetaShiftOneBatch024Neg100WeightUpper hpThetaJensenCellsBatch024_bounds hpThetaShiftOneBatch024Neg100_weight_bounds
  have hl : (-114276198531 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch024Lower j * hpThetaShiftOneBatch024Neg100WeightLower j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftOneBatch024Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftOneBatch024Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch024Lower j * hpThetaShiftOneBatch024Neg100WeightUpper j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftOneBatch024Neg100WeightUpper j) / 1600) ≤ (-6956053051 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftOneBatch024Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (480 : ℝ) / 1600 = 24 / 80 by norm_num,
    show ((480 : ℝ) + 20) / 1600 = (24 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch024Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2047459971 / 100000000000 : ℝ)
  | 1 => (-4119752081 / 200000000000 : ℝ)
  | 2 => (-10360960777 / 500000000000 : ℝ)
  | 3 => (-20844060449 / 1000000000000 : ℝ)
  | 4 => (-20965154261 / 1000000000000 : ℝ)
  | 5 => (-527129501 / 25000000000 : ℝ)
  | 6 => (-10602057359 / 500000000000 : ℝ)
  | 7 => (-4264387021 / 200000000000 : ℝ)
  | 8 => (-2679827237 / 125000000000 : ℝ)
  | 9 => (-4310827933 / 200000000000 : ℝ)
  | 10 => (-21668476873 / 1000000000000 : ℝ)
  | 11 => (-1089080293 / 50000000000 : ℝ)
  | 12 => (-2736687857 / 125000000000 : ℝ)
  | 13 => (-22004143973 / 1000000000000 : ℝ)
  | 14 => (-2211350521 / 100000000000 : ℝ)
  | 15 => (-11110781227 / 500000000000 : ℝ)
  | 16 => (-558207287 / 25000000000 : ℝ)
  | 17 => (-22433667951 / 1000000000000 : ℝ)
  | 18 => (-22537667421 / 1000000000000 : ℝ)
  | 19 => (-11320132667 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch024Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-20349462053 / 1000000000000 : ℝ)
  | 1 => (-20474599709 / 1000000000000 : ℝ)
  | 2 => (-5149690101 / 250000000000 : ℝ)
  | 3 => (-20721921553 / 1000000000000 : ℝ)
  | 4 => (-651376889 / 31250000000 : ℝ)
  | 5 => (-1048257713 / 50000000000 : ℝ)
  | 6 => (-21085180039 / 1000000000000 : ℝ)
  | 7 => (-21204114717 / 1000000000000 : ℝ)
  | 8 => (-83288809 / 3906250000 : ℝ)
  | 9 => (-4287723579 / 200000000000 : ℝ)
  | 10 => (-1347133729 / 62500000000 : ℝ)
  | 11 => (-2708559609 / 125000000000 : ℝ)
  | 12 => (-21781605859 / 1000000000000 : ℝ)
  | 13 => (-4378700571 / 200000000000 : ℝ)
  | 14 => (-5501035993 / 250000000000 : ℝ)
  | 15 => (-22113505209 / 1000000000000 : ℝ)
  | 16 => (-22221562453 / 1000000000000 : ℝ)
  | 17 => (-22328291479 / 1000000000000 : ℝ)
  | 18 => (-448673359 / 20000000000 : ℝ)
  | 19 => (-1126883371 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch024Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((480 : ℝ) + (j.val : ℝ)) / 1600)
      (((480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch024Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch024Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((480 : ℝ) + (j.val : ℝ)) / 1600)
    (((480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch024Neg65WeightLower j.val) (hpThetaShiftOneBatch024Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch024Neg65WeightLower, hpThetaShiftOneBatch024Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch024Neg65_integral_bounds :
    (-47952957071 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-94151950953 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch024Lower hpThetaJensenCellsBatch024Upper
    hpThetaShiftOneBatch024Neg65WeightLower hpThetaShiftOneBatch024Neg65WeightUpper hpThetaJensenCellsBatch024_bounds hpThetaShiftOneBatch024Neg65_weight_bounds
  have hl : (-47952957071 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch024Lower j * hpThetaShiftOneBatch024Neg65WeightLower j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftOneBatch024Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftOneBatch024Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch024Lower j * hpThetaShiftOneBatch024Neg65WeightUpper j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftOneBatch024Neg65WeightUpper j) / 1600) ≤ (-94151950953 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftOneBatch024Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (480 : ℝ) / 1600 = 24 / 80 by norm_num,
    show ((480 : ℝ) + 20) / 1600 = (24 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch024Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1188050501 / 125000000000 : ℝ)
  | 1 => (-4835005839 / 500000000000 : ℝ)
  | 2 => (-9836244989 / 1000000000000 : ℝ)
  | 3 => (-10003097267 / 1000000000000 : ℝ)
  | 4 => (-2034112351 / 200000000000 : ℝ)
  | 5 => (-5169315807 / 500000000000 : ℝ)
  | 6 => (-10507299921 / 1000000000000 : ℝ)
  | 7 => (-10676559671 / 1000000000000 : ℝ)
  | 8 => (-433856151 / 40000000000 : ℝ)
  | 9 => (-5508412531 / 500000000000 : ℝ)
  | 10 => (-2796954069 / 250000000000 : ℝ)
  | 11 => (-70996063 / 6250000000 : ℝ)
  | 12 => (-11531479049 / 1000000000000 : ℝ)
  | 13 => (-11704135679 / 1000000000000 : ℝ)
  | 14 => (-11877332379 / 1000000000000 : ℝ)
  | 15 => (-482042459 / 40000000000 : ℝ)
  | 16 => (-12225315207 / 1000000000000 : ℝ)
  | 17 => (-6200042867 / 500000000000 : ℝ)
  | 18 => (-1571920641 / 125000000000 : ℝ)
  | 19 => (-6375572689 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch024Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-9339428571 / 1000000000000 : ℝ)
  | 1 => (-9504404007 / 1000000000000 : ℝ)
  | 2 => (-9670011677 / 1000000000000 : ℝ)
  | 3 => (-2459061247 / 250000000000 : ℝ)
  | 4 => (-5001548633 / 500000000000 : ℝ)
  | 5 => (-5085280877 / 500000000000 : ℝ)
  | 6 => (-10338631613 / 1000000000000 : ℝ)
  | 7 => (-131341249 / 12500000000 : ℝ)
  | 8 => (-1067655967 / 100000000000 : ℝ)
  | 9 => (-5423201887 / 500000000000 : ℝ)
  | 10 => (-11016825061 / 1000000000000 : ℝ)
  | 11 => (-447512651 / 40000000000 : ℝ)
  | 12 => (-11359370079 / 1000000000000 : ℝ)
  | 13 => (-1441434881 / 125000000000 : ℝ)
  | 14 => (-5852067839 / 500000000000 : ℝ)
  | 15 => (-5938666189 / 500000000000 : ℝ)
  | 16 => (-6025530737 / 500000000000 : ℝ)
  | 17 => (-6112657603 / 500000000000 : ℝ)
  | 18 => (-12400085733 / 1000000000000 : ℝ)
  | 19 => (-12575365127 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch024Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((480 : ℝ) + (j.val : ℝ)) / 1600)
      (((480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch024Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch024Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((480 : ℝ) + (j.val : ℝ)) / 1600)
    (((480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch024Neg40WeightLower j.val) (hpThetaShiftOneBatch024Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch024Neg40WeightLower, hpThetaShiftOneBatch024Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch024Neg40_integral_bounds :
    (-98579700833 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-47898861233 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch024Lower hpThetaJensenCellsBatch024Upper
    hpThetaShiftOneBatch024Neg40WeightLower hpThetaShiftOneBatch024Neg40WeightUpper hpThetaJensenCellsBatch024_bounds hpThetaShiftOneBatch024Neg40_weight_bounds
  have hl : (-98579700833 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch024Lower j * hpThetaShiftOneBatch024Neg40WeightLower j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftOneBatch024Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftOneBatch024Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch024Lower j * hpThetaShiftOneBatch024Neg40WeightUpper j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftOneBatch024Neg40WeightUpper j) / 1600) ≤ (-47898861233 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftOneBatch024Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (480 : ℝ) / 1600 = 24 / 80 by norm_num,
    show ((480 : ℝ) + 20) / 1600 = (24 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch024Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (11413066247 / 1000000000000 : ℝ)
  | 1 => (5673856891 / 500000000000 : ℝ)
  | 2 => (2256302447 / 200000000000 : ℝ)
  | 3 => (5607229917 / 500000000000 : ℝ)
  | 4 => (445862193 / 40000000000 : ℝ)
  | 5 => (2769448869 / 250000000000 : ℝ)
  | 6 => (5504090039 / 500000000000 : ℝ)
  | 7 => (170901671 / 15625000000 : ℝ)
  | 8 => (1358296801 / 125000000000 : ℝ)
  | 9 => (10794180827 / 1000000000000 : ℝ)
  | 10 => (10721124581 / 1000000000000 : ℝ)
  | 11 => (10647204071 / 1000000000000 : ℝ)
  | 12 => (5286208861 / 500000000000 : ℝ)
  | 13 => (524838199 / 50000000000 : ℝ)
  | 14 => (2084048263 / 200000000000 : ℝ)
  | 15 => (517142411 / 50000000000 : ℝ)
  | 16 => (2566145803 / 250000000000 : ℝ)
  | 17 => (2546361207 / 250000000000 : ℝ)
  | 18 => (10105431633 / 1000000000000 : ℝ)
  | 19 => (1002454221 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch024Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (11477571429 / 1000000000000 : ℝ)
  | 1 => (1426633281 / 125000000000 : ℝ)
  | 2 => (11347713783 / 1000000000000 : ℝ)
  | 3 => (2820378059 / 250000000000 : ℝ)
  | 4 => (2242891967 / 200000000000 : ℝ)
  | 5 => (5573277413 / 500000000000 : ℝ)
  | 6 => (11077795477 / 1000000000000 : ℝ)
  | 7 => (11008180079 / 1000000000000 : ℝ)
  | 8 => (2187541389 / 200000000000 : ℝ)
  | 9 => (10866374409 / 1000000000000 : ℝ)
  | 10 => (2698545207 / 250000000000 : ℝ)
  | 11 => (5360562291 / 500000000000 : ℝ)
  | 12 => (1330900509 / 125000000000 : ℝ)
  | 13 => (10572417723 / 1000000000000 : ℝ)
  | 14 => (10496763981 / 1000000000000 : ℝ)
  | 15 => (2605060329 / 250000000000 : ℝ)
  | 16 => (10342848221 / 1000000000000 : ℝ)
  | 17 => (10264583213 / 1000000000000 : ℝ)
  | 18 => (10185444829 / 1000000000000 : ℝ)
  | 19 => (5052715817 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch024Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((480 : ℝ) + (j.val : ℝ)) / 1600)
      (((480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch024Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch024Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((480 : ℝ) + (j.val : ℝ)) / 1600)
    (((480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch024Neg20WeightLower j.val) (hpThetaShiftOneBatch024Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch024Neg20WeightLower, hpThetaShiftOneBatch024Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch024Neg20_integral_bounds :
    (47173727517 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (24 / 80 : ℝ) ((24 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (96238701779 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch024Lower hpThetaJensenCellsBatch024Upper
    hpThetaShiftOneBatch024Neg20WeightLower hpThetaShiftOneBatch024Neg20WeightUpper hpThetaJensenCellsBatch024_bounds hpThetaShiftOneBatch024Neg20_weight_bounds
  have hl : (47173727517 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch024Lower j * hpThetaShiftOneBatch024Neg20WeightLower j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftOneBatch024Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftOneBatch024Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch024Lower j * hpThetaShiftOneBatch024Neg20WeightUpper j)
        (hpThetaJensenCellsBatch024Upper j * hpThetaShiftOneBatch024Neg20WeightUpper j) / 1600) ≤ (96238701779 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch024Lower, hpThetaJensenCellsBatch024Upper,
      hpThetaShiftOneBatch024Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (480 : ℝ) / 1600 = 24 / 80 by norm_num,
    show ((480 : ℝ) + 20) / 1600 = (24 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch024Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch024Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch024Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch024Neg20_integral_bounds
end HodgeProofHP
