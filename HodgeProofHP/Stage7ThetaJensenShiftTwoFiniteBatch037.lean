/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch037

/-! Exact signed weight and batch integral certificates, batch 37 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch037Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (960355499 / 500000000000 : ℝ)
  | 1 => (60844899 / 31250000000 : ℝ)
  | 2 => (1973492479 / 1000000000000 : ℝ)
  | 3 => (1000037847 / 500000000000 : ℝ)
  | 4 => (63336997 / 31250000000 : ℝ)
  | 5 => (205361453 / 100000000000 : ℝ)
  | 6 => (2080564917 / 1000000000000 : ℝ)
  | 7 => (1053816171 / 500000000000 : ℝ)
  | 8 => (1067407001 / 500000000000 : ℝ)
  | 9 => (1081053511 / 500000000000 : ℝ)
  | 10 => (43790169 / 20000000000 : ℝ)
  | 11 => (443403051 / 200000000000 : ℝ)
  | 12 => (280578041 / 125000000000 : ℝ)
  | 13 => (1136166241 / 500000000000 : ℝ)
  | 14 => (1150068223 / 500000000000 : ℝ)
  | 15 => (232803287 / 100000000000 : ℝ)
  | 16 => (29450229 / 12500000000 : ℝ)
  | 17 => (596022319 / 250000000000 : ℝ)
  | 18 => (2412242137 / 1000000000000 : ℝ)
  | 19 => (2440473211 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch037Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1947036769 / 1000000000000 : ℝ)
  | 1 => (1541791 / 781250000 : ℝ)
  | 2 => (400015139 / 200000000000 : ℝ)
  | 3 => (405356781 / 200000000000 : ℝ)
  | 4 => (2053614531 / 1000000000000 : ℝ)
  | 5 => (1040282459 / 500000000000 : ℝ)
  | 6 => (2107632343 / 1000000000000 : ℝ)
  | 7 => (2134814003 / 1000000000000 : ℝ)
  | 8 => (2162107023 / 1000000000000 : ℝ)
  | 9 => (2189508451 / 1000000000000 : ℝ)
  | 10 => (277126907 / 125000000000 : ℝ)
  | 11 => (2244624329 / 1000000000000 : ℝ)
  | 12 => (2272332483 / 1000000000000 : ℝ)
  | 13 => (2300136447 / 1000000000000 : ℝ)
  | 14 => (2328032871 / 1000000000000 : ℝ)
  | 15 => (2356018321 / 1000000000000 : ℝ)
  | 16 => (2384089277 / 1000000000000 : ℝ)
  | 17 => (1206121069 / 500000000000 : ℝ)
  | 18 => (610118303 / 250000000000 : ℝ)
  | 19 => (617194681 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch037Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((740 : ℝ) + (j.val : ℝ)) / 1600)
      (((740 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch037Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch037Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((740 : ℝ) + (j.val : ℝ)) / 1600)
    (((740 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch037Neg100WeightLower j.val) (hpThetaShiftTwoBatch037Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch037Neg100WeightLower, hpThetaShiftTwoBatch037Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch037Neg100_integral_bounds :
    (4683254719 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (4817658739 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (740 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch037Lower hpThetaJensenCellsBatch037Upper
    hpThetaShiftTwoBatch037Neg100WeightLower hpThetaShiftTwoBatch037Neg100WeightUpper hpThetaJensenCellsBatch037_bounds hpThetaShiftTwoBatch037Neg100_weight_bounds
  have hl : (4683254719 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch037Lower j * hpThetaShiftTwoBatch037Neg100WeightLower j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftTwoBatch037Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftTwoBatch037Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch037Lower j * hpThetaShiftTwoBatch037Neg100WeightUpper j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftTwoBatch037Neg100WeightUpper j) / 1600) ≤ (4817658739 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftTwoBatch037Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (740 : ℝ) / 1600 = 37 / 80 by norm_num,
    show ((740 : ℝ) + 20) / 1600 = (37 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch037Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-363190437 / 1000000000000 : ℝ)
  | 1 => (-355654211 / 1000000000000 : ℝ)
  | 2 => (-347957481 / 1000000000000 : ℝ)
  | 3 => (-340098859 / 1000000000000 : ℝ)
  | 4 => (-66415391 / 200000000000 : ℝ)
  | 5 => (-161945189 / 500000000000 : ℝ)
  | 6 => (-315537737 / 1000000000000 : ℝ)
  | 7 => (-307017639 / 1000000000000 : ℝ)
  | 8 => (-74582173 / 250000000000 : ℝ)
  | 9 => (-144734751 / 500000000000 : ℝ)
  | 10 => (-70109669 / 250000000000 : ℝ)
  | 11 => (-13561741 / 50000000000 : ℝ)
  | 12 => (-261856541 / 1000000000000 : ℝ)
  | 13 => (-50460489 / 200000000000 : ℝ)
  | 14 => (-242571139 / 1000000000000 : ℝ)
  | 15 => (-23266123 / 100000000000 : ℝ)
  | 16 => (-3477677 / 15625000000 : ℝ)
  | 17 => (-212300039 / 1000000000000 : ℝ)
  | 18 => (-100922987 / 500000000000 : ℝ)
  | 19 => (-2987621 / 15625000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch037Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-35565421 / 100000000000 : ℝ)
  | 1 => (-8698937 / 25000000000 : ℝ)
  | 2 => (-170049429 / 500000000000 : ℝ)
  | 3 => (-166038477 / 500000000000 : ℝ)
  | 4 => (-323890377 / 1000000000000 : ℝ)
  | 5 => (-39442217 / 125000000000 : ℝ)
  | 6 => (-153508819 / 500000000000 : ℝ)
  | 7 => (-298328691 / 1000000000000 : ℝ)
  | 8 => (-289469501 / 1000000000000 : ℝ)
  | 9 => (-11217547 / 40000000000 : ℝ)
  | 10 => (-271234819 / 1000000000000 : ℝ)
  | 11 => (-13092827 / 50000000000 : ℝ)
  | 12 => (-63075611 / 250000000000 : ℝ)
  | 13 => (-121285569 / 500000000000 : ℝ)
  | 14 => (-232661229 / 1000000000000 : ℝ)
  | 15 => (-222571327 / 1000000000000 : ℝ)
  | 16 => (-106150019 / 500000000000 : ℝ)
  | 17 => (-201845973 / 1000000000000 : ℝ)
  | 18 => (-191207743 / 1000000000000 : ℝ)
  | 19 => (-4509599 / 25000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch037Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((740 : ℝ) + (j.val : ℝ)) / 1600)
      (((740 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch037Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch037Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((740 : ℝ) + (j.val : ℝ)) / 1600)
    (((740 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch037Neg65WeightLower j.val) (hpThetaShiftTwoBatch037Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch037Neg65WeightLower, hpThetaShiftTwoBatch037Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch037Neg65_integral_bounds :
    (-622714367 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-29667843 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (740 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch037Lower hpThetaJensenCellsBatch037Upper
    hpThetaShiftTwoBatch037Neg65WeightLower hpThetaShiftTwoBatch037Neg65WeightUpper hpThetaJensenCellsBatch037_bounds hpThetaShiftTwoBatch037Neg65_weight_bounds
  have hl : (-622714367 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch037Lower j * hpThetaShiftTwoBatch037Neg65WeightLower j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftTwoBatch037Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftTwoBatch037Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch037Lower j * hpThetaShiftTwoBatch037Neg65WeightUpper j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftTwoBatch037Neg65WeightUpper j) / 1600) ≤ (-29667843 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftTwoBatch037Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (740 : ℝ) / 1600 = 37 / 80 by norm_num,
    show ((740 : ℝ) + 20) / 1600 = (37 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch037Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-122730701 / 125000000000 : ℝ)
  | 1 => (-246713601 / 250000000000 : ℝ)
  | 2 => (-495914379 / 500000000000 : ℝ)
  | 3 => (-996767807 / 1000000000000 : ℝ)
  | 4 => (-1001670683 / 1000000000000 : ℝ)
  | 5 => (-1006536511 / 1000000000000 : ℝ)
  | 6 => (-126420551 / 125000000000 : ℝ)
  | 7 => (-203230697 / 200000000000 : ℝ)
  | 8 => (-510451423 / 500000000000 : ℝ)
  | 9 => (-256402897 / 250000000000 : ℝ)
  | 10 => (-1030278801 / 1000000000000 : ℝ)
  | 11 => (-64681473 / 62500000000 : ℝ)
  | 12 => (-1039484967 / 1000000000000 : ℝ)
  | 13 => (-208804413 / 200000000000 : ℝ)
  | 14 => (-524256963 / 500000000000 : ℝ)
  | 15 => (-210591921 / 200000000000 : ℝ)
  | 16 => (-1057358151 / 1000000000000 : ℝ)
  | 17 => (-530854303 / 500000000000 : ℝ)
  | 18 => (-266502501 / 250000000000 : ℝ)
  | 19 => (-8562091 / 8000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch037Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-488401611 / 500000000000 : ℝ)
  | 1 => (-981845607 / 1000000000000 : ℝ)
  | 2 => (-986854403 / 1000000000000 : ℝ)
  | 3 => (-991828757 / 1000000000000 : ℝ)
  | 4 => (-498383903 / 500000000000 : ℝ)
  | 5 => (-500835341 / 500000000000 : ℝ)
  | 6 => (-100653651 / 100000000000 : ℝ)
  | 7 => (-1011364407 / 1000000000000 : ℝ)
  | 8 => (-254038371 / 250000000000 : ℝ)
  | 9 => (-204180569 / 200000000000 : ℝ)
  | 10 => (-1025611587 / 1000000000000 : ℝ)
  | 11 => (-2575697 / 2500000000 : ℝ)
  | 12 => (-1034903567 / 1000000000000 : ℝ)
  | 13 => (-519742483 / 500000000000 : ℝ)
  | 14 => (-65251379 / 62500000000 : ℝ)
  | 15 => (-41940557 / 40000000000 : ℝ)
  | 16 => (-263239901 / 250000000000 : ℝ)
  | 17 => (-21147163 / 20000000000 : ℝ)
  | 18 => (-212341721 / 200000000000 : ℝ)
  | 19 => (-1066010003 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch037Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((740 : ℝ) + (j.val : ℝ)) / 1600)
      (((740 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch037Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch037Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((740 : ℝ) + (j.val : ℝ)) / 1600)
    (((740 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch037Neg45WeightLower j.val) (hpThetaShiftTwoBatch037Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch037Neg45WeightLower, hpThetaShiftTwoBatch037Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch037Neg45_integral_bounds :
    (-562139003 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-34426493 / 15625000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (740 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch037Lower hpThetaJensenCellsBatch037Upper
    hpThetaShiftTwoBatch037Neg45WeightLower hpThetaShiftTwoBatch037Neg45WeightUpper hpThetaJensenCellsBatch037_bounds hpThetaShiftTwoBatch037Neg45_weight_bounds
  have hl : (-562139003 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch037Lower j * hpThetaShiftTwoBatch037Neg45WeightLower j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftTwoBatch037Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftTwoBatch037Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch037Lower j * hpThetaShiftTwoBatch037Neg45WeightUpper j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftTwoBatch037Neg45WeightUpper j) / 1600) ≤ (-34426493 / 15625000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftTwoBatch037Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (740 : ℝ) / 1600 = 37 / 80 by norm_num,
    show ((740 : ℝ) + 20) / 1600 = (37 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch037Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-102922719 / 500000000000 : ℝ)
  | 1 => (-8511029 / 40000000000 : ℝ)
  | 2 => (-109878387 / 500000000000 : ℝ)
  | 3 => (-226788639 / 1000000000000 : ℝ)
  | 4 => (-233871371 / 1000000000000 : ℝ)
  | 5 => (-12050251 / 50000000000 : ℝ)
  | 6 => (-124094817 / 500000000000 : ℝ)
  | 7 => (-31928157 / 125000000000 : ℝ)
  | 8 => (-26271193 / 100000000000 : ℝ)
  | 9 => (-8439053 / 31250000000 : ℝ)
  | 10 => (-2167489 / 7812500000 : ℝ)
  | 11 => (-284878653 / 1000000000000 : ℝ)
  | 12 => (-36546239 / 125000000000 : ℝ)
  | 13 => (-299912401 / 1000000000000 : ℝ)
  | 14 => (-76876537 / 250000000000 : ℝ)
  | 15 => (-157575589 / 500000000000 : ℝ)
  | 16 => (-80711879 / 250000000000 : ℝ)
  | 17 => (-330595181 / 1000000000000 : ℝ)
  | 18 => (-338394193 / 1000000000000 : ℝ)
  | 19 => (-43280571 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch037Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6217683 / 31250000000 : ℝ)
  | 1 => (-205845437 / 1000000000000 : ℝ)
  | 2 => (-53193931 / 250000000000 : ℝ)
  | 3 => (-219756773 / 1000000000000 : ℝ)
  | 4 => (-113394319 / 500000000000 : ℝ)
  | 5 => (-23387137 / 100000000000 : ℝ)
  | 6 => (-241005019 / 1000000000000 : ℝ)
  | 7 => (-248189633 / 1000000000000 : ℝ)
  | 8 => (-51085051 / 200000000000 : ℝ)
  | 9 => (-262711929 / 1000000000000 : ℝ)
  | 10 => (-54009939 / 200000000000 : ℝ)
  | 11 => (-277438591 / 1000000000000 : ℝ)
  | 12 => (-71219663 / 250000000000 : ℝ)
  | 13 => (-292369911 / 1000000000000 : ℝ)
  | 14 => (-749781 / 2500000000 : ℝ)
  | 15 => (-307506147 / 1000000000000 : ℝ)
  | 16 => (-315151177 / 1000000000000 : ℝ)
  | 17 => (-64569503 / 200000000000 : ℝ)
  | 18 => (-16529759 / 50000000000 : ℝ)
  | 19 => (-21149637 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch037Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((740 : ℝ) + (j.val : ℝ)) / 1600)
      (((740 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch037Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch037Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((740 : ℝ) + (j.val : ℝ)) / 1600)
    (((740 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch037Neg25WeightLower j.val) (hpThetaShiftTwoBatch037Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch037Neg25WeightLower, hpThetaShiftTwoBatch037Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch037Neg25_integral_bounds :
    (-119590117 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-572737009 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (740 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch037Lower hpThetaJensenCellsBatch037Upper
    hpThetaShiftTwoBatch037Neg25WeightLower hpThetaShiftTwoBatch037Neg25WeightUpper hpThetaJensenCellsBatch037_bounds hpThetaShiftTwoBatch037Neg25_weight_bounds
  have hl : (-119590117 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch037Lower j * hpThetaShiftTwoBatch037Neg25WeightLower j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftTwoBatch037Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftTwoBatch037Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch037Lower j * hpThetaShiftTwoBatch037Neg25WeightUpper j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftTwoBatch037Neg25WeightUpper j) / 1600) ≤ (-572737009 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftTwoBatch037Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (740 : ℝ) / 1600 = 37 / 80 by norm_num,
    show ((740 : ℝ) + 20) / 1600 = (37 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch037Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch037Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch037Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch037Neg25_integral_bounds
end HodgeProofHP
