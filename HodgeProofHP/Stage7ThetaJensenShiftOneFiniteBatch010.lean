/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch010

/-! Exact signed weight and batch integral certificates, batch 10 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch010Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (65250929 / 25000000000 : ℝ)
  | 1 => (1296057147 / 500000000000 : ℝ)
  | 2 => (1286702887 / 500000000000 : ℝ)
  | 3 => (2553906323 / 1000000000000 : ℝ)
  | 4 => (2533610753 / 1000000000000 : ℝ)
  | 5 => (251251397 / 100000000000 : ℝ)
  | 6 => (622652743 / 250000000000 : ℝ)
  | 7 => (2467896849 / 1000000000000 : ℝ)
  | 8 => (244436679 / 100000000000 : ℝ)
  | 9 => (2420016079 / 1000000000000 : ℝ)
  | 10 => (2394840097 / 1000000000000 : ℝ)
  | 11 => (296104291 / 125000000000 : ℝ)
  | 12 => (468398871 / 200000000000 : ℝ)
  | 13 => (2314315863 / 1000000000000 : ℝ)
  | 14 => (2285794643 / 1000000000000 : ℝ)
  | 15 => (225642659 / 100000000000 : ℝ)
  | 16 => (445241541 / 200000000000 : ℝ)
  | 17 => (1097567049 / 500000000000 : ℝ)
  | 18 => (2163201989 / 1000000000000 : ℝ)
  | 19 => (2130407707 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch010Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2627179737 / 1000000000000 : ℝ)
  | 1 => (2610037161 / 1000000000000 : ℝ)
  | 2 => (518422859 / 200000000000 : ℝ)
  | 3 => (102936231 / 40000000000 : ℝ)
  | 4 => (638476581 / 250000000000 : ℝ)
  | 5 => (1266805377 / 500000000000 : ℝ)
  | 6 => (2512513971 / 1000000000000 : ℝ)
  | 7 => (2490610973 / 1000000000000 : ℝ)
  | 8 => (49357937 / 20000000000 : ℝ)
  | 9 => (2444366791 / 1000000000000 : ℝ)
  | 10 => (30250201 / 12500000000 : ℝ)
  | 11 => (1197420049 / 500000000000 : ℝ)
  | 12 => (2368834329 / 1000000000000 : ℝ)
  | 13 => (585498589 / 250000000000 : ℝ)
  | 14 => (289289483 / 125000000000 : ℝ)
  | 15 => (571448661 / 250000000000 : ℝ)
  | 16 => (2256426591 / 1000000000000 : ℝ)
  | 17 => (1113103853 / 500000000000 : ℝ)
  | 18 => (2195134099 / 1000000000000 : ℝ)
  | 19 => (216320199 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch010Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((200 : ℝ) + (j.val : ℝ)) / 1600)
      (((200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch010Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch010Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((200 : ℝ) + (j.val : ℝ)) / 1600)
    (((200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch010Neg100WeightLower j.val) (hpThetaShiftOneBatch010Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch010Neg100WeightLower, hpThetaShiftOneBatch010Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch010Neg100_integral_bounds :
    (45240491697 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (46227095817 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch010Lower hpThetaJensenCellsBatch010Upper
    hpThetaShiftOneBatch010Neg100WeightLower hpThetaShiftOneBatch010Neg100WeightUpper hpThetaJensenCellsBatch010_bounds hpThetaShiftOneBatch010Neg100_weight_bounds
  have hl : (45240491697 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch010Lower j * hpThetaShiftOneBatch010Neg100WeightLower j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftOneBatch010Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftOneBatch010Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch010Lower j * hpThetaShiftOneBatch010Neg100WeightUpper j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftOneBatch010Neg100WeightUpper j) / 1600) ≤ (46227095817 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftOneBatch010Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (200 : ℝ) / 1600 = 10 / 80 by norm_num,
    show ((200 : ℝ) + 20) / 1600 = (10 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch010Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2119199417 / 500000000000 : ℝ)
  | 1 => (424861967 / 100000000000 : ℝ)
  | 2 => (851664649 / 200000000000 : ℝ)
  | 3 => (170700133 / 40000000000 : ℝ)
  | 4 => (4276153697 / 1000000000000 : ℝ)
  | 5 => (4284268171 / 1000000000000 : ℝ)
  | 6 => (2145920291 / 500000000000 : ℝ)
  | 7 => (1074716197 / 250000000000 : ℝ)
  | 8 => (4305334673 / 1000000000000 : ℝ)
  | 9 => (4311244147 / 1000000000000 : ℝ)
  | 10 => (2158293573 / 500000000000 : ℝ)
  | 11 => (4321357633 / 1000000000000 : ℝ)
  | 12 => (5406937 / 1250000000 : ℝ)
  | 13 => (4329157067 / 1000000000000 : ℝ)
  | 14 => (1083043521 / 250000000000 : ℝ)
  | 15 => (4334594731 / 1000000000000 : ℝ)
  | 16 => (2168206559 / 500000000000 : ℝ)
  | 17 => (1084405847 / 250000000000 : ℝ)
  | 18 => (1084549077 / 250000000000 : ℝ)
  | 19 => (4337547407 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch010Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (4248619671 / 1000000000000 : ℝ)
  | 1 => (2129161623 / 500000000000 : ℝ)
  | 2 => (2133751663 / 500000000000 : ℝ)
  | 3 => (2138076849 / 500000000000 : ℝ)
  | 4 => (1071067043 / 250000000000 : ℝ)
  | 5 => (4291840583 / 1000000000000 : ℝ)
  | 6 => (4298864789 / 1000000000000 : ℝ)
  | 7 => (2152667337 / 500000000000 : ℝ)
  | 8 => (1077811037 / 250000000000 : ℝ)
  | 9 => (4316587147 / 1000000000000 : ℝ)
  | 10 => (2160678817 / 500000000000 : ℝ)
  | 11 => (4325549601 / 1000000000000 : ℝ)
  | 12 => (1082289267 / 250000000000 : ℝ)
  | 13 => (866434817 / 200000000000 : ℝ)
  | 14 => (1083648683 / 250000000000 : ℝ)
  | 15 => (4336413119 / 1000000000000 : ℝ)
  | 16 => (4337623389 / 1000000000000 : ℝ)
  | 17 => (1084554929 / 250000000000 : ℝ)
  | 18 => (2169148479 / 500000000000 : ℝ)
  | 19 => (4338196309 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch010Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((200 : ℝ) + (j.val : ℝ)) / 1600)
      (((200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch010Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch010Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((200 : ℝ) + (j.val : ℝ)) / 1600)
    (((200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch010Neg65WeightLower j.val) (hpThetaShiftOneBatch010Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch010Neg65WeightLower, hpThetaShiftOneBatch010Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch010Neg65_integral_bounds :
    (81301302267 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (41159928451 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch010Lower hpThetaJensenCellsBatch010Upper
    hpThetaShiftOneBatch010Neg65WeightLower hpThetaShiftOneBatch010Neg65WeightUpper hpThetaJensenCellsBatch010_bounds hpThetaShiftOneBatch010Neg65_weight_bounds
  have hl : (81301302267 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch010Lower j * hpThetaShiftOneBatch010Neg65WeightLower j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftOneBatch010Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftOneBatch010Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch010Lower j * hpThetaShiftOneBatch010Neg65WeightUpper j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftOneBatch010Neg65WeightUpper j) / 1600) ≤ (41159928451 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftOneBatch010Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (200 : ℝ) / 1600 = 10 / 80 by norm_num,
    show ((200 : ℝ) + 20) / 1600 = (10 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch010Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (5521410987 / 1000000000000 : ℝ)
  | 1 => (111101571 / 20000000000 : ℝ)
  | 2 => (1397127611 / 250000000000 : ℝ)
  | 3 => (5621701533 / 1000000000000 : ℝ)
  | 4 => (226185867 / 40000000000 : ℝ)
  | 5 => (1421835181 / 250000000000 : ℝ)
  | 6 => (1429944633 / 250000000000 : ℝ)
  | 7 => (5751954947 / 1000000000000 : ℝ)
  | 8 => (2891932407 / 500000000000 : ℝ)
  | 9 => (232620119 / 40000000000 : ℝ)
  | 10 => (365429017 / 62500000000 : ℝ)
  | 11 => (2938971771 / 500000000000 : ℝ)
  | 12 => (2954367811 / 500000000000 : ℝ)
  | 13 => (5939235347 / 1000000000000 : ℝ)
  | 14 => (373089847 / 62500000000 : ℝ)
  | 15 => (599933707 / 100000000000 : ℝ)
  | 16 => (1205785747 / 200000000000 : ℝ)
  | 17 => (3029103689 / 500000000000 : ℝ)
  | 18 => (3043583917 / 500000000000 : ℝ)
  | 19 => (764475617 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch010Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5555078551 / 1000000000000 : ℝ)
  | 1 => (1117702089 / 200000000000 : ℝ)
  | 2 => (2810850767 / 500000000000 : ℝ)
  | 3 => (1413661669 / 250000000000 : ℝ)
  | 4 => (227493629 / 40000000000 : ℝ)
  | 5 => (5719778533 / 1000000000000 : ℝ)
  | 6 => (1437988737 / 250000000000 : ℝ)
  | 7 => (1156772963 / 200000000000 : ℝ)
  | 8 => (45433617 / 7812500000 : ℝ)
  | 9 => (5846864273 / 1000000000000 : ℝ)
  | 10 => (5877943543 / 1000000000000 : ℝ)
  | 11 => (5908735623 / 1000000000000 : ℝ)
  | 12 => (1484808837 / 250000000000 : ℝ)
  | 13 => (5969437553 / 1000000000000 : ℝ)
  | 14 => (5999337071 / 1000000000000 : ℝ)
  | 15 => (188404023 / 31250000000 : ℝ)
  | 16 => (6058207379 / 1000000000000 : ℝ)
  | 17 => (1217433567 / 200000000000 : ℝ)
  | 18 => (6115804937 / 1000000000000 : ℝ)
  | 19 => (6144113519 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch010Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((200 : ℝ) + (j.val : ℝ)) / 1600)
      (((200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch010Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch010Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((200 : ℝ) + (j.val : ℝ)) / 1600)
    (((200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch010Neg40WeightLower j.val) (hpThetaShiftOneBatch010Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch010Neg40WeightLower, hpThetaShiftOneBatch010Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch010Neg40_integral_bounds :
    (1100259393 / 10000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (27967187201 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch010Lower hpThetaJensenCellsBatch010Upper
    hpThetaShiftOneBatch010Neg40WeightLower hpThetaShiftOneBatch010Neg40WeightUpper hpThetaJensenCellsBatch010_bounds hpThetaShiftOneBatch010Neg40_weight_bounds
  have hl : (1100259393 / 10000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch010Lower j * hpThetaShiftOneBatch010Neg40WeightLower j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftOneBatch010Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftOneBatch010Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch010Lower j * hpThetaShiftOneBatch010Neg40WeightUpper j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftOneBatch010Neg40WeightUpper j) / 1600) ≤ (27967187201 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftOneBatch010Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (200 : ℝ) / 1600 = 10 / 80 by norm_num,
    show ((200 : ℝ) + 20) / 1600 = (10 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch010Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (414353751 / 62500000000 : ℝ)
  | 1 => (1336905961 / 200000000000 : ℝ)
  | 2 => (3369724557 / 500000000000 : ℝ)
  | 3 => (271776593 / 40000000000 : ℝ)
  | 4 => (1712355953 / 250000000000 : ℝ)
  | 5 => (6904472939 / 1000000000000 : ℝ)
  | 6 => (6959559059 / 1000000000000 : ℝ)
  | 7 => (876834877 / 125000000000 : ℝ)
  | 8 => (3534914823 / 500000000000 : ℝ)
  | 9 => (3562503887 / 500000000000 : ℝ)
  | 10 => (1436042043 / 200000000000 : ℝ)
  | 11 => (452214611 / 62500000000 : ℝ)
  | 12 => (3645337627 / 500000000000 : ℝ)
  | 13 => (7345931439 / 1000000000000 : ℝ)
  | 14 => (1850299777 / 250000000000 : ℝ)
  | 15 => (932059379 / 125000000000 : ℝ)
  | 16 => (7511755973 / 1000000000000 : ℝ)
  | 17 => (1891759671 / 250000000000 : ℝ)
  | 18 => (7622319907 / 1000000000000 : ℝ)
  | 19 => (3838798189 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch010Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3342264903 / 500000000000 : ℝ)
  | 1 => (1347889823 / 200000000000 : ℝ)
  | 2 => (3397207413 / 500000000000 : ℝ)
  | 3 => (6849423813 / 1000000000000 : ℝ)
  | 4 => (345223647 / 50000000000 : ℝ)
  | 5 => (347977953 / 50000000000 : ℝ)
  | 6 => (7014679017 / 1000000000000 : ℝ)
  | 7 => (7069829647 / 1000000000000 : ℝ)
  | 8 => (285000311 / 40000000000 : ℝ)
  | 9 => (897526277 / 125000000000 : ℝ)
  | 10 => (7235433777 / 1000000000000 : ℝ)
  | 11 => (1458135051 / 200000000000 : ℝ)
  | 12 => (91824143 / 12500000000 : ℝ)
  | 13 => (7401199109 / 1000000000000 : ℝ)
  | 14 => (7456475033 / 1000000000000 : ℝ)
  | 15 => (3755877987 / 500000000000 : ℝ)
  | 16 => (1513407737 / 200000000000 : ℝ)
  | 17 => (1905579977 / 250000000000 : ℝ)
  | 18 => (7677596379 / 1000000000000 : ℝ)
  | 19 => (3866432413 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch010Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((200 : ℝ) + (j.val : ℝ)) / 1600)
      (((200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch010Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch010Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((200 : ℝ) + (j.val : ℝ)) / 1600)
    (((200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch010Neg20WeightLower j.val) (hpThetaShiftOneBatch010Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch010Neg20WeightLower, hpThetaShiftOneBatch010Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch010Neg20_integral_bounds :
    (135056669161 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (137642043331 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch010Lower hpThetaJensenCellsBatch010Upper
    hpThetaShiftOneBatch010Neg20WeightLower hpThetaShiftOneBatch010Neg20WeightUpper hpThetaJensenCellsBatch010_bounds hpThetaShiftOneBatch010Neg20_weight_bounds
  have hl : (135056669161 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch010Lower j * hpThetaShiftOneBatch010Neg20WeightLower j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftOneBatch010Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftOneBatch010Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch010Lower j * hpThetaShiftOneBatch010Neg20WeightUpper j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftOneBatch010Neg20WeightUpper j) / 1600) ≤ (137642043331 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftOneBatch010Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (200 : ℝ) / 1600 = 10 / 80 by norm_num,
    show ((200 : ℝ) + 20) / 1600 = (10 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch010Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch010Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch010Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch010Neg20_integral_bounds
end HodgeProofHP
