/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch035

/-! Exact signed weight and batch integral certificates, batch 35 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch035Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (994525553 / 1000000000000 : ℝ)
  | 1 => (507175551 / 500000000000 : ℝ)
  | 2 => (103435659 / 100000000000 : ℝ)
  | 3 => (210908337 / 200000000000 : ℝ)
  | 4 => (53745301 / 50000000000 : ℝ)
  | 5 => (1095449189 / 1000000000000 : ℝ)
  | 6 => (1116170747 / 1000000000000 : ℝ)
  | 7 => (1137070207 / 1000000000000 : ℝ)
  | 8 => (289536761 / 250000000000 : ℝ)
  | 9 => (117940069 / 100000000000 : ℝ)
  | 10 => (240166107 / 200000000000 : ℝ)
  | 11 => (1222435929 / 1000000000000 : ℝ)
  | 12 => (49768647 / 40000000000 : ℝ)
  | 13 => (1266170533 / 1000000000000 : ℝ)
  | 14 => (64414911 / 50000000000 : ℝ)
  | 15 => (327649601 / 250000000000 : ℝ)
  | 16 => (133307021 / 100000000000 : ℝ)
  | 17 => (1355712713 / 1000000000000 : ℝ)
  | 18 => (1378524943 / 1000000000000 : ℝ)
  | 19 => (35037647 / 25000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch035Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1014351103 / 1000000000000 : ℝ)
  | 1 => (1034356591 / 1000000000000 : ℝ)
  | 2 => (527270843 / 500000000000 : ℝ)
  | 3 => (1074906021 / 1000000000000 : ℝ)
  | 4 => (109544919 / 100000000000 : ℝ)
  | 5 => (279042687 / 250000000000 : ℝ)
  | 6 => (8883361 / 7812500000 : ℝ)
  | 7 => (231629409 / 200000000000 : ℝ)
  | 8 => (1179400691 / 1000000000000 : ℝ)
  | 9 => (150103817 / 125000000000 : ℝ)
  | 10 => (122243593 / 100000000000 : ℝ)
  | 11 => (77763511 / 62500000000 : ℝ)
  | 12 => (633085267 / 500000000000 : ℝ)
  | 13 => (1288298221 / 1000000000000 : ℝ)
  | 14 => (262119681 / 200000000000 : ℝ)
  | 15 => (1333070211 / 1000000000000 : ℝ)
  | 16 => (677856357 / 500000000000 : ℝ)
  | 17 => (86157809 / 62500000000 : ℝ)
  | 18 => (1401505881 / 1000000000000 : ℝ)
  | 19 => (712327227 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch035Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((700 : ℝ) + (j.val : ℝ)) / 1600)
      (((700 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch035Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch035Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((700 : ℝ) + (j.val : ℝ)) / 1600)
    (((700 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch035Neg100WeightLower j.val) (hpThetaShiftTwoBatch035Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch035Neg100WeightLower, hpThetaShiftTwoBatch035Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch035Neg100_integral_bounds :
    (1673982317 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (3460978129 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (700 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch035Lower hpThetaJensenCellsBatch035Upper
    hpThetaShiftTwoBatch035Neg100WeightLower hpThetaShiftTwoBatch035Neg100WeightUpper hpThetaJensenCellsBatch035_bounds hpThetaShiftTwoBatch035Neg100_weight_bounds
  have hl : (1673982317 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch035Lower j * hpThetaShiftTwoBatch035Neg100WeightLower j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftTwoBatch035Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftTwoBatch035Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch035Lower j * hpThetaShiftTwoBatch035Neg100WeightUpper j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftTwoBatch035Neg100WeightUpper j) / 1600) ≤ (3460978129 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftTwoBatch035Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (700 : ℝ) / 1600 = 35 / 80 by norm_num,
    show ((700 : ℝ) + 20) / 1600 = (35 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch035Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-548705727 / 1000000000000 : ℝ)
  | 1 => (-109295553 / 200000000000 : ℝ)
  | 2 => (-544142657 / 1000000000000 : ℝ)
  | 3 => (-270849573 / 500000000000 : ℝ)
  | 4 => (-539145971 / 1000000000000 : ℝ)
  | 5 => (-67060233 / 125000000000 : ℝ)
  | 6 => (-106741111 / 200000000000 : ℝ)
  | 7 => (-106163153 / 200000000000 : ℝ)
  | 8 => (-105562243 / 200000000000 : ℝ)
  | 9 => (-524690619 / 1000000000000 : ℝ)
  | 10 => (-260726343 / 500000000000 : ℝ)
  | 11 => (-259048061 / 500000000000 : ℝ)
  | 12 => (-128654907 / 250000000000 : ℝ)
  | 13 => (-511021899 / 1000000000000 : ℝ)
  | 14 => (-507301629 / 1000000000000 : ℝ)
  | 15 => (-251728753 / 500000000000 : ℝ)
  | 16 => (-499488213 / 1000000000000 : ℝ)
  | 17 => (-30962027 / 62500000000 : ℝ)
  | 18 => (-491168837 / 1000000000000 : ℝ)
  | 19 => (-486816101 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch035Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-136619441 / 250000000000 : ℝ)
  | 1 => (-8502229 / 15625000000 : ℝ)
  | 2 => (-108339829 / 200000000000 : ℝ)
  | 3 => (-53914597 / 100000000000 : ℝ)
  | 4 => (-536481863 / 1000000000000 : ℝ)
  | 5 => (-266852777 / 500000000000 : ℝ)
  | 6 => (-132703941 / 250000000000 : ℝ)
  | 7 => (-263905607 / 500000000000 : ℝ)
  | 8 => (-262345309 / 500000000000 : ℝ)
  | 9 => (-104290537 / 200000000000 : ℝ)
  | 10 => (-518096121 / 1000000000000 : ℝ)
  | 11 => (-514619627 / 1000000000000 : ℝ)
  | 12 => (-255510949 / 500000000000 : ℝ)
  | 13 => (-126825407 / 250000000000 : ℝ)
  | 14 => (-100691501 / 200000000000 : ℝ)
  | 15 => (-124872053 / 250000000000 : ℝ)
  | 16 => (-495392431 / 1000000000000 : ℝ)
  | 17 => (-122792209 / 250000000000 : ℝ)
  | 18 => (-4868161 / 10000000000 : ℝ)
  | 19 => (-482332893 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch035Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((700 : ℝ) + (j.val : ℝ)) / 1600)
      (((700 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch035Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch035Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((700 : ℝ) + (j.val : ℝ)) / 1600)
    (((700 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch035Neg65WeightLower j.val) (hpThetaShiftTwoBatch035Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch035Neg65WeightLower, hpThetaShiftTwoBatch035Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch035Neg65_integral_bounds :
    (-93291377 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-730370669 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (700 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch035Lower hpThetaJensenCellsBatch035Upper
    hpThetaShiftTwoBatch035Neg65WeightLower hpThetaShiftTwoBatch035Neg65WeightUpper hpThetaJensenCellsBatch035_bounds hpThetaShiftTwoBatch035Neg65_weight_bounds
  have hl : (-93291377 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch035Lower j * hpThetaShiftTwoBatch035Neg65WeightLower j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftTwoBatch035Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftTwoBatch035Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch035Lower j * hpThetaShiftTwoBatch035Neg65WeightUpper j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftTwoBatch035Neg65WeightUpper j) / 1600) ≤ (-730370669 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftTwoBatch035Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (700 : ℝ) / 1600 = 35 / 80 by norm_num,
    show ((700 : ℝ) + 20) / 1600 = (35 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch035Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-762310901 / 1000000000000 : ℝ)
  | 1 => (-768067941 / 1000000000000 : ℝ)
  | 2 => (-386909767 / 500000000000 : ℝ)
  | 3 => (-19489127 / 25000000000 : ℝ)
  | 4 => (-392651987 / 500000000000 : ℝ)
  | 5 => (-791035607 / 1000000000000 : ℝ)
  | 6 => (-796759359 / 1000000000000 : ℝ)
  | 7 => (-802474609 / 1000000000000 : ℝ)
  | 8 => (-202045181 / 250000000000 : ℝ)
  | 9 => (-81387707 / 100000000000 : ℝ)
  | 10 => (-819563003 / 1000000000000 : ℝ)
  | 11 => (-412618937 / 500000000000 : ℝ)
  | 12 => (-207725257 / 250000000000 : ℝ)
  | 13 => (-418275901 / 500000000000 : ℝ)
  | 14 => (-842189529 / 1000000000000 : ℝ)
  | 15 => (-847813533 / 1000000000000 : ℝ)
  | 16 => (-853423133 / 1000000000000 : ℝ)
  | 17 => (-429508821 / 500000000000 : ℝ)
  | 18 => (-216149091 / 250000000000 : ℝ)
  | 19 => (-870158599 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch035Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-151309801 / 200000000000 : ℝ)
  | 1 => (-7623109 / 10000000000 : ℝ)
  | 2 => (-38403397 / 50000000000 : ℝ)
  | 3 => (-773819533 / 1000000000000 : ℝ)
  | 4 => (-779565079 / 1000000000000 : ℝ)
  | 5 => (-785303973 / 1000000000000 : ℝ)
  | 6 => (-395517803 / 500000000000 : ℝ)
  | 7 => (-398379679 / 500000000000 : ℝ)
  | 8 => (-50154663 / 62500000000 : ℝ)
  | 9 => (-808180723 / 1000000000000 : ℝ)
  | 10 => (-813877069 / 1000000000000 : ℝ)
  | 11 => (-409781501 / 500000000000 : ℝ)
  | 12 => (-825237873 / 1000000000000 : ℝ)
  | 13 => (-830901027 / 1000000000000 : ℝ)
  | 14 => (-836551801 / 1000000000000 : ℝ)
  | 15 => (-105273691 / 125000000000 : ℝ)
  | 16 => (-211953383 / 250000000000 : ℝ)
  | 17 => (-213355783 / 250000000000 : ℝ)
  | 18 => (-859017641 / 1000000000000 : ℝ)
  | 19 => (-864596363 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch035Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((700 : ℝ) + (j.val : ℝ)) / 1600)
      (((700 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch035Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch035Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((700 : ℝ) + (j.val : ℝ)) / 1600)
    (((700 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch035Neg45WeightLower j.val) (hpThetaShiftTwoBatch035Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch035Neg45WeightLower, hpThetaShiftTwoBatch035Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch035Neg45_integral_bounds :
    (-2332262997 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-285107893 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (700 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch035Lower hpThetaJensenCellsBatch035Upper
    hpThetaShiftTwoBatch035Neg45WeightLower hpThetaShiftTwoBatch035Neg45WeightUpper hpThetaJensenCellsBatch035_bounds hpThetaShiftTwoBatch035Neg45_weight_bounds
  have hl : (-2332262997 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch035Lower j * hpThetaShiftTwoBatch035Neg45WeightLower j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftTwoBatch035Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftTwoBatch035Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch035Lower j * hpThetaShiftTwoBatch035Neg45WeightUpper j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftTwoBatch035Neg45WeightUpper j) / 1600) ≤ (-285107893 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftTwoBatch035Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (700 : ℝ) / 1600 = 35 / 80 by norm_num,
    show ((700 : ℝ) + 20) / 1600 = (35 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch035Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (30613127 / 1000000000000 : ℝ)
  | 1 => (25645991 / 1000000000000 : ℝ)
  | 2 => (5157963 / 250000000000 : ℝ)
  | 3 => (7785291 / 500000000000 : ℝ)
  | 4 => (2092411 / 200000000000 : ℝ)
  | 5 => (1326537 / 250000000000 : ℝ)
  | 6 => (102737 / 1000000000000 : ℝ)
  | 7 => (-2574149 / 500000000000 : ℝ)
  | 8 => (-5223539 / 500000000000 : ℝ)
  | 9 => (-15793721 / 1000000000000 : ℝ)
  | 10 => (-21188343 / 1000000000000 : ℝ)
  | 11 => (-26631059 / 1000000000000 : ℝ)
  | 12 => (-16060991 / 500000000000 : ℝ)
  | 13 => (-1506449 / 40000000000 : ℝ)
  | 14 => (-168941 / 3906250000 : ℝ)
  | 15 => (-24442553 / 500000000000 : ℝ)
  | 16 => (-54569959 / 1000000000000 : ℝ)
  | 17 => (-60303561 / 1000000000000 : ℝ)
  | 18 => (-516297 / 7812500000 : ℝ)
  | 19 => (-4494839 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch035Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3553339 / 100000000000 : ℝ)
  | 1 => (3826641 / 125000000000 : ℝ)
  | 2 => (3205749 / 125000000000 : ℝ)
  | 3 => (20631853 / 1000000000000 : ℝ)
  | 4 => (15570583 / 1000000000000 : ℝ)
  | 5 => (1307757 / 125000000000 : ℝ)
  | 6 => (5306149 / 1000000000000 : ℝ)
  | 7 => (51369 / 500000000000 : ℝ)
  | 8 => (-5148297 / 1000000000000 : ℝ)
  | 9 => (-10447077 / 1000000000000 : ℝ)
  | 10 => (-394843 / 25000000000 : ℝ)
  | 11 => (-10594171 / 500000000000 : ℝ)
  | 12 => (-13315529 / 500000000000 : ℝ)
  | 13 => (-32121981 / 1000000000000 : ℝ)
  | 14 => (-4707653 / 125000000000 : ℝ)
  | 15 => (-8649779 / 200000000000 : ℝ)
  | 16 => (-9777021 / 200000000000 : ℝ)
  | 17 => (-27284979 / 500000000000 : ℝ)
  | 18 => (-1507589 / 25000000000 : ℝ)
  | 19 => (-13217203 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch035Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((700 : ℝ) + (j.val : ℝ)) / 1600)
      (((700 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch035Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch035Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((700 : ℝ) + (j.val : ℝ)) / 1600)
    (((700 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch035Neg25WeightLower j.val) (hpThetaShiftTwoBatch035Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch035Neg25WeightLower, hpThetaShiftTwoBatch035Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch035Neg25_integral_bounds :
    (-5211637 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (35 / 80 : ℝ) ((35 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-17823181 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (700 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch035Lower hpThetaJensenCellsBatch035Upper
    hpThetaShiftTwoBatch035Neg25WeightLower hpThetaShiftTwoBatch035Neg25WeightUpper hpThetaJensenCellsBatch035_bounds hpThetaShiftTwoBatch035Neg25_weight_bounds
  have hl : (-5211637 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch035Lower j * hpThetaShiftTwoBatch035Neg25WeightLower j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftTwoBatch035Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftTwoBatch035Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch035Lower j * hpThetaShiftTwoBatch035Neg25WeightUpper j)
        (hpThetaJensenCellsBatch035Upper j * hpThetaShiftTwoBatch035Neg25WeightUpper j) / 1600) ≤ (-17823181 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch035Lower, hpThetaJensenCellsBatch035Upper,
      hpThetaShiftTwoBatch035Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (700 : ℝ) / 1600 = 35 / 80 by norm_num,
    show ((700 : ℝ) + 20) / 1600 = (35 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch035Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch035Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch035Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch035Neg25_integral_bounds
end HodgeProofHP
