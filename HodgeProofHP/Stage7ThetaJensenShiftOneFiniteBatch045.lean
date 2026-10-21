/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch045

/-! Exact signed weight and batch integral certificates, batch 45 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch045Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-25153031921 / 62500000000 : ℝ)
  | 1 => (-413691844557 / 1000000000000 : ℝ)
  | 2 => (-21254704983 / 50000000000 : ℝ)
  | 3 => (-218328416159 / 500000000000 : ℝ)
  | 4 => (-448381610003 / 1000000000000 : ℝ)
  | 5 => (-460270011443 / 1000000000000 : ℝ)
  | 6 => (-472323626683 / 1000000000000 : ℝ)
  | 7 => (-242272028571 / 500000000000 : ℝ)
  | 8 => (-496932915677 / 1000000000000 : ℝ)
  | 9 => (-509491826639 / 1000000000000 : ℝ)
  | 10 => (-261111212967 / 500000000000 : ℝ)
  | 11 => (-133781590271 / 250000000000 : ℝ)
  | 12 => (-68525661411 / 125000000000 : ℝ)
  | 13 => (-14036522187 / 25000000000 : ℝ)
  | 14 => (-114978966479 / 200000000000 : ℝ)
  | 15 => (-36781801289 / 62500000000 : ℝ)
  | 16 => (-15057613967 / 25000000000 : ℝ)
  | 17 => (-308141882529 / 500000000000 : ℝ)
  | 18 => (-630448170297 / 1000000000000 : ℝ)
  | 19 => (-322399758521 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch045Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-391362553063 / 1000000000000 : ℝ)
  | 1 => (-80489702147 / 200000000000 : ℝ)
  | 2 => (-103422961139 / 250000000000 : ℝ)
  | 3 => (-425094099659 / 1000000000000 : ℝ)
  | 4 => (-436656832317 / 1000000000000 : ℝ)
  | 5 => (-224190805001 / 500000000000 : ℝ)
  | 6 => (-230135005721 / 500000000000 : ℝ)
  | 7 => (-236161813341 / 500000000000 : ℝ)
  | 8 => (-484544057141 / 1000000000000 : ℝ)
  | 9 => (-124233228919 / 250000000000 : ℝ)
  | 10 => (-254745913319 / 500000000000 : ℝ)
  | 11 => (-522222425933 / 1000000000000 : ℝ)
  | 12 => (-535126361083 / 1000000000000 : ℝ)
  | 13 => (-548205291287 / 1000000000000 : ℝ)
  | 14 => (-561460887479 / 1000000000000 : ℝ)
  | 15 => (-287447416197 / 500000000000 : ℝ)
  | 16 => (-588508820623 / 1000000000000 : ℝ)
  | 17 => (-602304558679 / 1000000000000 : ℝ)
  | 18 => (-616283765057 / 1000000000000 : ℝ)
  | 19 => (-78806021287 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch045Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((900 : ℝ) + (j.val : ℝ)) / 1600)
      (((900 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch045Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch045Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((900 : ℝ) + (j.val : ℝ)) / 1600)
    (((900 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch045Neg100WeightLower j.val) (hpThetaShiftOneBatch045Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch045Neg100WeightLower, hpThetaShiftOneBatch045Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch045Neg100_integral_bounds :
    (-15624359073 / 50000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-29941086083 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (900 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch045Lower hpThetaJensenCellsBatch045Upper
    hpThetaShiftOneBatch045Neg100WeightLower hpThetaShiftOneBatch045Neg100WeightUpper hpThetaJensenCellsBatch045_bounds hpThetaShiftOneBatch045Neg100_weight_bounds
  have hl : (-15624359073 / 50000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch045Lower j * hpThetaShiftOneBatch045Neg100WeightLower j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftOneBatch045Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftOneBatch045Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch045Lower j * hpThetaShiftOneBatch045Neg100WeightUpper j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftOneBatch045Neg100WeightUpper j) / 1600) ≤ (-29941086083 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftOneBatch045Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (900 : ℝ) / 1600 = 45 / 80 by norm_num,
    show ((900 : ℝ) + 20) / 1600 = (45 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch045Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (119408326241 / 500000000000 : ℝ)
  | 1 => (239673439369 / 1000000000000 : ℝ)
  | 2 => (48103381113 / 200000000000 : ℝ)
  | 3 => (48269357897 / 200000000000 : ℝ)
  | 4 => (121081413547 / 500000000000 : ℝ)
  | 5 => (121482375949 / 500000000000 : ℝ)
  | 6 => (243752294921 / 1000000000000 : ℝ)
  | 7 => (244525184699 / 1000000000000 : ℝ)
  | 8 => (245283147257 / 1000000000000 : ℝ)
  | 9 => (246025906099 / 1000000000000 : ℝ)
  | 10 => (123376591097 / 500000000000 : ℝ)
  | 11 => (49492938791 / 200000000000 : ℝ)
  | 12 => (24816015723 / 100000000000 : ℝ)
  | 13 => (248839285283 / 1000000000000 : ℝ)
  | 14 => (124750894391 / 500000000000 : ℝ)
  | 15 => (250147375781 / 1000000000000 : ℝ)
  | 16 => (31346968963 / 125000000000 : ℝ)
  | 17 => (251386619333 / 1000000000000 : ℝ)
  | 18 => (25197967879 / 100000000000 : ℝ)
  | 19 => (126277313761 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch045Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (23967343937 / 100000000000 : ℝ)
  | 1 => (120258452783 / 500000000000 : ℝ)
  | 2 => (120673394743 / 500000000000 : ℝ)
  | 3 => (48432565419 / 200000000000 : ℝ)
  | 4 => (242964751899 / 1000000000000 : ℝ)
  | 5 => (121876147461 / 500000000000 : ℝ)
  | 6 => (2445251847 / 10000000000 : ℝ)
  | 7 => (122641573629 / 500000000000 : ℝ)
  | 8 => (2460259061 / 10000000000 : ℝ)
  | 9 => (49350636439 / 200000000000 : ℝ)
  | 10 => (61866173489 / 250000000000 : ℝ)
  | 11 => (248160157231 / 1000000000000 : ℝ)
  | 12 => (62209821321 / 250000000000 : ℝ)
  | 13 => (249501788783 / 1000000000000 : ℝ)
  | 14 => (125073687891 / 500000000000 : ℝ)
  | 15 => (50155150341 / 200000000000 : ℝ)
  | 16 => (125693309667 / 500000000000 : ℝ)
  | 17 => (251979678791 / 1000000000000 : ℝ)
  | 18 => (252554627523 / 1000000000000 : ℝ)
  | 19 => (253111160287 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch045Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((900 : ℝ) + (j.val : ℝ)) / 1600)
      (((900 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch045Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch045Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((900 : ℝ) + (j.val : ℝ)) / 1600)
    (((900 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch045Neg65WeightLower j.val) (hpThetaShiftOneBatch045Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch045Neg65WeightLower, hpThetaShiftOneBatch045Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch045Neg65_integral_bounds :
    (146615431843 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (18712859723 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (900 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch045Lower hpThetaJensenCellsBatch045Upper
    hpThetaShiftOneBatch045Neg65WeightLower hpThetaShiftOneBatch045Neg65WeightUpper hpThetaJensenCellsBatch045_bounds hpThetaShiftOneBatch045Neg65_weight_bounds
  have hl : (146615431843 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch045Lower j * hpThetaShiftOneBatch045Neg65WeightLower j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftOneBatch045Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftOneBatch045Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch045Lower j * hpThetaShiftOneBatch045Neg65WeightUpper j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftOneBatch045Neg65WeightUpper j) / 1600) ≤ (18712859723 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftOneBatch045Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (900 : ℝ) / 1600 = 45 / 80 by norm_num,
    show ((900 : ℝ) + 20) / 1600 = (45 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch045Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (42314883853 / 1000000000000 : ℝ)
  | 1 => (1081829019 / 25000000000 : ℝ)
  | 2 => (1105938179 / 25000000000 : ℝ)
  | 3 => (22603991101 / 500000000000 : ℝ)
  | 4 => (4618452471 / 100000000000 : ℝ)
  | 5 => (47167153177 / 1000000000000 : ℝ)
  | 6 => (4815586577 / 100000000000 : ℝ)
  | 7 => (307191627 / 6250000000 : ℝ)
  | 8 => (12537883581 / 250000000000 : ℝ)
  | 9 => (25579242469 / 500000000000 : ℝ)
  | 10 => (26085754489 / 500000000000 : ℝ)
  | 11 => (53190602913 / 1000000000000 : ℝ)
  | 12 => (27107881433 / 500000000000 : ℝ)
  | 13 => (55246984609 / 1000000000000 : ℝ)
  | 14 => (56284263561 / 1000000000000 : ℝ)
  | 15 => (57327594783 / 1000000000000 : ℝ)
  | 16 => (3648560811 / 62500000000 : ℝ)
  | 17 => (29716196241 / 500000000000 : ℝ)
  | 18 => (30246923637 / 500000000000 : ℝ)
  | 19 => (30780665479 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch045Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (43273160761 / 1000000000000 : ℝ)
  | 1 => (44237527161 / 1000000000000 : ℝ)
  | 2 => (45207982203 / 1000000000000 : ℝ)
  | 3 => (46184524711 / 1000000000000 : ℝ)
  | 4 => (23583576589 / 500000000000 : ℝ)
  | 5 => (48155865771 / 1000000000000 : ℝ)
  | 6 => (49150660321 / 1000000000000 : ℝ)
  | 7 => (2006061373 / 40000000000 : ℝ)
  | 8 => (51158484939 / 1000000000000 : ℝ)
  | 9 => (52171508979 / 1000000000000 : ℝ)
  | 10 => (26595301457 / 500000000000 : ℝ)
  | 11 => (54215762867 / 1000000000000 : ℝ)
  | 12 => (5524698461 / 100000000000 : ℝ)
  | 13 => (28142131781 / 500000000000 : ℝ)
  | 14 => (1791487337 / 31250000000 : ℝ)
  | 15 => (58376972977 / 1000000000000 : ℝ)
  | 16 => (59432392483 / 1000000000000 : ℝ)
  | 17 => (2419753891 / 40000000000 : ℝ)
  | 18 => (61561330959 / 1000000000000 : ℝ)
  | 19 => (62634836769 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch045Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((900 : ℝ) + (j.val : ℝ)) / 1600)
      (((900 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch045Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch045Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((900 : ℝ) + (j.val : ℝ)) / 1600)
    (((900 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch045Neg40WeightLower j.val) (hpThetaShiftOneBatch045Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch045Neg40WeightLower, hpThetaShiftOneBatch045Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch045Neg40_integral_bounds :
    (30678369351 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (31848847941 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (900 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch045Lower hpThetaJensenCellsBatch045Upper
    hpThetaShiftOneBatch045Neg40WeightLower hpThetaShiftOneBatch045Neg40WeightUpper hpThetaJensenCellsBatch045_bounds hpThetaShiftOneBatch045Neg40_weight_bounds
  have hl : (30678369351 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch045Lower j * hpThetaShiftOneBatch045Neg40WeightLower j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftOneBatch045Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftOneBatch045Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch045Lower j * hpThetaShiftOneBatch045Neg40WeightUpper j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftOneBatch045Neg40WeightUpper j) / 1600) ≤ (31848847941 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftOneBatch045Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (900 : ℝ) / 1600 = 45 / 80 by norm_num,
    show ((900 : ℝ) + 20) / 1600 = (45 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch045Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-36754759767 / 500000000000 : ℝ)
  | 1 => (-18423260437 / 250000000000 : ℝ)
  | 2 => (-73875129347 / 1000000000000 : ℝ)
  | 3 => (-74055768583 / 1000000000000 : ℝ)
  | 4 => (-2969397827 / 40000000000 : ℝ)
  | 5 => (-7441264681 / 100000000000 : ℝ)
  | 6 => (-74588858141 / 1000000000000 : ℝ)
  | 7 => (-2336361431 / 31250000000 : ℝ)
  | 8 => (-74936755851 / 1000000000000 : ℝ)
  | 9 => (-9388551797 / 125000000000 : ℝ)
  | 10 => (-37639263697 / 500000000000 : ℝ)
  | 11 => (-75447080897 / 1000000000000 : ℝ)
  | 12 => (-1512281217 / 20000000000 : ℝ)
  | 13 => (-75779453183 / 1000000000000 : ℝ)
  | 14 => (-75943243797 / 1000000000000 : ℝ)
  | 15 => (-76105418561 / 1000000000000 : ℝ)
  | 16 => (-38132981657 / 500000000000 : ℝ)
  | 17 => (-9553107983 / 125000000000 : ℝ)
  | 18 => (-19145526497 / 250000000000 : ℝ)
  | 19 => (-38368837717 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch045Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-73324576419 / 1000000000000 : ℝ)
  | 1 => (-73509519533 / 1000000000000 : ℝ)
  | 2 => (-73693041747 / 1000000000000 : ℝ)
  | 3 => (-36937564673 / 500000000000 : ℝ)
  | 4 => (-37027884291 / 500000000000 : ℝ)
  | 5 => (-37117472837 / 500000000000 : ℝ)
  | 6 => (-74412646809 / 1000000000000 : ℝ)
  | 7 => (-3729442907 / 50000000000 : ℝ)
  | 8 => (-74763565791 / 1000000000000 : ℝ)
  | 9 => (-1498735117 / 20000000000 : ℝ)
  | 10 => (-120173463 / 1600000000 : ℝ)
  | 11 => (-75278527393 / 1000000000000 : ℝ)
  | 12 => (-1178860639 / 15625000000 : ℝ)
  | 13 => (-75614060849 / 1000000000000 : ℝ)
  | 14 => (-37889726591 / 500000000000 : ℝ)
  | 15 => (-18985810949 / 250000000000 : ℝ)
  | 16 => (-237829433 / 3125000000 : ℝ)
  | 17 => (-76265963313 / 1000000000000 : ℝ)
  | 18 => (-76424863863 / 1000000000000 : ℝ)
  | 19 => (-76582105987 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch045Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((900 : ℝ) + (j.val : ℝ)) / 1600)
      (((900 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch045Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch045Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((900 : ℝ) + (j.val : ℝ)) / 1600)
    (((900 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch045Neg20WeightLower j.val) (hpThetaShiftOneBatch045Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch045Neg20WeightLower, hpThetaShiftOneBatch045Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch045Neg20_integral_bounds :
    (-2849686191 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-8936656893 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (900 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch045Lower hpThetaJensenCellsBatch045Upper
    hpThetaShiftOneBatch045Neg20WeightLower hpThetaShiftOneBatch045Neg20WeightUpper hpThetaJensenCellsBatch045_bounds hpThetaShiftOneBatch045Neg20_weight_bounds
  have hl : (-2849686191 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch045Lower j * hpThetaShiftOneBatch045Neg20WeightLower j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftOneBatch045Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftOneBatch045Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch045Lower j * hpThetaShiftOneBatch045Neg20WeightUpper j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftOneBatch045Neg20WeightUpper j) / 1600) ≤ (-8936656893 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftOneBatch045Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (900 : ℝ) / 1600 = 45 / 80 by norm_num,
    show ((900 : ℝ) + 20) / 1600 = (45 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch045Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch045Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch045Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch045Neg20_integral_bounds
end HodgeProofHP
