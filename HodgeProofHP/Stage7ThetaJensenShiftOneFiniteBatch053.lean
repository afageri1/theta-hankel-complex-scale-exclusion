/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch053

/-! Exact signed weight and batch integral certificates, batch 53 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch053Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5613137317039 / 1000000000000 : ℝ)
  | 1 => (-5678846417727 / 1000000000000 : ℝ)
  | 2 => (-2872575776783 / 500000000000 : ℝ)
  | 3 => (-5812056982469 / 1000000000000 : ℝ)
  | 4 => (-5879566986107 / 1000000000000 : ℝ)
  | 5 => (-5947685870011 / 1000000000000 : ℝ)
  | 6 => (-6016417963669 / 1000000000000 : ℝ)
  | 7 => (-760720952579 / 125000000000 : ℝ)
  | 8 => (-769467402327 / 125000000000 : ℝ)
  | 9 => (-3113168579799 / 500000000000 : ℝ)
  | 10 => (-1574391467481 / 250000000000 : ℝ)
  | 11 => (-796178725051 / 125000000000 : ℝ)
  | 12 => (-1610483356609 / 250000000000 : ℝ)
  | 13 => (-814385156009 / 125000000000 : ℝ)
  | 14 => (-6588877790153 / 1000000000000 : ℝ)
  | 15 => (-6663327602403 / 1000000000000 : ℝ)
  | 16 => (-6738435259531 / 1000000000000 : ℝ)
  | 17 => (-3407102680667 / 500000000000 : ℝ)
  | 18 => (-861330316601 / 125000000000 : ℝ)
  | 19 => (-1393550284849 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch053Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5548020017249 / 1000000000000 : ℝ)
  | 1 => (-2806568658519 / 500000000000 : ℝ)
  | 2 => (-2839423208863 / 500000000000 : ℝ)
  | 3 => (-1149030310713 / 200000000000 : ℝ)
  | 4 => (-1453014245617 / 250000000000 : ℝ)
  | 5 => (-2939783493053 / 500000000000 : ℝ)
  | 6 => (-594768587001 / 100000000000 : ℝ)
  | 7 => (-1504104490917 / 250000000000 : ℝ)
  | 8 => (-6085767620631 / 1000000000000 : ℝ)
  | 9 => (-1231147843723 / 200000000000 : ℝ)
  | 10 => (-6226337159597 / 1000000000000 : ℝ)
  | 11 => (-6297565869923 / 1000000000000 : ℝ)
  | 12 => (-6369429800407 / 1000000000000 : ℝ)
  | 13 => (-1288386685287 / 200000000000 : ℝ)
  | 14 => (-6515081248071 / 1000000000000 : ℝ)
  | 15 => (-823609723769 / 125000000000 : ℝ)
  | 16 => (-3331663801201 / 500000000000 : ℝ)
  | 17 => (-673843525953 / 100000000000 : ℝ)
  | 18 => (-6814205361333 / 1000000000000 : ℝ)
  | 19 => (-6890642532807 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch053Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1060 : ℝ) + (j.val : ℝ)) / 1600)
      (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch053Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch053Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1060 : ℝ) + (j.val : ℝ)) / 1600)
    (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch053Neg100WeightLower j.val) (hpThetaShiftOneBatch053Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch053Neg100WeightLower, hpThetaShiftOneBatch053Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch053Neg100_integral_bounds :
    (-702910582391 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-680787652413 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1060 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch053Lower hpThetaJensenCellsBatch053Upper
    hpThetaShiftOneBatch053Neg100WeightLower hpThetaShiftOneBatch053Neg100WeightUpper hpThetaJensenCellsBatch053_bounds hpThetaShiftOneBatch053Neg100_weight_bounds
  have hl : (-702910582391 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch053Lower j * hpThetaShiftOneBatch053Neg100WeightLower j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftOneBatch053Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftOneBatch053Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch053Lower j * hpThetaShiftOneBatch053Neg100WeightUpper j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftOneBatch053Neg100WeightUpper j) / 1600) ≤ (-680787652413 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftOneBatch053Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1060 : ℝ) / 1600 = 53 / 80 by norm_num,
    show ((1060 : ℝ) + 20) / 1600 = (53 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch053Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-26596177823 / 500000000000 : ℝ)
  | 1 => (-59969501457 / 1000000000000 : ℝ)
  | 2 => (-33422671027 / 500000000000 : ℝ)
  | 3 => (-73820766117 / 1000000000000 : ℝ)
  | 4 => (-80896667989 / 1000000000000 : ℝ)
  | 5 => (-88073947701 / 1000000000000 : ℝ)
  | 6 => (-95353510999 / 1000000000000 : ℝ)
  | 7 => (-102736269371 / 1000000000000 : ℝ)
  | 8 => (-110223140069 / 1000000000000 : ℝ)
  | 9 => (-117815046141 / 1000000000000 : ℝ)
  | 10 => (-62756458227 / 500000000000 : ℝ)
  | 11 => (-133317685721 / 1000000000000 : ℝ)
  | 12 => (-70615147263 / 500000000000 : ℝ)
  | 13 => (-74625844677 / 500000000000 : ℝ)
  | 14 => (-78691411307 / 500000000000 : ℝ)
  | 15 => (-165624652671 / 1000000000000 : ℝ)
  | 16 => (-86989071933 / 500000000000 : ℝ)
  | 17 => (-182444266547 / 1000000000000 : ℝ)
  | 18 => (-95511998549 / 500000000000 : ℝ)
  | 19 => (-4992957949 / 25000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch053Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5814127697 / 125000000000 : ℝ)
  | 1 => (-10638471129 / 200000000000 : ℝ)
  | 2 => (-3748093841 / 62500000000 : ℝ)
  | 3 => (-66845342053 / 1000000000000 : ℝ)
  | 4 => (-18455191529 / 250000000000 : ℝ)
  | 5 => (-20224166997 / 250000000000 : ℝ)
  | 6 => (-880739477 / 10000000000 : ℝ)
  | 7 => (-47676755499 / 500000000000 : ℝ)
  | 8 => (-10273626937 / 100000000000 : ℝ)
  | 9 => (-27555785017 / 250000000000 : ℝ)
  | 10 => (-5890752307 / 50000000000 : ℝ)
  | 11 => (-125512916453 / 1000000000000 : ℝ)
  | 12 => (-3332942143 / 25000000000 : ℝ)
  | 13 => (-5649211781 / 40000000000 : ℝ)
  | 14 => (-149251689353 / 1000000000000 : ℝ)
  | 15 => (-157382822613 / 1000000000000 : ℝ)
  | 16 => (-16562465267 / 100000000000 : ℝ)
  | 17 => (-34795628773 / 200000000000 : ℝ)
  | 18 => (-91222133273 / 500000000000 : ℝ)
  | 19 => (-191023997097 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch053Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1060 : ℝ) + (j.val : ℝ)) / 1600)
      (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch053Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch053Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1060 : ℝ) + (j.val : ℝ)) / 1600)
    (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch053Neg65WeightLower j.val) (hpThetaShiftOneBatch053Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch053Neg65WeightLower, hpThetaShiftOneBatch053Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch053Neg65_integral_bounds :
    (-13549418871 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-12432796977 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1060 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch053Lower hpThetaJensenCellsBatch053Upper
    hpThetaShiftOneBatch053Neg65WeightLower hpThetaShiftOneBatch053Neg65WeightUpper hpThetaJensenCellsBatch053_bounds hpThetaShiftOneBatch053Neg65_weight_bounds
  have hl : (-13549418871 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch053Lower j * hpThetaShiftOneBatch053Neg65WeightLower j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftOneBatch053Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftOneBatch053Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch053Lower j * hpThetaShiftOneBatch053Neg65WeightUpper j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftOneBatch053Neg65WeightUpper j) / 1600) ≤ (-12432796977 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftOneBatch053Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1060 : ℝ) / 1600 = 53 / 80 by norm_num,
    show ((1060 : ℝ) + 20) / 1600 = (53 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch053Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (130688831051 / 500000000000 : ℝ)
  | 1 => (52599235361 / 200000000000 : ℝ)
  | 2 => (132307125869 / 500000000000 : ℝ)
  | 3 => (133115894289 / 500000000000 : ℝ)
  | 4 => (53569737607 / 200000000000 : ℝ)
  | 5 => (5389296997 / 20000000000 : ℝ)
  | 6 => (27108017279 / 100000000000 : ℝ)
  | 7 => (272694554643 / 1000000000000 : ℝ)
  | 8 => (17144243263 / 62500000000 : ℝ)
  | 9 => (275920081297 / 1000000000000 : ℝ)
  | 10 => (277531016723 / 1000000000000 : ℝ)
  | 11 => (279140592299 / 1000000000000 : ℝ)
  | 12 => (280748700829 / 1000000000000 : ℝ)
  | 13 => (282355234107 / 1000000000000 : ℝ)
  | 14 => (141980041453 / 500000000000 : ℝ)
  | 15 => (142781568489 / 500000000000 : ℝ)
  | 16 => (287164285043 / 1000000000000 : ℝ)
  | 17 => (72190853697 / 250000000000 : ℝ)
  | 18 => (290360412859 / 1000000000000 : ℝ)
  | 19 => (145977582429 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch053Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (131498088403 / 500000000000 : ℝ)
  | 1 => (264614251739 / 1000000000000 : ℝ)
  | 2 => (266231788579 / 1000000000000 : ℝ)
  | 3 => (66962172009 / 250000000000 : ℝ)
  | 4 => (269464849851 / 1000000000000 : ℝ)
  | 5 => (271080172791 / 1000000000000 : ℝ)
  | 6 => (68173638661 / 250000000000 : ℝ)
  | 7 => (274307892209 / 1000000000000 : ℝ)
  | 8 => (137960040649 / 500000000000 : ℝ)
  | 9 => (69382754181 / 250000000000 : ℝ)
  | 10 => (2791405923 / 10000000000 : ℝ)
  | 11 => (28074870083 / 100000000000 : ℝ)
  | 12 => (70588808527 / 250000000000 : ℝ)
  | 13 => (283960082907 / 1000000000000 : ℝ)
  | 14 => (285563136979 / 1000000000000 : ℝ)
  | 15 => (71791071261 / 250000000000 : ℝ)
  | 16 => (288763414789 / 1000000000000 : ℝ)
  | 17 => (14518020643 / 50000000000 : ℝ)
  | 18 => (291955164859 / 1000000000000 : ℝ)
  | 19 => (293547555333 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch053Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1060 : ℝ) + (j.val : ℝ)) / 1600)
      (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch053Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch053Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1060 : ℝ) + (j.val : ℝ)) / 1600)
    (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch053Neg40WeightLower j.val) (hpThetaShiftOneBatch053Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch053Neg40WeightLower, hpThetaShiftOneBatch053Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch053Neg40_integral_bounds :
    (30443967799 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (15629106411 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1060 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch053Lower hpThetaJensenCellsBatch053Upper
    hpThetaShiftOneBatch053Neg40WeightLower hpThetaShiftOneBatch053Neg40WeightUpper hpThetaJensenCellsBatch053_bounds hpThetaShiftOneBatch053Neg40_weight_bounds
  have hl : (30443967799 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch053Lower j * hpThetaShiftOneBatch053Neg40WeightLower j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftOneBatch053Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftOneBatch053Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch053Lower j * hpThetaShiftOneBatch053Neg40WeightUpper j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftOneBatch053Neg40WeightUpper j) / 1600) ≤ (15629106411 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftOneBatch053Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1060 : ℝ) / 1600 = 53 / 80 by norm_num,
    show ((1060 : ℝ) + 20) / 1600 = (53 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch053Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-74949779981 / 1000000000000 : ℝ)
  | 1 => (-18679071181 / 250000000000 : ℝ)
  | 2 => (-18619725567 / 250000000000 : ℝ)
  | 3 => (-1159962761 / 15625000000 : ℝ)
  | 4 => (-73992412139 / 1000000000000 : ℝ)
  | 5 => (-36871636347 / 500000000000 : ℝ)
  | 6 => (-73490182501 / 1000000000000 : ℝ)
  | 7 => (-7323312571 / 100000000000 : ℝ)
  | 8 => (-18243021621 / 250000000000 : ℝ)
  | 9 => (-36353524501 / 500000000000 : ℝ)
  | 10 => (-72437997459 / 1000000000000 : ℝ)
  | 11 => (-36082458033 / 500000000000 : ℝ)
  | 12 => (-17971947263 / 250000000000 : ℝ)
  | 13 => (-71606600661 / 1000000000000 : ℝ)
  | 14 => (-17830333789 / 250000000000 : ℝ)
  | 15 => (-71031976819 / 1000000000000 : ℝ)
  | 16 => (-70738509949 / 1000000000000 : ℝ)
  | 17 => (-14088183773 / 200000000000 : ℝ)
  | 18 => (-35069593953 / 500000000000 : ℝ)
  | 19 => (-6983330143 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch053Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-74716284723 / 1000000000000 : ℝ)
  | 1 => (-74478902267 / 1000000000000 : ℝ)
  | 2 => (-74237616703 / 1000000000000 : ℝ)
  | 3 => (-36996206069 / 500000000000 : ℝ)
  | 4 => (-73743272693 / 1000000000000 : ℝ)
  | 5 => (-29396073 / 400000000 : ℝ)
  | 6 => (-73233125709 / 1000000000000 : ℝ)
  | 7 => (-72972086483 / 1000000000000 : ℝ)
  | 8 => (-72707049001 / 1000000000000 : ℝ)
  | 9 => (-36218998729 / 500000000000 : ℝ)
  | 10 => (-14432983213 / 200000000000 : ℝ)
  | 11 => (-71887789051 / 1000000000000 : ℝ)
  | 12 => (-3580330033 / 50000000000 : ℝ)
  | 13 => (-14264267031 / 200000000000 : ℝ)
  | 14 => (-35515988409 / 500000000000 : ℝ)
  | 15 => (-17684627487 / 250000000000 : ℝ)
  | 16 => (-4402557429 / 62500000000 : ℝ)
  | 17 => (-14027837581 / 200000000000 : ℝ)
  | 18 => (-69833301429 / 1000000000000 : ℝ)
  | 19 => (-13904648763 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch053Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1060 : ℝ) + (j.val : ℝ)) / 1600)
      (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch053Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch053Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1060 : ℝ) + (j.val : ℝ)) / 1600)
    (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch053Neg20WeightLower j.val) (hpThetaShiftOneBatch053Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch053Neg20WeightLower, hpThetaShiftOneBatch053Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch053Neg20_integral_bounds :
    (-8174174581 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-797794927 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1060 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch053Lower hpThetaJensenCellsBatch053Upper
    hpThetaShiftOneBatch053Neg20WeightLower hpThetaShiftOneBatch053Neg20WeightUpper hpThetaJensenCellsBatch053_bounds hpThetaShiftOneBatch053Neg20_weight_bounds
  have hl : (-8174174581 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch053Lower j * hpThetaShiftOneBatch053Neg20WeightLower j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftOneBatch053Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftOneBatch053Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch053Lower j * hpThetaShiftOneBatch053Neg20WeightUpper j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftOneBatch053Neg20WeightUpper j) / 1600) ≤ (-797794927 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftOneBatch053Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1060 : ℝ) / 1600 = 53 / 80 by norm_num,
    show ((1060 : ℝ) + 20) / 1600 = (53 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch053Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch053Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch053Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch053Neg20_integral_bounds
end HodgeProofHP
