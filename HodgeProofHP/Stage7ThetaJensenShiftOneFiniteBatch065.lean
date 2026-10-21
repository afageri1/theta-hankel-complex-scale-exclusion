/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch065

/-! Exact signed weight and batch integral certificates, batch 65 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch065Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6511237911081 / 125000000000 : ℝ)
  | 1 => (-52490496121377 / 1000000000000 : ℝ)
  | 2 => (-10578732465321 / 200000000000 : ℝ)
  | 3 => (-26649707764459 / 500000000000 : ℝ)
  | 4 => (-53707769411001 / 1000000000000 : ℝ)
  | 5 => (-5411873771383 / 100000000000 : ℝ)
  | 6 => (-852067722451 / 15625000000 : ℝ)
  | 7 => (-27474286419119 / 500000000000 : ℝ)
  | 8 => (-692093342937 / 12500000000 : ℝ)
  | 9 => (-55789032003101 / 1000000000000 : ℝ)
  | 10 => (-56213280577991 / 1000000000000 : ℝ)
  | 11 => (-3540014203401 / 62500000000 : ℝ)
  | 12 => (-5706988618681 / 100000000000 : ℝ)
  | 13 => (-28751135794727 / 500000000000 : ℝ)
  | 14 => (-57937397736671 / 1000000000000 : ℝ)
  | 15 => (-3648454935189 / 62500000000 : ℝ)
  | 16 => (-7351991207939 / 125000000000 : ℝ)
  | 17 => (-59259364293769 / 1000000000000 : ℝ)
  | 18 => (-59705597370263 / 1000000000000 : ℝ)
  | 19 => (-15038660867623 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch065Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-51691870261737 / 1000000000000 : ℝ)
  | 1 => (-52089903288647 / 1000000000000 : ℝ)
  | 2 => (-1640328003793 / 31250000000 : ℝ)
  | 3 => (-13223415581651 / 250000000000 : ℝ)
  | 4 => (-53299415528917 / 1000000000000 : ℝ)
  | 5 => (-53707769411 / 1000000000 : ℝ)
  | 6 => (-54118737713829 / 1000000000000 : ℝ)
  | 7 => (-54532334236863 / 1000000000000 : ℝ)
  | 8 => (-54948572838237 / 1000000000000 : ℝ)
  | 9 => (-55367467434959 / 1000000000000 : ℝ)
  | 10 => (-557890320031 / 10000000000 : ℝ)
  | 11 => (-5621328057799 / 100000000000 : ℝ)
  | 12 => (-11328045450883 / 200000000000 : ℝ)
  | 13 => (-57069886186809 / 1000000000000 : ℝ)
  | 14 => (-57502271589453 / 1000000000000 : ℝ)
  | 15 => (-5793739773667 / 100000000000 : ℝ)
  | 16 => (-58375278963023 / 1000000000000 : ℝ)
  | 17 => (-58815929663511 / 1000000000000 : ℝ)
  | 18 => (-7407420536721 / 125000000000 : ℝ)
  | 19 => (-29852798685131 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch065Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1300 : ℝ) + (j.val : ℝ)) / 1600)
      (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch065Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch065Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1300 : ℝ) + (j.val : ℝ)) / 1600)
    (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch065Neg100WeightLower j.val) (hpThetaShiftOneBatch065Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch065Neg100WeightLower, hpThetaShiftOneBatch065Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch065Neg100_integral_bounds :
    (-48840101427 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-188953175991 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch065Lower hpThetaJensenCellsBatch065Upper
    hpThetaShiftOneBatch065Neg100WeightLower hpThetaShiftOneBatch065Neg100WeightUpper hpThetaJensenCellsBatch065_bounds hpThetaShiftOneBatch065Neg100_weight_bounds
  have hl : (-48840101427 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch065Lower j * hpThetaShiftOneBatch065Neg100WeightLower j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftOneBatch065Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftOneBatch065Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch065Lower j * hpThetaShiftOneBatch065Neg100WeightUpper j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftOneBatch065Neg100WeightUpper j) / 1600) ≤ (-188953175991 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftOneBatch065Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1300 : ℝ) / 1600 = 65 / 80 by norm_num,
    show ((1300 : ℝ) + 20) / 1600 = (65 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch065Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-374132863471 / 50000000000 : ℝ)
  | 1 => (-755555607833 / 100000000000 : ℝ)
  | 2 => (-381450023879 / 50000000000 : ℝ)
  | 3 => (-7702993669291 / 1000000000000 : ℝ)
  | 4 => (-7777538870231 / 1000000000000 : ℝ)
  | 5 => (-3926319655929 / 500000000000 : ℝ)
  | 6 => (-7928298240377 / 1000000000000 : ℝ)
  | 7 => (-8004518916787 / 1000000000000 : ℝ)
  | 8 => (-1616260923387 / 200000000000 : ℝ)
  | 9 => (-8158658631563 / 1000000000000 : ℝ)
  | 10 => (-8236584266367 / 1000000000000 : ℝ)
  | 11 => (-4157542421019 / 500000000000 : ℝ)
  | 12 => (-2098540923581 / 250000000000 : ℝ)
  | 13 => (-338952966963 / 40000000000 : ℝ)
  | 14 => (-8554069647297 / 1000000000000 : ℝ)
  | 15 => (-2158725873801 / 250000000000 : ℝ)
  | 16 => (-8716329114271 / 1000000000000 : ℝ)
  | 17 => (-2199587479071 / 250000000000 : ℝ)
  | 18 => (-4440484664197 / 500000000000 : ℝ)
  | 19 => (-896419079317 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch065Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-7410300863317 / 1000000000000 : ℝ)
  | 1 => (-7482657269419 / 1000000000000 : ℝ)
  | 2 => (-7555556078329 / 1000000000000 : ℝ)
  | 3 => (-7629000477579 / 1000000000000 : ℝ)
  | 4 => (-770299366929 / 100000000000 : ℝ)
  | 5 => (-777753887023 / 100000000000 : ℝ)
  | 6 => (-7852639311857 / 1000000000000 : ℝ)
  | 7 => (-991037280047 / 125000000000 : ℝ)
  | 8 => (-4002259458393 / 500000000000 : ℝ)
  | 9 => (-4040652308467 / 500000000000 : ℝ)
  | 10 => (-4079329315781 / 500000000000 : ℝ)
  | 11 => (-4118292133183 / 500000000000 : ℝ)
  | 12 => (-8315084842037 / 1000000000000 : ℝ)
  | 13 => (-8394163694323 / 1000000000000 : ℝ)
  | 14 => (-4236912087037 / 500000000000 : ℝ)
  | 15 => (-133657338239 / 15625000000 : ℝ)
  | 16 => (-8634903495203 / 1000000000000 : ℝ)
  | 17 => (-871632911427 / 100000000000 : ℝ)
  | 18 => (-8798349916283 / 1000000000000 : ℝ)
  | 19 => (-8880969328393 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch065Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1300 : ℝ) + (j.val : ℝ)) / 1600)
      (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch065Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch065Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1300 : ℝ) + (j.val : ℝ)) / 1600)
    (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch065Neg65WeightLower j.val) (hpThetaShiftOneBatch065Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch065Neg65WeightLower, hpThetaShiftOneBatch065Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch065Neg65_integral_bounds :
    (-28576149443 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-27585334543 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch065Lower hpThetaJensenCellsBatch065Upper
    hpThetaShiftOneBatch065Neg65WeightLower hpThetaShiftOneBatch065Neg65WeightUpper hpThetaJensenCellsBatch065_bounds hpThetaShiftOneBatch065Neg65_weight_bounds
  have hl : (-28576149443 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch065Lower j * hpThetaShiftOneBatch065Neg65WeightLower j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftOneBatch065Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftOneBatch065Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch065Lower j * hpThetaShiftOneBatch065Neg65WeightUpper j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftOneBatch065Neg65WeightUpper j) / 1600) ≤ (-27585334543 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftOneBatch065Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1300 : ℝ) / 1600 = 65 / 80 by norm_num,
    show ((1300 : ℝ) + 20) / 1600 = (65 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch065Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (240360527467 / 1000000000000 : ℝ)
  | 1 => (235948124071 / 1000000000000 : ℝ)
  | 2 => (231468643373 / 1000000000000 : ℝ)
  | 3 => (56730388163 / 250000000000 : ℝ)
  | 4 => (111153158157 / 500000000000 : ℝ)
  | 5 => (108811197939 / 500000000000 : ℝ)
  | 6 => (106434624983 / 500000000000 : ℝ)
  | 7 => (52011583573 / 250000000000 : ℝ)
  | 8 => (101576550827 / 500000000000 : ℝ)
  | 9 => (49547250479 / 250000000000 : ℝ)
  | 10 => (38630696401 / 200000000000 : ℝ)
  | 11 => (188045985893 / 1000000000000 : ℝ)
  | 12 => (18286595459 / 100000000000 : ℝ)
  | 13 => (44403206533 / 250000000000 : ℝ)
  | 14 => (172286035569 / 1000000000000 : ℝ)
  | 15 => (166885014953 / 1000000000000 : ℝ)
  | 16 => (161409193329 / 1000000000000 : ℝ)
  | 17 => (155857996723 / 1000000000000 : ℝ)
  | 18 => (1173678501 / 7812500000 : ℝ)
  | 19 => (144527167497 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch065Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (244706383419 / 1000000000000 : ℝ)
  | 1 => (60090131867 / 250000000000 : ℝ)
  | 2 => (29493515509 / 125000000000 : ℝ)
  | 3 => (115734321687 / 500000000000 : ℝ)
  | 4 => (226921552653 / 1000000000000 : ℝ)
  | 5 => (44461263263 / 200000000000 : ℝ)
  | 6 => (217622395879 / 1000000000000 : ℝ)
  | 7 => (212869249967 / 1000000000000 : ℝ)
  | 8 => (208046334293 / 1000000000000 : ℝ)
  | 9 => (40630620331 / 200000000000 : ℝ)
  | 10 => (198189001917 / 1000000000000 : ℝ)
  | 11 => (96576741003 / 500000000000 : ℝ)
  | 12 => (94022992947 / 500000000000 : ℝ)
  | 13 => (182865954591 / 1000000000000 : ℝ)
  | 14 => (177612826133 / 1000000000000 : ℝ)
  | 15 => (17228603557 / 100000000000 : ℝ)
  | 16 => (83442507477 / 500000000000 : ℝ)
  | 17 => (16140919333 / 100000000000 : ℝ)
  | 18 => (38964499181 / 250000000000 : ℝ)
  | 19 => (150230848129 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch065Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1300 : ℝ) + (j.val : ℝ)) / 1600)
      (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch065Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch065Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1300 : ℝ) + (j.val : ℝ)) / 1600)
    (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch065Neg40WeightLower j.val) (hpThetaShiftOneBatch065Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch065Neg40WeightLower, hpThetaShiftOneBatch065Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch065Neg40_integral_bounds :
    (42087827 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (354176757 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch065Lower hpThetaJensenCellsBatch065Upper
    hpThetaShiftOneBatch065Neg40WeightLower hpThetaShiftOneBatch065Neg40WeightUpper hpThetaJensenCellsBatch065_bounds hpThetaShiftOneBatch065Neg40_weight_bounds
  have hl : (42087827 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch065Lower j * hpThetaShiftOneBatch065Neg40WeightLower j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftOneBatch065Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftOneBatch065Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch065Lower j * hpThetaShiftOneBatch065Neg40WeightUpper j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftOneBatch065Neg40WeightUpper j) / 1600) ≤ (354176757 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftOneBatch065Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1300 : ℝ) / 1600 = 65 / 80 by norm_num,
    show ((1300 : ℝ) + 20) / 1600 = (65 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch065Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (123634307467 / 1000000000000 : ℝ)
  | 1 => (782207877 / 6250000000 : ℝ)
  | 2 => (126678228569 / 1000000000000 : ℝ)
  | 3 => (128209206953 / 1000000000000 : ℝ)
  | 4 => (129746190019 / 1000000000000 : ℝ)
  | 5 => (1050313377 / 8000000000 : ℝ)
  | 6 => (26567629487 / 200000000000 : ℝ)
  | 7 => (67196554961 / 500000000000 : ℝ)
  | 8 => (67977026681 / 500000000000 : ℝ)
  | 9 => (137520971339 / 1000000000000 : ℝ)
  | 10 => (139093857237 / 1000000000000 : ℝ)
  | 11 => (140672704247 / 1000000000000 : ℝ)
  | 12 => (35564376339 / 250000000000 : ℝ)
  | 13 => (35962063339 / 250000000000 : ℝ)
  | 14 => (36361235209 / 250000000000 : ℝ)
  | 15 => (73523780091 / 500000000000 : ℝ)
  | 16 => (7432805179 / 50000000000 : ℝ)
  | 17 => (2347977547 / 15625000000 : ℝ)
  | 18 => (151890930241 / 1000000000000 : ℝ)
  | 19 => (9594824803 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch065Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (125153260321 / 1000000000000 : ℝ)
  | 1 => (12667822857 / 100000000000 : ℝ)
  | 2 => (64104603477 / 500000000000 : ℝ)
  | 3 => (6487309501 / 50000000000 : ℝ)
  | 4 => (65644586063 / 500000000000 : ℝ)
  | 5 => (33209536859 / 250000000000 : ℝ)
  | 6 => (134393109923 / 1000000000000 : ℝ)
  | 7 => (135954053363 / 1000000000000 : ℝ)
  | 8 => (6876048567 / 50000000000 : ℝ)
  | 9 => (69546928619 / 500000000000 : ℝ)
  | 10 => (17584088031 / 125000000000 : ℝ)
  | 11 => (142257505357 / 1000000000000 : ℝ)
  | 12 => (143848253357 / 1000000000000 : ℝ)
  | 13 => (145444940837 / 1000000000000 : ℝ)
  | 14 => (147047560183 / 1000000000000 : ℝ)
  | 15 => (148656103581 / 1000000000000 : ℝ)
  | 16 => (150270563009 / 1000000000000 : ℝ)
  | 17 => (75945465121 / 500000000000 : ℝ)
  | 18 => (153517196849 / 1000000000000 : ℝ)
  | 19 => (15514935419 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch065Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1300 : ℝ) + (j.val : ℝ)) / 1600)
      (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch065Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch065Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1300 : ℝ) + (j.val : ℝ)) / 1600)
    (((1300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch065Neg20WeightLower j.val) (hpThetaShiftOneBatch065Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch065Neg20WeightLower, hpThetaShiftOneBatch065Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch065Neg20_integral_bounds :
    (469150849 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (65 / 80 : ℝ) ((65 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (48690073 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch065Lower hpThetaJensenCellsBatch065Upper
    hpThetaShiftOneBatch065Neg20WeightLower hpThetaShiftOneBatch065Neg20WeightUpper hpThetaJensenCellsBatch065_bounds hpThetaShiftOneBatch065Neg20_weight_bounds
  have hl : (469150849 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch065Lower j * hpThetaShiftOneBatch065Neg20WeightLower j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftOneBatch065Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftOneBatch065Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch065Lower j * hpThetaShiftOneBatch065Neg20WeightUpper j)
        (hpThetaJensenCellsBatch065Upper j * hpThetaShiftOneBatch065Neg20WeightUpper j) / 1600) ≤ (48690073 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch065Lower, hpThetaJensenCellsBatch065Upper,
      hpThetaShiftOneBatch065Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1300 : ℝ) / 1600 = 65 / 80 by norm_num,
    show ((1300 : ℝ) + 20) / 1600 = (65 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch065Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch065Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch065Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch065Neg20_integral_bounds
end HodgeProofHP
