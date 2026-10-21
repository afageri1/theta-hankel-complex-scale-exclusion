/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch076

/-! Exact signed weight and batch integral certificates, batch 76 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch076Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-9797800981117 / 1000000000000 : ℝ)
  | 1 => (-9873549850759 / 1000000000000 : ℝ)
  | 2 => (-2487453092161 / 250000000000 : ℝ)
  | 3 => (-2005318312183 / 200000000000 : ℝ)
  | 4 => (-2525972617249 / 250000000000 : ℝ)
  | 5 => (-10181712149661 / 1000000000000 : ℝ)
  | 6 => (-2052011935019 / 200000000000 : ℝ)
  | 7 => (-2584734033241 / 250000000000 : ℝ)
  | 8 => (-416733785059 / 40000000000 : ℝ)
  | 9 => (-10498288274447 / 1000000000000 : ℝ)
  | 10 => (-10578770211373 / 1000000000000 : ℝ)
  | 11 => (-2664948396873 / 250000000000 : ℝ)
  | 12 => (-10741361568847 / 1000000000000 : ℝ)
  | 13 => (-135293466717 / 12500000000 : ℝ)
  | 14 => (-5453072045447 / 500000000000 : ℝ)
  | 15 => (-5494682521661 / 500000000000 : ℝ)
  | 16 => (-5536571712297 / 500000000000 : ℝ)
  | 17 => (-5578741240403 / 500000000000 : ℝ)
  | 18 => (-1405298184283 / 125000000000 : ℝ)
  | 19 => (-11327855683559 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch076Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4861281374397 / 500000000000 : ℝ)
  | 1 => (-2449450245279 / 250000000000 : ℝ)
  | 2 => (-4936774925379 / 500000000000 : ℝ)
  | 3 => (-9949812368643 / 1000000000000 : ℝ)
  | 4 => (-5013295780457 / 500000000000 : ℝ)
  | 5 => (-2020778093799 / 200000000000 : ℝ)
  | 6 => (-509085607483 / 50000000000 : ℝ)
  | 7 => (-5130029837547 / 500000000000 : ℝ)
  | 8 => (-10338936132963 / 1000000000000 : ℝ)
  | 9 => (-5209172313237 / 500000000000 : ℝ)
  | 10 => (-5249144137223 / 500000000000 : ℝ)
  | 11 => (-2644692552843 / 250000000000 : ℝ)
  | 12 => (-10659793587491 / 1000000000000 : ℝ)
  | 13 => (-5370680784423 / 500000000000 : ℝ)
  | 14 => (-10823477337359 / 1000000000000 : ℝ)
  | 15 => (-10906144090893 / 1000000000000 : ℝ)
  | 16 => (-10989365043321 / 1000000000000 : ℝ)
  | 17 => (-11073143424593 / 1000000000000 : ℝ)
  | 18 => (-2231496496161 / 200000000000 : ℝ)
  | 19 => (-11242385474263 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch076Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1520 : ℝ) + (j.val : ℝ)) / 1600)
      (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch076Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch076Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1520 : ℝ) + (j.val : ℝ)) / 1600)
    (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch076Neg100WeightLower j.val) (hpThetaShiftTwoBatch076Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch076Neg100WeightLower, hpThetaShiftTwoBatch076Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch076Neg100_integral_bounds :
    (-423090299 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-203293261 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch076Lower hpThetaJensenCellsBatch076Upper
    hpThetaShiftTwoBatch076Neg100WeightLower hpThetaShiftTwoBatch076Neg100WeightUpper hpThetaJensenCellsBatch076_bounds hpThetaShiftTwoBatch076Neg100_weight_bounds
  have hl : (-423090299 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch076Lower j * hpThetaShiftTwoBatch076Neg100WeightLower j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftTwoBatch076Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftTwoBatch076Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch076Lower j * hpThetaShiftTwoBatch076Neg100WeightUpper j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftTwoBatch076Neg100WeightUpper j) / 1600) ≤ (-203293261 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftTwoBatch076Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1520 : ℝ) / 1600 = 76 / 80 by norm_num,
    show ((1520 : ℝ) + 20) / 1600 = (76 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch076Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1572835447181 / 1000000000000 : ℝ)
  | 1 => (-1586960414817 / 1000000000000 : ℝ)
  | 2 => (-1601192393347 / 1000000000000 : ℝ)
  | 3 => (-1615532068183 / 1000000000000 : ℝ)
  | 4 => (-814990064211 / 500000000000 : ℝ)
  | 5 => (-1644537266869 / 1000000000000 : ℝ)
  | 6 => (-1659204180047 / 1000000000000 : ℝ)
  | 7 => (-836990784109 / 500000000000 : ℝ)
  | 8 => (-1688870135397 / 1000000000000 : ℝ)
  | 9 => (-170387058937 / 100000000000 : ℝ)
  | 10 => (-1718983641709 / 1000000000000 : ℝ)
  | 11 => (-1734210007793 / 1000000000000 : ℝ)
  | 12 => (-1749550406819 / 1000000000000 : ℝ)
  | 13 => (-55156423807 / 31250000000 : ℝ)
  | 14 => (-1780576199699 / 1000000000000 : ℝ)
  | 15 => (-898131525603 / 500000000000 : ℝ)
  | 16 => (-906033425499 / 500000000000 : ℝ)
  | 17 => (-57124635551 / 31250000000 : ℝ)
  | 18 => (-184402825359 / 100000000000 : ℝ)
  | 19 => (-930093672647 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch076Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-779408404349 / 500000000000 : ℝ)
  | 1 => (-78641772359 / 50000000000 : ℝ)
  | 2 => (-49592512963 / 31250000000 : ℝ)
  | 3 => (-800596196673 / 500000000000 : ℝ)
  | 4 => (-807766034091 / 500000000000 : ℝ)
  | 5 => (-1629980128421 / 1000000000000 : ℝ)
  | 6 => (-411134316717 / 250000000000 : ℝ)
  | 7 => (-829602090023 / 500000000000 : ℝ)
  | 8 => (-1673981568217 / 1000000000000 : ℝ)
  | 9 => (-422217533849 / 250000000000 : ℝ)
  | 10 => (-1703870589369 / 1000000000000 : ℝ)
  | 11 => (-429745910427 / 250000000000 : ℝ)
  | 12 => (-108388125487 / 62500000000 : ℝ)
  | 13 => (-874775203409 / 500000000000 : ℝ)
  | 14 => (-1765005561823 / 1000000000000 : ℝ)
  | 15 => (-890288099849 / 500000000000 : ℝ)
  | 16 => (-359252610241 / 200000000000 : ℝ)
  | 17 => (-1812066850997 / 1000000000000 : ℝ)
  | 18 => (-1827988337631 / 1000000000000 : ℝ)
  | 19 => (-1844028253589 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch076Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1520 : ℝ) + (j.val : ℝ)) / 1600)
      (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch076Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch076Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1520 : ℝ) + (j.val : ℝ)) / 1600)
    (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch076Neg65WeightLower j.val) (hpThetaShiftTwoBatch076Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch076Neg65WeightLower, hpThetaShiftTwoBatch076Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch076Neg65_integral_bounds :
    (-429131 / 6250000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-13180701 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch076Lower hpThetaJensenCellsBatch076Upper
    hpThetaShiftTwoBatch076Neg65WeightLower hpThetaShiftTwoBatch076Neg65WeightUpper hpThetaJensenCellsBatch076_bounds hpThetaShiftTwoBatch076Neg65_weight_bounds
  have hl : (-429131 / 6250000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch076Lower j * hpThetaShiftTwoBatch076Neg65WeightLower j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftTwoBatch076Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftTwoBatch076Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch076Lower j * hpThetaShiftTwoBatch076Neg65WeightUpper j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftTwoBatch076Neg65WeightUpper j) / 1600) ≤ (-13180701 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftTwoBatch076Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1520 : ℝ) / 1600 = 76 / 80 by norm_num,
    show ((1520 : ℝ) + 20) / 1600 = (76 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch076Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-33339521313 / 200000000000 : ℝ)
  | 1 => (-169061097631 / 1000000000000 : ℝ)
  | 2 => (-171447448299 / 1000000000000 : ℝ)
  | 3 => (-17385682927 / 100000000000 : ℝ)
  | 4 => (-176289412263 / 1000000000000 : ℝ)
  | 5 => (-178745370019 / 1000000000000 : ℝ)
  | 6 => (-18122487631 / 100000000000 : ℝ)
  | 7 => (-9186405297 / 50000000000 : ℝ)
  | 8 => (-186255234749 / 1000000000000 : ℝ)
  | 9 => (-188806439623 / 1000000000000 : ℝ)
  | 10 => (-747585541 / 3906250000 : ℝ)
  | 11 => (-12123861897 / 62500000000 : ℝ)
  | 12 => (-49151573809 / 250000000000 : ℝ)
  | 13 => (-99627797127 / 500000000000 : ℝ)
  | 14 => (-100964934791 / 500000000000 : ℝ)
  | 15 => (-51157326117 / 250000000000 : ℝ)
  | 16 => (-103677041619 / 500000000000 : ℝ)
  | 17 => (-105052195651 / 500000000000 : ℝ)
  | 18 => (-106440207579 / 500000000000 : ℝ)
  | 19 => (-107841171199 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch076Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-164356805413 / 1000000000000 : ℝ)
  | 1 => (-41674401641 / 250000000000 : ℝ)
  | 2 => (-16906109763 / 100000000000 : ℝ)
  | 3 => (-85723724149 / 500000000000 : ℝ)
  | 4 => (-173856829269 / 1000000000000 : ℝ)
  | 5 => (-88144706131 / 500000000000 : ℝ)
  | 6 => (-89372685009 / 500000000000 : ℝ)
  | 7 => (-181224876309 / 1000000000000 : ℝ)
  | 8 => (-183728105939 / 1000000000000 : ℝ)
  | 9 => (-46563808687 / 250000000000 : ℝ)
  | 10 => (-94403219811 / 500000000000 : ℝ)
  | 11 => (-38276379699 / 200000000000 : ℝ)
  | 12 => (-193981790351 / 1000000000000 : ℝ)
  | 13 => (-39321259047 / 200000000000 : ℝ)
  | 14 => (-199255594253 / 1000000000000 : ℝ)
  | 15 => (-201929869581 / 1000000000000 : ℝ)
  | 16 => (-204629304467 / 1000000000000 : ℝ)
  | 17 => (-207354083237 / 1000000000000 : ℝ)
  | 18 => (-210104391301 / 1000000000000 : ℝ)
  | 19 => (-212880415157 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch076Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1520 : ℝ) + (j.val : ℝ)) / 1600)
      (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch076Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch076Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1520 : ℝ) + (j.val : ℝ)) / 1600)
    (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch076Neg45WeightLower j.val) (hpThetaShiftTwoBatch076Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch076Neg45WeightLower, hpThetaShiftTwoBatch076Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch076Neg45_integral_bounds :
    (-380297 / 50000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-3632873 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch076Lower hpThetaJensenCellsBatch076Upper
    hpThetaShiftTwoBatch076Neg45WeightLower hpThetaShiftTwoBatch076Neg45WeightUpper hpThetaJensenCellsBatch076_bounds hpThetaShiftTwoBatch076Neg45_weight_bounds
  have hl : (-380297 / 50000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch076Lower j * hpThetaShiftTwoBatch076Neg45WeightLower j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftTwoBatch076Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftTwoBatch076Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch076Lower j * hpThetaShiftTwoBatch076Neg45WeightUpper j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftTwoBatch076Neg45WeightUpper j) / 1600) ≤ (-3632873 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftTwoBatch076Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1520 : ℝ) / 1600 = 76 / 80 by norm_num,
    show ((1520 : ℝ) + 20) / 1600 = (76 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch076Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4937557447 / 125000000000 : ℝ)
  | 1 => (39727331019 / 1000000000000 : ℝ)
  | 2 => (39954476903 / 1000000000000 : ℝ)
  | 3 => (20090944637 / 500000000000 : ℝ)
  | 4 => (40409560083 / 1000000000000 : ℝ)
  | 5 => (40637481193 / 1000000000000 : ℝ)
  | 6 => (40865644373 / 1000000000000 : ℝ)
  | 7 => (410940413 / 10000000000 : ℝ)
  | 8 => (41322663557 / 1000000000000 : ℝ)
  | 9 => (20775751317 / 500000000000 : ℝ)
  | 10 => (41780549927 / 1000000000000 : ℝ)
  | 11 => (8401959347 / 200000000000 : ℝ)
  | 12 => (42239234263 / 1000000000000 : ℝ)
  | 13 => (42468853619 / 1000000000000 : ℝ)
  | 14 => (42698645813 / 1000000000000 : ℝ)
  | 15 => (42928601761 / 1000000000000 : ℝ)
  | 16 => (43158712277 / 1000000000000 : ℝ)
  | 17 => (43388968079 / 1000000000000 : ℝ)
  | 18 => (43619359783 / 1000000000000 : ℝ)
  | 19 => (43849877907 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch076Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1986366551 / 50000000000 : ℝ)
  | 1 => (4994309613 / 125000000000 : ℝ)
  | 2 => (1607275571 / 40000000000 : ℝ)
  | 3 => (10102390021 / 250000000000 : ℝ)
  | 4 => (20318740597 / 500000000000 : ℝ)
  | 5 => (20432822187 / 500000000000 : ℝ)
  | 6 => (41094041301 / 1000000000000 : ℝ)
  | 7 => (20661331779 / 500000000000 : ℝ)
  | 8 => (8310300527 / 200000000000 : ℝ)
  | 9 => (5222568741 / 125000000000 : ℝ)
  | 10 => (328201537 / 7812500000 : ℝ)
  | 11 => (5279904283 / 125000000000 : ℝ)
  | 12 => (2123442681 / 50000000000 : ℝ)
  | 13 => (21349322907 / 500000000000 : ℝ)
  | 14 => (21464300881 / 500000000000 : ℝ)
  | 15 => (21579356139 / 500000000000 : ℝ)
  | 16 => (542362101 / 12500000000 : ℝ)
  | 17 => (5452419973 / 125000000000 : ℝ)
  | 18 => (10962469477 / 250000000000 : ℝ)
  | 19 => (44080512869 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch076Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1520 : ℝ) + (j.val : ℝ)) / 1600)
      (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch076Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch076Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1520 : ℝ) + (j.val : ℝ)) / 1600)
    (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch076Neg25WeightLower j.val) (hpThetaShiftTwoBatch076Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch076Neg25WeightLower, hpThetaShiftTwoBatch076Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch076Neg25_integral_bounds :
    (202667 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (420883 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch076Lower hpThetaJensenCellsBatch076Upper
    hpThetaShiftTwoBatch076Neg25WeightLower hpThetaShiftTwoBatch076Neg25WeightUpper hpThetaJensenCellsBatch076_bounds hpThetaShiftTwoBatch076Neg25_weight_bounds
  have hl : (202667 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch076Lower j * hpThetaShiftTwoBatch076Neg25WeightLower j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftTwoBatch076Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftTwoBatch076Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch076Lower j * hpThetaShiftTwoBatch076Neg25WeightUpper j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftTwoBatch076Neg25WeightUpper j) / 1600) ≤ (420883 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftTwoBatch076Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1520 : ℝ) / 1600 = 76 / 80 by norm_num,
    show ((1520 : ℝ) + 20) / 1600 = (76 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch076Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch076Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch076Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch076Neg25_integral_bounds
end HodgeProofHP
