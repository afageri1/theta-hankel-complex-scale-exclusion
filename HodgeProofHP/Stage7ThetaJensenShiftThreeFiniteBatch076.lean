/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch076

/-! Exact signed weight and batch integral certificates, batch 76 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch076Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-166851808771 / 500000000000 : ℝ)
  | 1 => (-42105851321 / 125000000000 : ℝ)
  | 2 => (-21251028393 / 62500000000 : ℝ)
  | 3 => (-171606373289 / 500000000000 : ℝ)
  | 4 => (-173217943309 / 500000000000 : ℝ)
  | 5 => (-349686074903 / 1000000000000 : ℝ)
  | 6 => (-11030109789 / 31250000000 : ℝ)
  | 7 => (-222667753 / 625000000 : ℝ)
  | 8 => (-179800477019 / 500000000000 : ℝ)
  | 9 => (-90740341697 / 250000000000 : ℝ)
  | 10 => (-91587462557 / 250000000000 : ℝ)
  | 11 => (-369766612893 / 1000000000000 : ℝ)
  | 12 => (-373211864687 / 1000000000000 : ℝ)
  | 13 => (-37668581689 / 100000000000 : ℝ)
  | 14 => (-95047170541 / 250000000000 : ℝ)
  | 15 => (-191860337281 / 500000000000 : ℝ)
  | 16 => (-387282009537 / 1000000000000 : ℝ)
  | 17 => (-195436451973 / 500000000000 : ℝ)
  | 18 => (-3081981063 / 7812500000 : ℝ)
  | 19 => (-99536061397 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch076Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-41323334829 / 125000000000 : ℝ)
  | 1 => (-333703617541 / 1000000000000 : ℝ)
  | 2 => (-336846810567 / 1000000000000 : ℝ)
  | 3 => (-340016454287 / 1000000000000 : ℝ)
  | 4 => (-343212746577 / 1000000000000 : ℝ)
  | 5 => (-346435886617 / 1000000000000 : ℝ)
  | 6 => (-174843037451 / 500000000000 : ℝ)
  | 7 => (-352963513247 / 1000000000000 : ℝ)
  | 8 => (-356268404799 / 1000000000000 : ℝ)
  | 9 => (-359600954037 / 1000000000000 : ℝ)
  | 10 => (-362961366787 / 1000000000000 : ℝ)
  | 11 => (-366349850227 / 1000000000000 : ℝ)
  | 12 => (-92441653223 / 250000000000 : ℝ)
  | 13 => (-186605932343 / 500000000000 : ℝ)
  | 14 => (-376685816889 / 1000000000000 : ℝ)
  | 15 => (-380188682163 / 1000000000000 : ℝ)
  | 16 => (-383720674561 / 1000000000000 : ℝ)
  | 17 => (-6051281399 / 15625000000 : ℝ)
  | 18 => (-78174580789 / 200000000000 : ℝ)
  | 19 => (-394493576063 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch076Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1520 : ℝ) + (j.val : ℝ)) / 1600)
      (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch076Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch076Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1520 : ℝ) + (j.val : ℝ)) / 1600)
    (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch076Neg100WeightLower j.val) (hpThetaShiftThreeBatch076Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch076Neg100WeightLower, hpThetaShiftThreeBatch076Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch076Neg100_integral_bounds :
    (-14627081 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-14033211 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch076Lower hpThetaJensenCellsBatch076Upper
    hpThetaShiftThreeBatch076Neg100WeightLower hpThetaShiftThreeBatch076Neg100WeightUpper hpThetaJensenCellsBatch076_bounds hpThetaShiftThreeBatch076Neg100_weight_bounds
  have hl : (-14627081 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch076Lower j * hpThetaShiftThreeBatch076Neg100WeightLower j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftThreeBatch076Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftThreeBatch076Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch076Lower j * hpThetaShiftThreeBatch076Neg100WeightUpper j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftThreeBatch076Neg100WeightUpper j) / 1600) ≤ (-14033211 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftThreeBatch076Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1520 : ℝ) / 1600 = 76 / 80 by norm_num,
    show ((1520 : ℝ) + 20) / 1600 = (76 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch076Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-32522003623 / 500000000000 : ℝ)
  | 1 => (-32875362809 / 500000000000 : ℝ)
  | 2 => (-66464059973 / 1000000000000 : ℝ)
  | 3 => (-67184064013 / 1000000000000 : ℝ)
  | 4 => (-67910791821 / 1000000000000 : ℝ)
  | 5 => (-34322148929 / 500000000000 : ℝ)
  | 6 => (-8673079621 / 125000000000 : ℝ)
  | 7 => (-3506593219 / 50000000000 : ℝ)
  | 8 => (-17721508927 / 250000000000 : ℝ)
  | 9 => (-35823603479 / 500000000000 : ℝ)
  | 10 => (-72415434527 / 1000000000000 : ℝ)
  | 11 => (-73190775203 / 1000000000000 : ℝ)
  | 12 => (-2958931447 / 40000000000 : ℝ)
  | 13 => (-74763025027 / 1000000000000 : ℝ)
  | 14 => (-37780024873 / 500000000000 : ℝ)
  | 15 => (-76364418721 / 1000000000000 : ℝ)
  | 16 => (-308704763 / 4000000000 : ℝ)
  | 17 => (-19498856259 / 250000000000 : ℝ)
  | 18 => (-39411090597 / 500000000000 : ℝ)
  | 19 => (-79656519253 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch076Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2573754061 / 40000000000 : ℝ)
  | 1 => (-13008801449 / 200000000000 : ℝ)
  | 2 => (-65750725617 / 1000000000000 : ℝ)
  | 3 => (-16616014993 / 250000000000 : ℝ)
  | 4 => (-16796016003 / 250000000000 : ℝ)
  | 5 => (-3395539591 / 50000000000 : ℝ)
  | 6 => (-68644297857 / 1000000000000 : ℝ)
  | 7 => (-69384636967 / 1000000000000 : ℝ)
  | 8 => (-70131864379 / 1000000000000 : ℝ)
  | 9 => (-70886035707 / 1000000000000 : ℝ)
  | 10 => (-71647206957 / 1000000000000 : ℝ)
  | 11 => (-36207717263 / 500000000000 : ℝ)
  | 12 => (-36595387601 / 500000000000 : ℝ)
  | 13 => (-36986643087 / 500000000000 : ℝ)
  | 14 => (-37381512513 / 500000000000 : ℝ)
  | 15 => (-15112009949 / 200000000000 : ℝ)
  | 16 => (-477277617 / 6250000000 : ℝ)
  | 17 => (-77176190749 / 1000000000000 : ℝ)
  | 18 => (-15599085007 / 200000000000 : ℝ)
  | 19 => (-78822181193 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch076Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1520 : ℝ) + (j.val : ℝ)) / 1600)
      (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch076Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch076Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1520 : ℝ) + (j.val : ℝ)) / 1600)
    (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch076Neg70WeightLower j.val) (hpThetaShiftThreeBatch076Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch076Neg70WeightLower, hpThetaShiftThreeBatch076Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch076Neg70_integral_bounds :
    (-2887211 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-1383083 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch076Lower hpThetaJensenCellsBatch076Upper
    hpThetaShiftThreeBatch076Neg70WeightLower hpThetaShiftThreeBatch076Neg70WeightUpper hpThetaJensenCellsBatch076_bounds hpThetaShiftThreeBatch076Neg70_weight_bounds
  have hl : (-2887211 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch076Lower j * hpThetaShiftThreeBatch076Neg70WeightLower j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftThreeBatch076Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftThreeBatch076Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch076Lower j * hpThetaShiftThreeBatch076Neg70WeightUpper j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftThreeBatch076Neg70WeightUpper j) / 1600) ≤ (-1383083 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftThreeBatch076Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1520 : ℝ) / 1600 = 76 / 80 by norm_num,
    show ((1520 : ℝ) + 20) / 1600 = (76 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch076Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-241756451 / 250000000000 : ℝ)
  | 1 => (-1017565783 / 1000000000000 : ℝ)
  | 2 => (-534438891 / 500000000000 : ℝ)
  | 3 => (-56048501 / 50000000000 : ℝ)
  | 4 => (-1173850789 / 1000000000000 : ℝ)
  | 5 => (-1227528449 / 1000000000000 : ℝ)
  | 6 => (-1282011427 / 1000000000000 : ℝ)
  | 7 => (-53492329 / 40000000000 : ℝ)
  | 8 => (-1393427413 / 1000000000000 : ℝ)
  | 9 => (-45324301 / 31250000000 : ℝ)
  | 10 => (-377041899 / 250000000000 : ℝ)
  | 11 => (-391701523 / 250000000000 : ℝ)
  | 12 => (-813150989 / 500000000000 : ℝ)
  | 13 => (-843332093 / 500000000000 : ℝ)
  | 14 => (-1747901721 / 1000000000000 : ℝ)
  | 15 => (-113126479 / 62500000000 : ℝ)
  | 16 => (-1873039169 / 1000000000000 : ℝ)
  | 17 => (-1936957467 / 1000000000000 : ℝ)
  | 18 => (-2001787863 / 1000000000000 : ℝ)
  | 19 => (-2067539739 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch076Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-91724969 / 100000000000 : ℝ)
  | 1 => (-967025803 / 1000000000000 : ℝ)
  | 2 => (-508782891 / 500000000000 : ℝ)
  | 3 => (-1068877781 / 1000000000000 : ℝ)
  | 4 => (-1120970019 / 1000000000000 : ℝ)
  | 5 => (-293462697 / 250000000000 : ℝ)
  | 6 => (-4795033 / 3906250000 : ℝ)
  | 7 => (-641005713 / 500000000000 : ℝ)
  | 8 => (-20895441 / 15625000000 : ℝ)
  | 9 => (-348356853 / 250000000000 : ℝ)
  | 10 => (-1450377631 / 1000000000000 : ℝ)
  | 11 => (-301633519 / 200000000000 : ℝ)
  | 12 => (-1566806091 / 1000000000000 : ℝ)
  | 13 => (-1626301977 / 1000000000000 : ℝ)
  | 14 => (-337332837 / 200000000000 : ℝ)
  | 15 => (-43697543 / 25000000000 : ℝ)
  | 16 => (-1810023663 / 1000000000000 : ℝ)
  | 17 => (-29266237 / 15625000000 : ℝ)
  | 18 => (-968478733 / 500000000000 : ℝ)
  | 19 => (-1000893931 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch076Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1520 : ℝ) + (j.val : ℝ)) / 1600)
      (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch076Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch076Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1520 : ℝ) + (j.val : ℝ)) / 1600)
    (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch076Neg45WeightLower j.val) (hpThetaShiftThreeBatch076Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch076Neg45WeightLower, hpThetaShiftThreeBatch076Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch076Neg45_integral_bounds :
    (-913 / 15625000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-27179 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch076Lower hpThetaJensenCellsBatch076Upper
    hpThetaShiftThreeBatch076Neg45WeightLower hpThetaShiftThreeBatch076Neg45WeightUpper hpThetaJensenCellsBatch076_bounds hpThetaShiftThreeBatch076Neg45_weight_bounds
  have hl : (-913 / 15625000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch076Lower j * hpThetaShiftThreeBatch076Neg45WeightLower j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftThreeBatch076Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftThreeBatch076Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch076Lower j * hpThetaShiftThreeBatch076Neg45WeightUpper j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftThreeBatch076Neg45WeightUpper j) / 1600) ≤ (-27179 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftThreeBatch076Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1520 : ℝ) / 1600 = 76 / 80 by norm_num,
    show ((1520 : ℝ) + 20) / 1600 = (76 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch076Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (235440343 / 250000000000 : ℝ)
  | 1 => (477074529 / 500000000000 : ℝ)
  | 2 => (966619699 / 1000000000000 : ℝ)
  | 3 => (97917351 / 100000000000 : ℝ)
  | 4 => (495905351 / 500000000000 : ℝ)
  | 5 => (200906297 / 200000000000 : ℝ)
  | 6 => (3973969 / 3906250000 : ℝ)
  | 7 => (206044929 / 200000000000 : ℝ)
  | 8 => (1043197429 / 1000000000000 : ℝ)
  | 9 => (1056254617 / 1000000000000 : ℝ)
  | 10 => (1069396407 / 1000000000000 : ℝ)
  | 11 => (1082622993 / 1000000000000 : ℝ)
  | 12 => (1095934567 / 1000000000000 : ℝ)
  | 13 => (1109331321 / 1000000000000 : ℝ)
  | 14 => (561406721 / 500000000000 : ℝ)
  | 15 => (568190557 / 500000000000 : ℝ)
  | 16 => (1150034521 / 1000000000000 : ℝ)
  | 17 => (581886921 / 500000000000 : ℝ)
  | 18 => (588799627 / 500000000000 : ℝ)
  | 19 => (297877733 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch076Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (954149059 / 1000000000000 : ℝ)
  | 1 => (9666197 / 10000000000 : ℝ)
  | 2 => (979173511 / 1000000000000 : ℝ)
  | 3 => (991810703 / 1000000000000 : ℝ)
  | 4 => (502265743 / 500000000000 : ℝ)
  | 5 => (203467213 / 200000000000 : ℝ)
  | 6 => (515112323 / 500000000000 : ℝ)
  | 7 => (104319743 / 100000000000 : ℝ)
  | 8 => (528127309 / 500000000000 : ℝ)
  | 9 => (133674551 / 125000000000 : ℝ)
  | 10 => (541311497 / 500000000000 : ℝ)
  | 11 => (136991821 / 125000000000 : ℝ)
  | 12 => (554665661 / 500000000000 : ℝ)
  | 13 => (1122813443 / 1000000000000 : ℝ)
  | 14 => (227276223 / 200000000000 : ℝ)
  | 15 => (575017261 / 500000000000 : ℝ)
  | 16 => (1163773843 / 1000000000000 : ℝ)
  | 17 => (235519851 / 200000000000 : ℝ)
  | 18 => (1191510933 / 1000000000000 : ℝ)
  | 19 => (1205509047 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch076Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1520 : ℝ) + (j.val : ℝ)) / 1600)
      (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch076Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch076Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1520 : ℝ) + (j.val : ℝ)) / 1600)
    (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch076Neg25WeightLower j.val) (hpThetaShiftThreeBatch076Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch076Neg25WeightLower, hpThetaShiftThreeBatch076Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch076Neg25_integral_bounds :
    (8237 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (43061 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch076Lower hpThetaJensenCellsBatch076Upper
    hpThetaShiftThreeBatch076Neg25WeightLower hpThetaShiftThreeBatch076Neg25WeightUpper hpThetaJensenCellsBatch076_bounds hpThetaShiftThreeBatch076Neg25_weight_bounds
  have hl : (8237 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch076Lower j * hpThetaShiftThreeBatch076Neg25WeightLower j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftThreeBatch076Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftThreeBatch076Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch076Lower j * hpThetaShiftThreeBatch076Neg25WeightUpper j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftThreeBatch076Neg25WeightUpper j) / 1600) ≤ (43061 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftThreeBatch076Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1520 : ℝ) / 1600 = 76 / 80 by norm_num,
    show ((1520 : ℝ) + 20) / 1600 = (76 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch076Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch076Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch076Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch076Neg25_integral_bounds
end HodgeProofHP
