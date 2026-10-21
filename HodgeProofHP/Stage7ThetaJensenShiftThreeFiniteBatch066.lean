/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch066

/-! Exact signed weight and batch integral certificates, batch 66 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch066Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-40705874813 / 1000000000000 : ℝ)
  | 1 => (-1029862187 / 25000000000 : ℝ)
  | 2 => (-41688214937 / 1000000000000 : ℝ)
  | 3 => (-42187103967 / 1000000000000 : ℝ)
  | 4 => (-42691201723 / 1000000000000 : ℝ)
  | 5 => (-21600277869 / 500000000000 : ℝ)
  | 6 => (-21857606959 / 500000000000 : ℝ)
  | 7 => (-22117612277 / 500000000000 : ℝ)
  | 8 => (-11190159079 / 250000000000 : ℝ)
  | 9 => (-22645749131 / 500000000000 : ℝ)
  | 10 => (-22913929919 / 500000000000 : ℝ)
  | 11 => (-46369770881 / 1000000000000 : ℝ)
  | 12 => (-46917281621 / 1000000000000 : ℝ)
  | 13 => (-11867610671 / 250000000000 : ℝ)
  | 14 => (-6003663137 / 125000000000 : ℝ)
  | 15 => (-24296960143 / 500000000000 : ℝ)
  | 16 => (-9832868017 / 200000000000 : ℝ)
  | 17 => (-12435154183 / 250000000000 : ℝ)
  | 18 => (-50322802877 / 1000000000000 : ℝ)
  | 19 => (-25455475791 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch066Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-20111165261 / 500000000000 : ℝ)
  | 1 => (-10176468703 / 250000000000 : ℝ)
  | 2 => (-41194487479 / 1000000000000 : ℝ)
  | 3 => (-5211026867 / 125000000000 : ℝ)
  | 4 => (-21093551983 / 500000000000 : ℝ)
  | 5 => (-21345600861 / 500000000000 : ℝ)
  | 6 => (-43200555737 / 1000000000000 : ℝ)
  | 7 => (-43715213917 / 1000000000000 : ℝ)
  | 8 => (-44235224553 / 1000000000000 : ℝ)
  | 9 => (-8952127263 / 200000000000 : ℝ)
  | 10 => (-45291498261 / 1000000000000 : ℝ)
  | 11 => (-45827859837 / 1000000000000 : ℝ)
  | 12 => (-72452767 / 1562500000 : ℝ)
  | 13 => (-2345864081 / 50000000000 : ℝ)
  | 14 => (-47470442683 / 1000000000000 : ℝ)
  | 15 => (-9605861019 / 200000000000 : ℝ)
  | 16 => (-9718784057 / 200000000000 : ℝ)
  | 17 => (-12291085021 / 250000000000 : ℝ)
  | 18 => (-49740616731 / 1000000000000 : ℝ)
  | 19 => (-12580700719 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch066Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1320 : ℝ) + (j.val : ℝ)) / 1600)
      (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch066Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch066Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1320 : ℝ) + (j.val : ℝ)) / 1600)
    (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch066Neg100WeightLower j.val) (hpThetaShiftThreeBatch066Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch066Neg100WeightLower, hpThetaShiftThreeBatch066Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch066Neg100_integral_bounds :
    (-111882457 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-10770421 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch066Lower hpThetaJensenCellsBatch066Upper
    hpThetaShiftThreeBatch066Neg100WeightLower hpThetaShiftThreeBatch066Neg100WeightUpper hpThetaJensenCellsBatch066_bounds hpThetaShiftThreeBatch066Neg100_weight_bounds
  have hl : (-111882457 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch066Lower j * hpThetaShiftThreeBatch066Neg100WeightLower j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftThreeBatch066Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftThreeBatch066Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch066Lower j * hpThetaShiftThreeBatch066Neg100WeightUpper j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftThreeBatch066Neg100WeightUpper j) / 1600) ≤ (-10770421 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftThreeBatch066Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1320 : ℝ) / 1600 = 66 / 80 by norm_num,
    show ((1320 : ℝ) + 20) / 1600 = (66 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch066Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2264595423 / 500000000000 : ℝ)
  | 1 => (-4609441499 / 1000000000000 : ℝ)
  | 2 => (-293171667 / 62500000000 : ℝ)
  | 3 => (-238655879 / 50000000000 : ℝ)
  | 4 => (-242828277 / 50000000000 : ℝ)
  | 5 => (-4941101967 / 1000000000000 : ℝ)
  | 6 => (-5026738379 / 1000000000000 : ℝ)
  | 7 => (-5113486393 / 1000000000000 : ℝ)
  | 8 => (-5201357731 / 1000000000000 : ℝ)
  | 9 => (-5290364217 / 1000000000000 : ℝ)
  | 10 => (-2690258889 / 500000000000 : ℝ)
  | 11 => (-5471830447 / 1000000000000 : ℝ)
  | 12 => (-5564314363 / 1000000000000 : ℝ)
  | 13 => (-5657981769 / 1000000000000 : ℝ)
  | 14 => (-2876422509 / 500000000000 : ℝ)
  | 15 => (-5848916569 / 1000000000000 : ℝ)
  | 16 => (-5946208989 / 1000000000000 : ℝ)
  | 17 => (-1208946991 / 200000000000 : ℝ)
  | 18 => (-768063407 / 125000000000 : ℝ)
  | 19 => (-6245538789 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch066Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4449983593 / 1000000000000 : ℝ)
  | 1 => (-905838169 / 200000000000 : ℝ)
  | 2 => (-2304720749 / 500000000000 : ℝ)
  | 3 => (-4690746671 / 1000000000000 : ℝ)
  | 4 => (-4773117579 / 1000000000000 : ℝ)
  | 5 => (-4856565539 / 1000000000000 : ℝ)
  | 6 => (-2470550983 / 500000000000 : ℝ)
  | 7 => (-2513369189 / 500000000000 : ℝ)
  | 8 => (-639185799 / 125000000000 : ℝ)
  | 9 => (-520135773 / 100000000000 : ℝ)
  | 10 => (-661295527 / 125000000000 : ℝ)
  | 11 => (-5380517777 / 1000000000000 : ℝ)
  | 12 => (-2735915223 / 500000000000 : ℝ)
  | 13 => (-2782157181 / 500000000000 : ℝ)
  | 14 => (-707247721 / 125000000000 : ℝ)
  | 15 => (-5752845017 / 1000000000000 : ℝ)
  | 16 => (-731114571 / 125000000000 : ℝ)
  | 17 => (-1486552247 / 250000000000 : ℝ)
  | 18 => (-3022367477 / 500000000000 : ℝ)
  | 19 => (-1228901451 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch066Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1320 : ℝ) + (j.val : ℝ)) / 1600)
      (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch066Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch066Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1320 : ℝ) + (j.val : ℝ)) / 1600)
    (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch066Neg70WeightLower j.val) (hpThetaShiftThreeBatch066Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch066Neg70WeightLower, hpThetaShiftThreeBatch066Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch066Neg70_integral_bounds :
    (-6541649 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-501191 / 40000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch066Lower hpThetaJensenCellsBatch066Upper
    hpThetaShiftThreeBatch066Neg70WeightLower hpThetaShiftThreeBatch066Neg70WeightUpper hpThetaJensenCellsBatch066_bounds hpThetaShiftThreeBatch066Neg70_weight_bounds
  have hl : (-6541649 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch066Lower j * hpThetaShiftThreeBatch066Neg70WeightLower j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftThreeBatch066Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftThreeBatch066Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch066Lower j * hpThetaShiftThreeBatch066Neg70WeightUpper j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftThreeBatch066Neg70WeightUpper j) / 1600) ≤ (-501191 / 40000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftThreeBatch066Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1320 : ℝ) / 1600 = 66 / 80 by norm_num,
    show ((1320 : ℝ) + 20) / 1600 = (66 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch066Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (554387971 / 500000000000 : ℝ)
  | 1 => (1114697593 / 1000000000000 : ℝ)
  | 2 => (1120593287 / 1000000000000 : ℝ)
  | 3 => (112646199 / 100000000000 : ℝ)
  | 4 => (17692229 / 15625000000 : ℝ)
  | 5 => (569057113 / 500000000000 : ℝ)
  | 6 => (1143895623 / 1000000000000 : ℝ)
  | 7 => (574822879 / 500000000000 : ℝ)
  | 8 => (144420441 / 125000000000 : ℝ)
  | 9 => (580523907 / 500000000000 : ℝ)
  | 10 => (583348741 / 500000000000 : ℝ)
  | 11 => (1172311383 / 1000000000000 : ℝ)
  | 12 => (1177888353 / 1000000000000 : ℝ)
  | 13 => (236685443 / 200000000000 : ℝ)
  | 14 => (297231693 / 250000000000 : ℝ)
  | 15 => (238877163 / 200000000000 : ℝ)
  | 16 => (599901559 / 500000000000 : ℝ)
  | 17 => (7532359 / 6250000000 : ℝ)
  | 18 => (1210507523 / 1000000000000 : ℝ)
  | 19 => (303948023 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch066Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (557348797 / 500000000000 : ℝ)
  | 1 => (140074161 / 125000000000 : ℝ)
  | 2 => (1126461991 / 1000000000000 : ℝ)
  | 3 => (1132302657 / 1000000000000 : ℝ)
  | 4 => (1138114227 / 1000000000000 : ℝ)
  | 5 => (142986953 / 125000000000 : ℝ)
  | 6 => (1149645759 / 1000000000000 : ℝ)
  | 7 => (1155363529 / 1000000000000 : ℝ)
  | 8 => (232209563 / 200000000000 : ℝ)
  | 9 => (1166697483 / 1000000000000 : ℝ)
  | 10 => (146538923 / 125000000000 : ℝ)
  | 11 => (588944177 / 500000000000 : ℝ)
  | 12 => (73964201 / 62500000000 : ℝ)
  | 13 => (1188926773 / 1000000000000 : ℝ)
  | 14 => (149298227 / 125000000000 : ℝ)
  | 15 => (1199803119 / 1000000000000 : ℝ)
  | 16 => (1205177441 / 1000000000000 : ℝ)
  | 17 => (302626881 / 250000000000 : ℝ)
  | 18 => (1215792093 / 1000000000000 : ℝ)
  | 19 => (61051493 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch066Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1320 : ℝ) + (j.val : ℝ)) / 1600)
      (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch066Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch066Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1320 : ℝ) + (j.val : ℝ)) / 1600)
    (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch066Neg45WeightLower j.val) (hpThetaShiftThreeBatch066Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch066Neg45WeightLower, hpThetaShiftThreeBatch066Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch066Neg45_integral_bounds :
    (2788469 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (179787 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch066Lower hpThetaJensenCellsBatch066Upper
    hpThetaShiftThreeBatch066Neg45WeightLower hpThetaShiftThreeBatch066Neg45WeightUpper hpThetaJensenCellsBatch066_bounds hpThetaShiftThreeBatch066Neg45_weight_bounds
  have hl : (2788469 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch066Lower j * hpThetaShiftThreeBatch066Neg45WeightLower j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftThreeBatch066Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftThreeBatch066Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch066Lower j * hpThetaShiftThreeBatch066Neg45WeightUpper j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftThreeBatch066Neg45WeightUpper j) / 1600) ≤ (179787 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftThreeBatch066Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1320 : ℝ) / 1600 = 66 / 80 by norm_num,
    show ((1320 : ℝ) + 20) / 1600 = (66 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch066Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-231300997 / 1000000000000 : ℝ)
  | 1 => (-46004633 / 200000000000 : ℝ)
  | 2 => (-11435843 / 50000000000 : ℝ)
  | 3 => (-227381851 / 1000000000000 : ℝ)
  | 4 => (-113008951 / 500000000000 : ℝ)
  | 5 => (-112312389 / 500000000000 : ℝ)
  | 6 => (-223202241 / 1000000000000 : ℝ)
  | 7 => (-110875027 / 500000000000 : ℝ)
  | 8 => (-220267979 / 1000000000000 : ℝ)
  | 9 => (-3418059 / 15625000000 : ℝ)
  | 10 => (-108606603 / 500000000000 : ℝ)
  | 11 => (-215640027 / 1000000000000 : ℝ)
  | 12 => (-214035997 / 1000000000000 : ℝ)
  | 13 => (-106200437 / 500000000000 : ℝ)
  | 14 => (-210734413 / 1000000000000 : ℝ)
  | 15 => (-209036371 / 1000000000000 : ℝ)
  | 16 => (-207306501 / 1000000000000 : ℝ)
  | 17 => (-205544557 / 1000000000000 : ℝ)
  | 18 => (-203750293 / 1000000000000 : ℝ)
  | 19 => (-10096173 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch066Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-57505791 / 250000000000 : ℝ)
  | 1 => (-228716859 / 1000000000000 : ℝ)
  | 2 => (-4547637 / 20000000000 : ℝ)
  | 3 => (-226017901 / 1000000000000 : ℝ)
  | 4 => (-224624777 / 1000000000000 : ℝ)
  | 5 => (-697507 / 3125000000 : ℝ)
  | 6 => (-221750053 / 1000000000000 : ℝ)
  | 7 => (-110133989 / 500000000000 : ℝ)
  | 8 => (-8750231 / 40000000000 : ℝ)
  | 9 => (-43442641 / 200000000000 : ℝ)
  | 10 => (-107820013 / 500000000000 : ℝ)
  | 11 => (-53508999 / 250000000000 : ℝ)
  | 12 => (-212400873 / 1000000000000 : ℝ)
  | 13 => (-52683603 / 250000000000 : ℝ)
  | 14 => (-20903637 / 100000000000 : ℝ)
  | 15 => (-414613 / 2000000000 : ℝ)
  | 16 => (-51386139 / 250000000000 : ℝ)
  | 17 => (-50937573 / 250000000000 : ℝ)
  | 18 => (-201923459 / 1000000000000 : ℝ)
  | 19 => (-200063809 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch066Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1320 : ℝ) + (j.val : ℝ)) / 1600)
      (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch066Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch066Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1320 : ℝ) + (j.val : ℝ)) / 1600)
    (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch066Neg25WeightLower j.val) (hpThetaShiftThreeBatch066Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch066Neg25WeightLower, hpThetaShiftThreeBatch066Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch066Neg25_integral_bounds :
    (-134741 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-130321 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch066Lower hpThetaJensenCellsBatch066Upper
    hpThetaShiftThreeBatch066Neg25WeightLower hpThetaShiftThreeBatch066Neg25WeightUpper hpThetaJensenCellsBatch066_bounds hpThetaShiftThreeBatch066Neg25_weight_bounds
  have hl : (-134741 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch066Lower j * hpThetaShiftThreeBatch066Neg25WeightLower j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftThreeBatch066Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftThreeBatch066Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch066Lower j * hpThetaShiftThreeBatch066Neg25WeightUpper j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftThreeBatch066Neg25WeightUpper j) / 1600) ≤ (-130321 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftThreeBatch066Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1320 : ℝ) / 1600 = 66 / 80 by norm_num,
    show ((1320 : ℝ) + 20) / 1600 = (66 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch066Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch066Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch066Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch066Neg25_integral_bounds
end HodgeProofHP
