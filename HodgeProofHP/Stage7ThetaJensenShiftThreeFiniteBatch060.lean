/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch060

/-! Exact signed weight and batch integral certificates, batch 60 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch060Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8264252593 / 1000000000000 : ℝ)
  | 1 => (-8388924829 / 1000000000000 : ℝ)
  | 2 => (-212879189 / 25000000000 : ℝ)
  | 3 => (-1728599527 / 200000000000 : ℝ)
  | 4 => (-8772432059 / 1000000000000 : ℝ)
  | 5 => (-890348799 / 100000000000 : ℝ)
  | 6 => (-4518091373 / 500000000000 : ℝ)
  | 7 => (-9170533801 / 1000000000000 : ℝ)
  | 8 => (-1163319849 / 125000000000 : ℝ)
  | 9 => (-1888855103 / 200000000000 : ℝ)
  | 10 => (-9583701927 / 1000000000000 : ℝ)
  | 11 => (-194497123 / 20000000000 : ℝ)
  | 12 => (-9867756473 / 1000000000000 : ℝ)
  | 13 => (-5006210673 / 500000000000 : ℝ)
  | 14 => (-1015886939 / 100000000000 : ℝ)
  | 15 => (-2061423879 / 200000000000 : ℝ)
  | 16 => (-5228595159 / 500000000000 : ℝ)
  | 17 => (-1060910129 / 100000000000 : ℝ)
  | 18 => (-10762871613 / 1000000000000 : ℝ)
  | 19 => (-2729630191 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch060Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2035283539 / 250000000000 : ℝ)
  | 1 => (-516515787 / 62500000000 : ℝ)
  | 2 => (-2097231207 / 250000000000 : ℝ)
  | 3 => (-8515167559 / 1000000000000 : ℝ)
  | 4 => (-4321498817 / 500000000000 : ℝ)
  | 5 => (-4386216029 / 500000000000 : ℝ)
  | 6 => (-8903487989 / 1000000000000 : ℝ)
  | 7 => (-1807236549 / 200000000000 : ℝ)
  | 8 => (-45852669 / 5000000000 : ℝ)
  | 9 => (-9306558791 / 1000000000000 : ℝ)
  | 10 => (-4722137757 / 500000000000 : ℝ)
  | 11 => (-4791850963 / 500000000000 : ℝ)
  | 12 => (-9724856149 / 1000000000000 : ℝ)
  | 13 => (-1233469559 / 125000000000 : ℝ)
  | 14 => (-2002484269 / 200000000000 : ℝ)
  | 15 => (-10158869389 / 1000000000000 : ℝ)
  | 16 => (-5153559697 / 500000000000 : ℝ)
  | 17 => (-10457190317 / 1000000000000 : ℝ)
  | 18 => (-10609101289 / 1000000000000 : ℝ)
  | 19 => (-2690717903 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch060Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1200 : ℝ) + (j.val : ℝ)) / 1600)
      (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch060Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch060Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1200 : ℝ) + (j.val : ℝ)) / 1600)
    (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch060Neg100WeightLower j.val) (hpThetaShiftThreeBatch060Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch060Neg100WeightLower, hpThetaShiftThreeBatch060Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch060Neg100_integral_bounds :
    (-41104829 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-79136953 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch060Lower hpThetaJensenCellsBatch060Upper
    hpThetaShiftThreeBatch060Neg100WeightLower hpThetaShiftThreeBatch060Neg100WeightUpper hpThetaJensenCellsBatch060_bounds hpThetaShiftThreeBatch060Neg100_weight_bounds
  have hl : (-41104829 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch060Lower j * hpThetaShiftThreeBatch060Neg100WeightLower j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftThreeBatch060Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftThreeBatch060Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch060Lower j * hpThetaShiftThreeBatch060Neg100WeightUpper j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftThreeBatch060Neg100WeightUpper j) / 1600) ≤ (-79136953 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftThreeBatch060Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1200 : ℝ) / 1600 = 60 / 80 by norm_num,
    show ((1200 : ℝ) + 20) / 1600 = (60 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch060Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (443381 / 500000000000 : ℝ)
  | 1 => (-10684379 / 1000000000000 : ℝ)
  | 2 => (-22504293 / 1000000000000 : ℝ)
  | 3 => (-34576473 / 1000000000000 : ℝ)
  | 4 => (-46904451 / 1000000000000 : ℝ)
  | 5 => (-11898359 / 200000000000 : ℝ)
  | 6 => (-72342113 / 1000000000000 : ℝ)
  | 7 => (-85459051 / 1000000000000 : ℝ)
  | 8 => (-19769259 / 200000000000 : ℝ)
  | 9 => (-112507571 / 1000000000000 : ℝ)
  | 10 => (-31611661 / 250000000000 : ℝ)
  | 11 => (-3516683 / 25000000000 : ℝ)
  | 12 => (-38793361 / 250000000000 : ℝ)
  | 13 => (-21246113 / 125000000000 : ℝ)
  | 14 => (-46264407 / 250000000000 : ℝ)
  | 15 => (-50110897 / 250000000000 : ℝ)
  | 16 => (-216130793 / 1000000000000 : ℝ)
  | 17 => (-232123301 / 1000000000000 : ℝ)
  | 18 => (-31053151 / 125000000000 : ℝ)
  | 19 => (-132520327 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch060Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (6106293 / 500000000000 : ℝ)
  | 1 => (886763 / 1000000000000 : ℝ)
  | 2 => (-5342189 / 500000000000 : ℝ)
  | 3 => (-5626073 / 250000000000 : ℝ)
  | 4 => (-4322059 / 125000000000 : ℝ)
  | 5 => (-938089 / 20000000000 : ℝ)
  | 6 => (-29745897 / 500000000000 : ℝ)
  | 7 => (-2260691 / 31250000000 : ℝ)
  | 8 => (-1709181 / 20000000000 : ℝ)
  | 9 => (-49423147 / 500000000000 : ℝ)
  | 10 => (-11250757 / 100000000000 : ℝ)
  | 11 => (-126446643 / 1000000000000 : ℝ)
  | 12 => (-140667319 / 1000000000000 : ℝ)
  | 13 => (-155173443 / 1000000000000 : ℝ)
  | 14 => (-169968903 / 1000000000000 : ℝ)
  | 15 => (-185057627 / 1000000000000 : ℝ)
  | 16 => (-200443587 / 1000000000000 : ℝ)
  | 17 => (-27016349 / 125000000000 : ℝ)
  | 18 => (-2321233 / 10000000000 : ℝ)
  | 19 => (-248425207 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch060Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1200 : ℝ) + (j.val : ℝ)) / 1600)
      (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch060Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch060Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1200 : ℝ) + (j.val : ℝ)) / 1600)
    (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch060Neg70WeightLower j.val) (hpThetaShiftThreeBatch060Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch060Neg70WeightLower, hpThetaShiftThreeBatch060Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch060Neg70_integral_bounds :
    (-2034399 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-877071 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch060Lower hpThetaJensenCellsBatch060Upper
    hpThetaShiftThreeBatch060Neg70WeightLower hpThetaShiftThreeBatch060Neg70WeightUpper hpThetaJensenCellsBatch060_bounds hpThetaShiftThreeBatch060Neg70_weight_bounds
  have hl : (-2034399 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch060Lower j * hpThetaShiftThreeBatch060Neg70WeightLower j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftThreeBatch060Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftThreeBatch060Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch060Lower j * hpThetaShiftThreeBatch060Neg70WeightUpper j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftThreeBatch060Neg70WeightUpper j) / 1600) ≤ (-877071 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftThreeBatch060Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1200 : ℝ) / 1600 = 60 / 80 by norm_num,
    show ((1200 : ℝ) + 20) / 1600 = (60 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch060Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (51570413 / 125000000000 : ℝ)
  | 1 => (104311959 / 250000000000 : ℝ)
  | 2 => (421959689 / 1000000000000 : ℝ)
  | 3 => (426698797 / 1000000000000 : ℝ)
  | 4 => (3370821 / 7812500000 : ℝ)
  | 5 => (436258487 / 1000000000000 : ℝ)
  | 6 => (88215783 / 200000000000 : ℝ)
  | 7 => (445926291 / 1000000000000 : ℝ)
  | 8 => (450800527 / 1000000000000 : ℝ)
  | 9 => (455701533 / 1000000000000 : ℝ)
  | 10 => (230314607 / 500000000000 : ℝ)
  | 11 => (465583473 / 1000000000000 : ℝ)
  | 12 => (235282103 / 500000000000 : ℝ)
  | 13 => (237785653 / 500000000000 : ℝ)
  | 14 => (240302331 / 500000000000 : ℝ)
  | 15 => (485664159 / 1000000000000 : ℝ)
  | 16 => (490749677 / 1000000000000 : ℝ)
  | 17 => (123965273 / 250000000000 : ℝ)
  | 18 => (250499137 / 500000000000 : ℝ)
  | 19 => (506161091 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch060Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (417247837 / 1000000000000 : ℝ)
  | 1 => (42195969 / 100000000000 : ℝ)
  | 2 => (213349399 / 500000000000 : ℝ)
  | 3 => (431465089 / 1000000000000 : ℝ)
  | 4 => (54532311 / 125000000000 : ℝ)
  | 5 => (110269729 / 250000000000 : ℝ)
  | 6 => (111481573 / 250000000000 : ℝ)
  | 7 => (28175033 / 62500000000 : ℝ)
  | 8 => (227850767 / 500000000000 : ℝ)
  | 9 => (92125843 / 200000000000 : ℝ)
  | 10 => (232791737 / 500000000000 : ℝ)
  | 11 => (470564207 / 1000000000000 : ℝ)
  | 12 => (475571307 / 1000000000000 : ℝ)
  | 13 => (480604663 / 1000000000000 : ℝ)
  | 14 => (3035401 / 6250000000 : ℝ)
  | 15 => (245374839 / 500000000000 : ℝ)
  | 16 => (495861093 / 1000000000000 : ℝ)
  | 17 => (20039931 / 40000000000 : ℝ)
  | 18 => (126540273 / 250000000000 : ℝ)
  | 19 => (255674703 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch060Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1200 : ℝ) + (j.val : ℝ)) / 1600)
      (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch060Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch060Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1200 : ℝ) + (j.val : ℝ)) / 1600)
    (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch060Neg45WeightLower j.val) (hpThetaShiftThreeBatch060Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch060Neg45WeightLower, hpThetaShiftThreeBatch060Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch060Neg45_integral_bounds :
    (7733961 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (8002673 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch060Lower hpThetaJensenCellsBatch060Upper
    hpThetaShiftThreeBatch060Neg45WeightLower hpThetaShiftThreeBatch060Neg45WeightUpper hpThetaJensenCellsBatch060_bounds hpThetaShiftThreeBatch060Neg45_weight_bounds
  have hl : (7733961 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch060Lower j * hpThetaShiftThreeBatch060Neg45WeightLower j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftThreeBatch060Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftThreeBatch060Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch060Lower j * hpThetaShiftThreeBatch060Neg45WeightUpper j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftThreeBatch060Neg45WeightUpper j) / 1600) ≤ (8002673 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftThreeBatch060Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1200 : ℝ) / 1600 = 60 / 80 by norm_num,
    show ((1200 : ℝ) + 20) / 1600 = (60 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch060Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-239191429 / 1000000000000 : ℝ)
  | 1 => (-119951391 / 500000000000 : ℝ)
  | 2 => (-240606767 / 1000000000000 : ℝ)
  | 3 => (-241303263 / 1000000000000 : ℝ)
  | 4 => (-120996073 / 500000000000 : ℝ)
  | 5 => (-242673291 / 1000000000000 : ℝ)
  | 6 => (-243346573 / 1000000000000 : ℝ)
  | 7 => (-122005933 / 500000000000 : ℝ)
  | 8 => (-122334521 / 500000000000 : ℝ)
  | 9 => (-9812719 / 40000000000 : ℝ)
  | 10 => (-49191707 / 200000000000 : ℝ)
  | 11 => (-1926489 / 7812500000 : ℝ)
  | 12 => (-3862719 / 15625000000 : ℝ)
  | 13 => (-9913147 / 40000000000 : ℝ)
  | 14 => (-124217219 / 500000000000 : ℝ)
  | 15 => (-24903117 / 100000000000 : ℝ)
  | 16 => (-124809369 / 500000000000 : ℝ)
  | 17 => (-125098503 / 500000000000 : ℝ)
  | 18 => (-250765839 / 1000000000000 : ℝ)
  | 19 => (-251325101 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch060Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-23847283 / 100000000000 : ℝ)
  | 1 => (-59797857 / 250000000000 : ℝ)
  | 2 => (-239902781 / 1000000000000 : ℝ)
  | 3 => (-120303383 / 500000000000 : ℝ)
  | 4 => (-120651631 / 500000000000 : ℝ)
  | 5 => (-48398429 / 200000000000 : ℝ)
  | 6 => (-24267329 / 100000000000 : ℝ)
  | 7 => (-60836643 / 250000000000 : ℝ)
  | 8 => (-48802373 / 200000000000 : ℝ)
  | 9 => (-244669041 / 1000000000000 : ℝ)
  | 10 => (-122658987 / 500000000000 : ℝ)
  | 11 => (-122979267 / 500000000000 : ℝ)
  | 12 => (-246590591 / 1000000000000 : ℝ)
  | 13 => (-49442803 / 200000000000 : ℝ)
  | 14 => (-123914337 / 500000000000 : ℝ)
  | 15 => (-248434437 / 1000000000000 : ℝ)
  | 16 => (-249031169 / 1000000000000 : ℝ)
  | 17 => (-249618737 / 1000000000000 : ℝ)
  | 18 => (-50039401 / 200000000000 : ℝ)
  | 19 => (-125382919 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch060Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1200 : ℝ) + (j.val : ℝ)) / 1600)
      (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch060Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch060Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1200 : ℝ) + (j.val : ℝ)) / 1600)
    (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch060Neg25WeightLower j.val) (hpThetaShiftThreeBatch060Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch060Neg25WeightLower, hpThetaShiftThreeBatch060Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch060Neg25_integral_bounds :
    (-4255279 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-829173 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch060Lower hpThetaJensenCellsBatch060Upper
    hpThetaShiftThreeBatch060Neg25WeightLower hpThetaShiftThreeBatch060Neg25WeightUpper hpThetaJensenCellsBatch060_bounds hpThetaShiftThreeBatch060Neg25_weight_bounds
  have hl : (-4255279 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch060Lower j * hpThetaShiftThreeBatch060Neg25WeightLower j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftThreeBatch060Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftThreeBatch060Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch060Lower j * hpThetaShiftThreeBatch060Neg25WeightUpper j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftThreeBatch060Neg25WeightUpper j) / 1600) ≤ (-829173 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftThreeBatch060Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1200 : ℝ) / 1600 = 60 / 80 by norm_num,
    show ((1200 : ℝ) + 20) / 1600 = (60 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch060Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch060Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch060Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch060Neg25_integral_bounds
end HodgeProofHP
