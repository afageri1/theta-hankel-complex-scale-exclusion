/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch013

/-! Exact signed weight and batch integral certificates, batch 13 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch013Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (14911827 / 1000000000000 : ℝ)
  | 1 => (-27869991 / 500000000000 : ℝ)
  | 2 => (-31822007 / 250000000000 : ℝ)
  | 3 => (-49932451 / 250000000000 : ℝ)
  | 4 => (-136531317 / 500000000000 : ℝ)
  | 5 => (-173641837 / 500000000000 : ℝ)
  | 6 => (-105597477 / 250000000000 : ℝ)
  | 7 => (-9967563 / 20000000000 : ℝ)
  | 8 => (-575245041 / 1000000000000 : ℝ)
  | 9 => (-652987049 / 1000000000000 : ℝ)
  | 10 => (-146320093 / 200000000000 : ℝ)
  | 11 => (-12673147 / 15625000000 : ℝ)
  | 12 => (-111428227 / 125000000000 : ℝ)
  | 13 => (-243157363 / 250000000000 : ℝ)
  | 14 => (-10546879 / 10000000000 : ℝ)
  | 15 => (-568798281 / 500000000000 : ℝ)
  | 16 => (-1221350661 / 1000000000000 : ℝ)
  | 17 => (-1305945237 / 1000000000000 : ℝ)
  | 18 => (-347843787 / 250000000000 : ℝ)
  | 19 => (-738817533 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch013Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (4233253 / 50000000000 : ℝ)
  | 1 => (3727957 / 250000000000 : ℝ)
  | 2 => (-55739981 / 1000000000000 : ℝ)
  | 3 => (-127288027 / 1000000000000 : ℝ)
  | 4 => (-199729803 / 1000000000000 : ℝ)
  | 5 => (-273062633 / 1000000000000 : ℝ)
  | 6 => (-347283673 / 1000000000000 : ℝ)
  | 7 => (-422389907 / 1000000000000 : ℝ)
  | 8 => (-498378149 / 1000000000000 : ℝ)
  | 9 => (-7190563 / 12500000000 : ℝ)
  | 10 => (-81623381 / 125000000000 : ℝ)
  | 11 => (-45725029 / 62500000000 : ℝ)
  | 12 => (-811081407 / 1000000000000 : ℝ)
  | 13 => (-178285163 / 200000000000 : ℝ)
  | 14 => (-972629451 / 1000000000000 : ℝ)
  | 15 => (-1054687899 / 1000000000000 : ℝ)
  | 16 => (-1137596561 / 1000000000000 : ℝ)
  | 17 => (-61067533 / 50000000000 : ℝ)
  | 18 => (-326486309 / 250000000000 : ℝ)
  | 19 => (-1391375147 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch013Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((260 : ℝ) + (j.val : ℝ)) / 1600)
      (((260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch013Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch013Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((260 : ℝ) + (j.val : ℝ)) / 1600)
    (((260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch013Neg100WeightLower j.val) (hpThetaShiftOneBatch013Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch013Neg100WeightLower, hpThetaShiftOneBatch013Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch013Neg100_integral_bounds :
    (-2404806161 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-2112232921 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch013Lower hpThetaJensenCellsBatch013Upper
    hpThetaShiftOneBatch013Neg100WeightLower hpThetaShiftOneBatch013Neg100WeightUpper hpThetaJensenCellsBatch013_bounds hpThetaShiftOneBatch013Neg100_weight_bounds
  have hl : (-2404806161 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch013Lower j * hpThetaShiftOneBatch013Neg100WeightLower j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftOneBatch013Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftOneBatch013Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch013Lower j * hpThetaShiftOneBatch013Neg100WeightUpper j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftOneBatch013Neg100WeightUpper j) / 1600) ≤ (-2112232921 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftOneBatch013Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (260 : ℝ) / 1600 = 13 / 80 by norm_num,
    show ((260 : ℝ) + 20) / 1600 = (13 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch013Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (741359759 / 200000000000 : ℝ)
  | 1 => (1837617449 / 500000000000 : ℝ)
  | 2 => (1821420091 / 500000000000 : ℝ)
  | 3 => (1804805547 / 500000000000 : ℝ)
  | 4 => (1787772077 / 500000000000 : ℝ)
  | 5 => (442579493 / 125000000000 : ℝ)
  | 6 => (1752441559 / 500000000000 : ℝ)
  | 7 => (867070599 / 250000000000 : ℝ)
  | 8 => (3430830569 / 1000000000000 : ℝ)
  | 9 => (3392524499 / 1000000000000 : ℝ)
  | 10 => (3353361117 / 1000000000000 : ℝ)
  | 11 => (828334357 / 250000000000 : ℝ)
  | 12 => (818112627 / 250000000000 : ℝ)
  | 13 => (1615348753 / 500000000000 : ℝ)
  | 14 => (637615129 / 200000000000 : ℝ)
  | 15 => (196536389 / 62500000000 : ℝ)
  | 16 => (387526827 / 125000000000 : ℝ)
  | 17 => (305497027 / 100000000000 : ℝ)
  | 18 => (3008846713 / 1000000000000 : ℝ)
  | 19 => (2961841547 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch013Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3737535487 / 1000000000000 : ℝ)
  | 1 => (926699699 / 250000000000 : ℝ)
  | 2 => (3675234899 / 1000000000000 : ℝ)
  | 3 => (3642840183 / 1000000000000 : ℝ)
  | 4 => (721922219 / 200000000000 : ℝ)
  | 5 => (715108831 / 200000000000 : ℝ)
  | 6 => (708127189 / 200000000000 : ℝ)
  | 7 => (3504883119 / 1000000000000 : ℝ)
  | 8 => (3468282397 / 1000000000000 : ℝ)
  | 9 => (343083057 / 100000000000 : ℝ)
  | 10 => (6785049 / 2000000000 : ℝ)
  | 11 => (1676680559 / 500000000000 : ℝ)
  | 12 => (3313337429 / 1000000000000 : ℝ)
  | 13 => (3272450509 / 1000000000000 : ℝ)
  | 14 => (3230697507 / 1000000000000 : ℝ)
  | 15 => (1594037823 / 500000000000 : ℝ)
  | 16 => (125783289 / 40000000000 : ℝ)
  | 17 => (3100214617 / 1000000000000 : ℝ)
  | 18 => (3054970271 / 1000000000000 : ℝ)
  | 19 => (1504423357 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch013Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((260 : ℝ) + (j.val : ℝ)) / 1600)
      (((260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch013Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch013Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((260 : ℝ) + (j.val : ℝ)) / 1600)
    (((260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch013Neg65WeightLower j.val) (hpThetaShiftOneBatch013Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch013Neg65WeightLower, hpThetaShiftOneBatch013Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch013Neg65_integral_bounds :
    (56968906873 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (29148550071 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch013Lower hpThetaJensenCellsBatch013Upper
    hpThetaShiftOneBatch013Neg65WeightLower hpThetaShiftOneBatch013Neg65WeightUpper hpThetaJensenCellsBatch013_bounds hpThetaShiftOneBatch013Neg65_weight_bounds
  have hl : (56968906873 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch013Lower j * hpThetaShiftOneBatch013Neg65WeightLower j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftOneBatch013Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftOneBatch013Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch013Lower j * hpThetaShiftOneBatch013Neg65WeightUpper j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftOneBatch013Neg65WeightUpper j) / 1600) ≤ (29148550071 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftOneBatch013Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (260 : ℝ) / 1600 = 13 / 80 by norm_num,
    show ((260 : ℝ) + 20) / 1600 = (13 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch013Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (6948214797 / 1000000000000 : ℝ)
  | 1 => (1391731959 / 200000000000 : ℝ)
  | 2 => (6968564297 / 1000000000000 : ℝ)
  | 3 => (6977923479 / 1000000000000 : ℝ)
  | 4 => (698673253 / 100000000000 : ℝ)
  | 5 => (3497493329 / 500000000000 : ℝ)
  | 6 => (1400536217 / 200000000000 : ℝ)
  | 7 => (876226381 / 125000000000 : ℝ)
  | 8 => (7016371803 / 1000000000000 : ℝ)
  | 9 => (3511179311 / 500000000000 : ℝ)
  | 10 => (3513883397 / 500000000000 : ℝ)
  | 11 => (7032591627 / 1000000000000 : ℝ)
  | 12 => (1407365689 / 200000000000 : ℝ)
  | 13 => (7040472593 / 1000000000000 : ℝ)
  | 14 => (880439929 / 125000000000 : ℝ)
  | 15 => (7045964343 / 1000000000000 : ℝ)
  | 16 => (880975341 / 125000000000 : ℝ)
  | 17 => (7049030007 / 1000000000000 : ℝ)
  | 18 => (7049633029 / 1000000000000 : ℝ)
  | 19 => (1409799943 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch013Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1739664949 / 250000000000 : ℝ)
  | 1 => (3484282149 / 500000000000 : ℝ)
  | 2 => (174448087 / 25000000000 : ℝ)
  | 3 => (6986732531 / 1000000000000 : ℝ)
  | 4 => (6994986659 / 1000000000000 : ℝ)
  | 5 => (3501340543 / 500000000000 : ℝ)
  | 6 => (7009811049 / 1000000000000 : ℝ)
  | 7 => (1754092951 / 250000000000 : ℝ)
  | 8 => (7022358623 / 1000000000000 : ℝ)
  | 9 => (1405553359 / 200000000000 : ℝ)
  | 10 => (1758147907 / 250000000000 : ℝ)
  | 11 => (3518414223 / 500000000000 : ℝ)
  | 12 => (3520236297 / 500000000000 : ℝ)
  | 13 => (7043519433 / 1000000000000 : ℝ)
  | 14 => (880745543 / 125000000000 : ℝ)
  | 15 => (7047802729 / 1000000000000 : ℝ)
  | 16 => (881128751 / 125000000000 : ℝ)
  | 17 => (7049641621 / 1000000000000 : ℝ)
  | 18 => (7049726249 / 1000000000000 : ℝ)
  | 19 => (704963303 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch013Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((260 : ℝ) + (j.val : ℝ)) / 1600)
      (((260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch013Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch013Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((260 : ℝ) + (j.val : ℝ)) / 1600)
    (((260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch013Neg40WeightLower j.val) (hpThetaShiftOneBatch013Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch013Neg40WeightLower, hpThetaShiftOneBatch013Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch013Neg40_integral_bounds :
    (59444861799 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (30091098529 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch013Lower hpThetaJensenCellsBatch013Upper
    hpThetaShiftOneBatch013Neg40WeightLower hpThetaShiftOneBatch013Neg40WeightUpper hpThetaJensenCellsBatch013_bounds hpThetaShiftOneBatch013Neg40_weight_bounds
  have hl : (59444861799 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch013Lower j * hpThetaShiftOneBatch013Neg40WeightLower j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftOneBatch013Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftOneBatch013Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch013Lower j * hpThetaShiftOneBatch013Neg40WeightUpper j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftOneBatch013Neg40WeightUpper j) / 1600) ≤ (30091098529 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftOneBatch013Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (260 : ℝ) / 1600 = 13 / 80 by norm_num,
    show ((260 : ℝ) + 20) / 1600 = (13 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch013Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (9898487653 / 1000000000000 : ℝ)
  | 1 => (19901031 / 2000000000 : ℝ)
  | 2 => (250059783 / 25000000000 : ℝ)
  | 3 => (10054111559 / 1000000000000 : ℝ)
  | 4 => (10105672657 / 1000000000000 : ℝ)
  | 5 => (2539267763 / 250000000000 : ℝ)
  | 6 => (408332127 / 40000000000 : ℝ)
  | 7 => (2051873091 / 200000000000 : ℝ)
  | 8 => (5155127157 / 500000000000 : ℝ)
  | 9 => (414438647 / 40000000000 : ℝ)
  | 10 => (10411497451 / 1000000000000 : ℝ)
  | 11 => (10461844557 / 1000000000000 : ℝ)
  | 12 => (105120039 / 10000000000 : ℝ)
  | 13 => (5280985943 / 500000000000 : ℝ)
  | 14 => (10611744917 / 1000000000000 : ℝ)
  | 15 => (1066131939 / 100000000000 : ℝ)
  | 16 => (5355345851 / 500000000000 : ℝ)
  | 17 => (10759858243 / 1000000000000 : ℝ)
  | 18 => (2702203851 / 250000000000 : ℝ)
  | 19 => (10857559569 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch013Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (9950515501 / 1000000000000 : ℝ)
  | 1 => (10002391321 / 1000000000000 : ℝ)
  | 2 => (251352789 / 25000000000 : ℝ)
  | 3 => (5052836329 / 500000000000 : ℝ)
  | 4 => (10157071053 / 1000000000000 : ℝ)
  | 5 => (1276037897 / 125000000000 : ℝ)
  | 6 => (641210341 / 62500000000 : ℝ)
  | 7 => (2062050863 / 200000000000 : ℝ)
  | 8 => (323780193 / 31250000000 : ℝ)
  | 9 => (2602874363 / 250000000000 : ℝ)
  | 10 => (5230922279 / 500000000000 : ℝ)
  | 11 => (10512003901 / 1000000000000 : ℝ)
  | 12 => (10561971887 / 1000000000000 : ℝ)
  | 13 => (5305872459 / 500000000000 : ℝ)
  | 14 => (10661319391 / 1000000000000 : ℝ)
  | 15 => (10710691703 / 1000000000000 : ℝ)
  | 16 => (2689964561 / 250000000000 : ℝ)
  | 17 => (2161763081 / 200000000000 : ℝ)
  | 18 => (1085755957 / 100000000000 : ℝ)
  | 19 => (10906087123 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch013Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((260 : ℝ) + (j.val : ℝ)) / 1600)
      (((260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch013Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch013Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((260 : ℝ) + (j.val : ℝ)) / 1600)
    (((260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch013Neg20WeightLower j.val) (hpThetaShiftOneBatch013Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch013Neg20WeightLower, hpThetaShiftOneBatch013Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch013Neg20_integral_bounds :
    (10994612789 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (279420893 / 1562500000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch013Lower hpThetaJensenCellsBatch013Upper
    hpThetaShiftOneBatch013Neg20WeightLower hpThetaShiftOneBatch013Neg20WeightUpper hpThetaJensenCellsBatch013_bounds hpThetaShiftOneBatch013Neg20_weight_bounds
  have hl : (10994612789 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch013Lower j * hpThetaShiftOneBatch013Neg20WeightLower j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftOneBatch013Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftOneBatch013Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch013Lower j * hpThetaShiftOneBatch013Neg20WeightUpper j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftOneBatch013Neg20WeightUpper j) / 1600) ≤ (279420893 / 1562500000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftOneBatch013Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (260 : ℝ) / 1600 = 13 / 80 by norm_num,
    show ((260 : ℝ) + 20) / 1600 = (13 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch013Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch013Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch013Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch013Neg20_integral_bounds
end HodgeProofHP
