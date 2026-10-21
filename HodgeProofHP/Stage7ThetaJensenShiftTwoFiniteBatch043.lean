/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch043

/-! Exact signed weight and batch integral certificates, batch 43 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch043Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4512062237 / 1000000000000 : ℝ)
  | 1 => (1126400603 / 250000000000 : ℝ)
  | 2 => (4498088331 / 1000000000000 : ℝ)
  | 3 => (2244749287 / 500000000000 : ℝ)
  | 4 => (4479811441 / 1000000000000 : ℝ)
  | 5 => (558625619 / 125000000000 : ℝ)
  | 6 => (1114264211 / 250000000000 : ℝ)
  | 7 => (2221972283 / 500000000000 : ℝ)
  | 8 => (27685283 / 6250000000 : ℝ)
  | 9 => (1103533963 / 250000000000 : ℝ)
  | 10 => (4397392859 / 1000000000000 : ℝ)
  | 11 => (175175703 / 40000000000 : ℝ)
  | 12 => (2180055489 / 500000000000 : ℝ)
  | 13 => (4339523741 / 1000000000000 : ℝ)
  | 14 => (4317606231 / 1000000000000 : ℝ)
  | 15 => (4294333507 / 1000000000000 : ℝ)
  | 16 => (1067420079 / 250000000000 : ℝ)
  | 17 => (4243621091 / 1000000000000 : ℝ)
  | 18 => (2108064973 / 500000000000 : ℝ)
  | 19 => (1046795169 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch043Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (4517488951 / 1000000000000 : ℝ)
  | 1 => (2256031119 / 500000000000 : ℝ)
  | 2 => (4505602413 / 1000000000000 : ℝ)
  | 3 => (1124522083 / 250000000000 : ℝ)
  | 4 => (179579943 / 40000000000 : ℝ)
  | 5 => (2239905721 / 500000000000 : ℝ)
  | 6 => (4469004953 / 1000000000000 : ℝ)
  | 7 => (891411369 / 200000000000 : ℝ)
  | 8 => (4443944567 / 1000000000000 : ℝ)
  | 9 => (4429645281 / 1000000000000 : ℝ)
  | 10 => (4414135853 / 1000000000000 : ℝ)
  | 11 => (219869643 / 50000000000 : ℝ)
  | 12 => (68428009 / 15625000000 : ℝ)
  | 13 => (4360110979 / 1000000000000 : ℝ)
  | 14 => (2169761871 / 500000000000 : ℝ)
  | 15 => (539700779 / 125000000000 : ℝ)
  | 16 => (1073583377 / 250000000000 : ℝ)
  | 17 => (4269680317 / 1000000000000 : ℝ)
  | 18 => (1060905273 / 250000000000 : ℝ)
  | 19 => (4216129947 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch043Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((860 : ℝ) + (j.val : ℝ)) / 1600)
      (((860 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch043Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch043Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((860 : ℝ) + (j.val : ℝ)) / 1600)
    (((860 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch043Neg100WeightLower j.val) (hpThetaShiftTwoBatch043Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch043Neg100WeightLower, hpThetaShiftTwoBatch043Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch043Neg100_integral_bounds :
    (1868674557 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (3816686789 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (860 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch043Lower hpThetaJensenCellsBatch043Upper
    hpThetaShiftTwoBatch043Neg100WeightLower hpThetaShiftTwoBatch043Neg100WeightUpper hpThetaJensenCellsBatch043_bounds hpThetaShiftTwoBatch043Neg100_weight_bounds
  have hl : (1868674557 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch043Lower j * hpThetaShiftTwoBatch043Neg100WeightLower j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftTwoBatch043Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftTwoBatch043Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch043Lower j * hpThetaShiftTwoBatch043Neg100WeightUpper j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftTwoBatch043Neg100WeightUpper j) / 1600) ≤ (3816686789 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftTwoBatch043Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (860 : ℝ) / 1600 = 43 / 80 by norm_num,
    show ((860 : ℝ) + 20) / 1600 = (43 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch043Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (128307327 / 62500000000 : ℝ)
  | 1 => (16315801 / 7812500000 : ℝ)
  | 2 => (1062103319 / 500000000000 : ℝ)
  | 3 => (2160269457 / 1000000000000 : ℝ)
  | 4 => (2196610847 / 1000000000000 : ℝ)
  | 5 => (558307659 / 250000000000 : ℝ)
  | 6 => (2270128617 / 1000000000000 : ℝ)
  | 7 => (2307304549 / 1000000000000 : ℝ)
  | 8 => (468951631 / 200000000000 : ℝ)
  | 9 => (2382489121 / 1000000000000 : ℝ)
  | 10 => (1210248549 / 500000000000 : ℝ)
  | 11 => (24587817 / 10000000000 : ℝ)
  | 12 => (1248671251 / 500000000000 : ℝ)
  | 13 => (634044761 / 250000000000 : ℝ)
  | 14 => (2575290823 / 1000000000000 : ℝ)
  | 15 => (26146773 / 10000000000 : ℝ)
  | 16 => (530867579 / 200000000000 : ℝ)
  | 17 => (269427199 / 100000000000 : ℝ)
  | 18 => (2734478923 / 1000000000000 : ℝ)
  | 19 => (346869749 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch043Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2088422529 / 1000000000000 : ℝ)
  | 1 => (2124206639 / 1000000000000 : ℝ)
  | 2 => (1080134729 / 500000000000 : ℝ)
  | 3 => (68644089 / 31250000000 : ℝ)
  | 4 => (2233230637 / 1000000000000 : ℝ)
  | 5 => (1135064309 / 500000000000 : ℝ)
  | 6 => (46146091 / 20000000000 : ℝ)
  | 7 => (586189539 / 250000000000 : ℝ)
  | 8 => (1191244561 / 500000000000 : ℝ)
  | 9 => (2420497099 / 1000000000000 : ℝ)
  | 10 => (2458781701 / 1000000000000 : ℝ)
  | 11 => (2497342503 / 1000000000000 : ℝ)
  | 12 => (507235809 / 200000000000 : ℝ)
  | 13 => (321911353 / 125000000000 : ℝ)
  | 14 => (2614677301 / 1000000000000 : ℝ)
  | 15 => (331792237 / 125000000000 : ℝ)
  | 16 => (2694271991 / 1000000000000 : ℝ)
  | 17 => (683619731 / 250000000000 : ℝ)
  | 18 => (2774957993 / 1000000000000 : ℝ)
  | 19 => (351963557 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch043Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((860 : ℝ) + (j.val : ℝ)) / 1600)
      (((860 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch043Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch043Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((860 : ℝ) + (j.val : ℝ)) / 1600)
    (((860 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch043Neg65WeightLower j.val) (hpThetaShiftTwoBatch043Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch043Neg65WeightLower, hpThetaShiftTwoBatch043Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch043Neg65_integral_bounds :
    (509773123 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (1053864163 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (860 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch043Lower hpThetaJensenCellsBatch043Upper
    hpThetaShiftTwoBatch043Neg65WeightLower hpThetaShiftTwoBatch043Neg65WeightUpper hpThetaJensenCellsBatch043_bounds hpThetaShiftTwoBatch043Neg65_weight_bounds
  have hl : (509773123 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch043Lower j * hpThetaShiftTwoBatch043Neg65WeightLower j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftTwoBatch043Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftTwoBatch043Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch043Lower j * hpThetaShiftTwoBatch043Neg65WeightUpper j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftTwoBatch043Neg65WeightUpper j) / 1600) ≤ (1053864163 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftTwoBatch043Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (860 : ℝ) / 1600 = 43 / 80 by norm_num,
    show ((860 : ℝ) + 20) / 1600 = (43 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch043Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-52289567 / 50000000000 : ℝ)
  | 1 => (-1038795697 / 1000000000000 : ℝ)
  | 2 => (-1031616591 / 1000000000000 : ℝ)
  | 3 => (-64015777 / 62500000000 : ℝ)
  | 4 => (-508350811 / 500000000000 : ℝ)
  | 5 => (-1008962561 / 1000000000000 : ℝ)
  | 6 => (-1001033647 / 1000000000000 : ℝ)
  | 7 => (-124114159 / 125000000000 : ℝ)
  | 8 => (-61537489 / 62500000000 : ℝ)
  | 9 => (-976091691 / 1000000000000 : ℝ)
  | 10 => (-483693627 / 500000000000 : ℝ)
  | 11 => (-479242447 / 500000000000 : ℝ)
  | 12 => (-189876597 / 200000000000 : ℝ)
  | 13 => (-470039951 / 500000000000 : ℝ)
  | 14 => (-930574013 / 1000000000000 : ℝ)
  | 15 => (-115107961 / 125000000000 : ℝ)
  | 16 => (-910947289 / 1000000000000 : ℝ)
  | 17 => (-450411589 / 500000000000 : ℝ)
  | 18 => (-178097943 / 200000000000 : ℝ)
  | 19 => (-175989051 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch043Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-64924731 / 62500000000 : ℝ)
  | 1 => (-103161659 / 100000000000 : ℝ)
  | 2 => (-1024252431 / 1000000000000 : ℝ)
  | 3 => (-1016701621 / 1000000000000 : ℝ)
  | 4 => (-197063 / 195312500 : ℝ)
  | 5 => (-500516823 / 500000000000 : ℝ)
  | 6 => (-992913271 / 1000000000000 : ℝ)
  | 7 => (-984599823 / 1000000000000 : ℝ)
  | 8 => (-97609169 / 100000000000 : ℝ)
  | 9 => (-967387253 / 1000000000000 : ℝ)
  | 10 => (-958484893 / 1000000000000 : ℝ)
  | 11 => (-118672873 / 125000000000 : ℝ)
  | 12 => (-940079901 / 1000000000000 : ℝ)
  | 13 => (-232643503 / 250000000000 : ℝ)
  | 14 => (-920863687 / 1000000000000 : ℝ)
  | 15 => (-113868411 / 125000000000 : ℝ)
  | 16 => (-900823177 / 1000000000000 : ℝ)
  | 17 => (-445244857 / 500000000000 : ℝ)
  | 18 => (-439972627 / 500000000000 : ℝ)
  | 19 => (-869188151 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch043Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((860 : ℝ) + (j.val : ℝ)) / 1600)
      (((860 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch043Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch043Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((860 : ℝ) + (j.val : ℝ)) / 1600)
    (((860 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch043Neg45WeightLower j.val) (hpThetaShiftTwoBatch043Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch043Neg45WeightLower, hpThetaShiftTwoBatch043Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch043Neg45_integral_bounds :
    (-210267111 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-204787529 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (860 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch043Lower hpThetaJensenCellsBatch043Upper
    hpThetaShiftTwoBatch043Neg45WeightLower hpThetaShiftTwoBatch043Neg45WeightUpper hpThetaJensenCellsBatch043_bounds hpThetaShiftTwoBatch043Neg45_weight_bounds
  have hl : (-210267111 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch043Lower j * hpThetaShiftTwoBatch043Neg45WeightLower j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftTwoBatch043Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftTwoBatch043Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch043Lower j * hpThetaShiftTwoBatch043Neg45WeightUpper j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftTwoBatch043Neg45WeightUpper j) / 1600) ≤ (-204787529 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftTwoBatch043Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (860 : ℝ) / 1600 = 43 / 80 by norm_num,
    show ((860 : ℝ) + 20) / 1600 = (43 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch043Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-139294349 / 100000000000 : ℝ)
  | 1 => (-702779309 / 500000000000 : ℝ)
  | 2 => (-709104671 / 500000000000 : ℝ)
  | 3 => (-715447651 / 500000000000 : ℝ)
  | 4 => (-144361613 / 100000000000 : ℝ)
  | 5 => (-728185729 / 500000000000 : ℝ)
  | 6 => (-1469160909 / 1000000000000 : ℝ)
  | 7 => (-185248013 / 125000000000 : ℝ)
  | 8 => (-1494840657 / 1000000000000 : ℝ)
  | 9 => (-75386509 / 50000000000 : ℝ)
  | 10 => (-380163069 / 250000000000 : ℝ)
  | 11 => (-1533606547 / 1000000000000 : ℝ)
  | 12 => (-386648147 / 250000000000 : ℝ)
  | 13 => (-155960999 / 100000000000 : ℝ)
  | 14 => (-786329169 / 500000000000 : ℝ)
  | 15 => (-1585737213 / 1000000000000 : ℝ)
  | 16 => (-1598846191 / 1000000000000 : ℝ)
  | 17 => (-805992421 / 500000000000 : ℝ)
  | 18 => (-406288183 / 250000000000 : ℝ)
  | 19 => (-819174711 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch043Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-690182157 / 500000000000 : ℝ)
  | 1 => (-1392943489 / 1000000000000 : ℝ)
  | 2 => (-1405558617 / 1000000000000 : ℝ)
  | 3 => (-1418209341 / 1000000000000 : ℝ)
  | 4 => (-1430895301 / 1000000000000 : ℝ)
  | 5 => (-1443616129 / 1000000000000 : ℝ)
  | 6 => (-1456371457 / 1000000000000 : ℝ)
  | 7 => (-367290227 / 250000000000 : ℝ)
  | 8 => (-1481984103 / 1000000000000 : ℝ)
  | 9 => (-93427541 / 62500000000 : ℝ)
  | 10 => (-1507730179 / 1000000000000 : ℝ)
  | 11 => (-60826091 / 40000000000 : ℝ)
  | 12 => (-766803273 / 500000000000 : ℝ)
  | 13 => (-1546592587 / 1000000000000 : ℝ)
  | 14 => (-1559609989 / 1000000000000 : ℝ)
  | 15 => (-1572658337 / 1000000000000 : ℝ)
  | 16 => (-396434303 / 250000000000 : ℝ)
  | 17 => (-159884619 / 100000000000 : ℝ)
  | 18 => (-1611984841 / 1000000000000 : ℝ)
  | 19 => (-1625152731 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch043Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((860 : ℝ) + (j.val : ℝ)) / 1600)
      (((860 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch043Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch043Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((860 : ℝ) + (j.val : ℝ)) / 1600)
    (((860 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch043Neg25WeightLower j.val) (hpThetaShiftTwoBatch043Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch043Neg25WeightLower, hpThetaShiftTwoBatch043Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch043Neg25_integral_bounds :
    (-10471023 / 8000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (43 / 80 : ℝ) ((43 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-19928247 / 15625000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (860 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch043Lower hpThetaJensenCellsBatch043Upper
    hpThetaShiftTwoBatch043Neg25WeightLower hpThetaShiftTwoBatch043Neg25WeightUpper hpThetaJensenCellsBatch043_bounds hpThetaShiftTwoBatch043Neg25_weight_bounds
  have hl : (-10471023 / 8000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch043Lower j * hpThetaShiftTwoBatch043Neg25WeightLower j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftTwoBatch043Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftTwoBatch043Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch043Lower j * hpThetaShiftTwoBatch043Neg25WeightUpper j)
        (hpThetaJensenCellsBatch043Upper j * hpThetaShiftTwoBatch043Neg25WeightUpper j) / 1600) ≤ (-19928247 / 15625000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch043Lower, hpThetaJensenCellsBatch043Upper,
      hpThetaShiftTwoBatch043Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (860 : ℝ) / 1600 = 43 / 80 by norm_num,
    show ((860 : ℝ) + 20) / 1600 = (43 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch043Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch043Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch043Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch043Neg25_integral_bounds
end HodgeProofHP
