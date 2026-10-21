/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch011

/-! Exact signed weight and batch integral certificates, batch 11 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch011Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (419349539 / 200000000000 : ℝ)
  | 1 => (2062218509 / 1000000000000 : ℝ)
  | 2 => (2026816819 / 1000000000000 : ℝ)
  | 3 => (1990539413 / 1000000000000 : ℝ)
  | 4 => (976691597 / 500000000000 : ℝ)
  | 5 => (1915345187 / 1000000000000 : ℝ)
  | 6 => (375284507 / 200000000000 : ℝ)
  | 7 => (229576563 / 125000000000 : ℝ)
  | 8 => (897956241 / 500000000000 : ℝ)
  | 9 => (109644999 / 62500000000 : ℝ)
  | 10 => (1711832647 / 1000000000000 : ℝ)
  | 11 => (1668448237 / 1000000000000 : ℝ)
  | 12 => (1624164649 / 1000000000000 : ℝ)
  | 13 => (1578979907 / 1000000000000 : ℝ)
  | 14 => (306578433 / 200000000000 : ℝ)
  | 15 => (23217183 / 15625000000 : ℝ)
  | 16 => (179750121 / 125000000000 : ℝ)
  | 17 => (138919449 / 100000000000 : ℝ)
  | 18 => (1339478969 / 1000000000000 : ℝ)
  | 19 => (322213309 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch011Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (532601927 / 250000000000 : ℝ)
  | 1 => (131046731 / 62500000000 : ℝ)
  | 2 => (206221851 / 100000000000 : ℝ)
  | 3 => (101340841 / 50000000000 : ℝ)
  | 4 => (995269707 / 500000000000 : ℝ)
  | 5 => (390676639 / 200000000000 : ℝ)
  | 6 => (478836297 / 250000000000 : ℝ)
  | 7 => (234552817 / 125000000000 : ℝ)
  | 8 => (367322501 / 200000000000 : ℝ)
  | 9 => (1795912483 / 1000000000000 : ℝ)
  | 10 => (350863997 / 200000000000 : ℝ)
  | 11 => (213979081 / 125000000000 : ℝ)
  | 12 => (834224119 / 500000000000 : ℝ)
  | 13 => (32483293 / 20000000000 : ℝ)
  | 14 => (394744977 / 250000000000 : ℝ)
  | 15 => (766446083 / 500000000000 : ℝ)
  | 16 => (1485899713 / 1000000000000 : ℝ)
  | 17 => (1438000969 / 1000000000000 : ℝ)
  | 18 => (1389194491 / 1000000000000 : ℝ)
  | 19 => (133947897 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch011Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((220 : ℝ) + (j.val : ℝ)) / 1600)
      (((220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch011Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch011Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((220 : ℝ) + (j.val : ℝ)) / 1600)
    (((220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch011Neg100WeightLower j.val) (hpThetaShiftOneBatch011Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch011Neg100WeightLower, hpThetaShiftOneBatch011Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch011Neg100_integral_bounds :
    (15724332713 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (32585243889 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch011Lower hpThetaJensenCellsBatch011Upper
    hpThetaShiftOneBatch011Neg100WeightLower hpThetaShiftOneBatch011Neg100WeightUpper hpThetaJensenCellsBatch011_bounds hpThetaShiftOneBatch011Neg100_weight_bounds
  have hl : (15724332713 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch011Lower j * hpThetaShiftOneBatch011Neg100WeightLower j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftOneBatch011Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftOneBatch011Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch011Lower j * hpThetaShiftOneBatch011Neg100WeightUpper j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftOneBatch011Neg100WeightUpper j) / 1600) ≤ (32585243889 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftOneBatch011Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (220 : ℝ) / 1600 = 11 / 80 by norm_num,
    show ((220 : ℝ) + 20) / 1600 = (11 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch011Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4336267289 / 1000000000000 : ℝ)
  | 1 => (541793783 / 125000000000 : ℝ)
  | 2 => (108294767 / 25000000000 : ℝ)
  | 3 => (108214573 / 25000000000 : ℝ)
  | 4 => (2162360703 / 500000000000 : ℝ)
  | 5 => (1080050149 / 250000000000 : ℝ)
  | 6 => (4315014989 / 1000000000000 : ℝ)
  | 7 => (4309159123 / 1000000000000 : ℝ)
  | 8 => (172105103 / 40000000000 : ℝ)
  | 9 => (859082993 / 200000000000 : ℝ)
  | 10 => (4287515953 / 1000000000000 : ℝ)
  | 11 => (2139462621 / 500000000000 : ℝ)
  | 12 => (2134818789 / 500000000000 : ℝ)
  | 13 => (2129823877 / 500000000000 : ℝ)
  | 14 => (2124475301 / 500000000000 : ℝ)
  | 15 => (1059385251 / 250000000000 : ℝ)
  | 16 => (4225413887 / 1000000000000 : ℝ)
  | 17 => (16455329 / 3906250000 : ℝ)
  | 18 => (4198987037 / 1000000000000 : ℝ)
  | 19 => (2092338697 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch011Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (271096713 / 62500000000 : ℝ)
  | 1 => (433626729 / 100000000000 : ℝ)
  | 2 => (866870053 / 200000000000 : ℝ)
  | 3 => (4331790681 / 1000000000000 : ℝ)
  | 4 => (4328582921 / 1000000000000 : ℝ)
  | 5 => (4324721407 / 1000000000000 : ℝ)
  | 6 => (4320200597 / 1000000000000 : ℝ)
  | 7 => (431501499 / 100000000000 : ℝ)
  | 8 => (1077289781 / 250000000000 : ℝ)
  | 9 => (537828447 / 125000000000 : ℝ)
  | 10 => (2147707483 / 500000000000 : ℝ)
  | 11 => (2143757977 / 500000000000 : ℝ)
  | 12 => (4278925243 / 1000000000000 : ℝ)
  | 13 => (4269637579 / 1000000000000 : ℝ)
  | 14 => (851929551 / 200000000000 : ℝ)
  | 15 => (4248950603 / 1000000000000 : ℝ)
  | 16 => (847508201 / 200000000000 : ℝ)
  | 17 => (16505523 / 3906250000 : ℝ)
  | 18 => (168502569 / 40000000000 : ℝ)
  | 19 => (2099493519 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch011Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((220 : ℝ) + (j.val : ℝ)) / 1600)
      (((220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch011Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch011Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((220 : ℝ) + (j.val : ℝ)) / 1600)
    (((220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch011Neg65WeightLower j.val) (hpThetaShiftOneBatch011Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch011Neg65WeightLower, hpThetaShiftOneBatch011Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch011Neg65_integral_bounds :
    (78232246241 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (79267932321 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch011Lower hpThetaJensenCellsBatch011Upper
    hpThetaShiftOneBatch011Neg65WeightLower hpThetaShiftOneBatch011Neg65WeightUpper hpThetaJensenCellsBatch011_bounds hpThetaShiftOneBatch011Neg65_weight_bounds
  have hl : (78232246241 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch011Lower j * hpThetaShiftOneBatch011Neg65WeightLower j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftOneBatch011Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftOneBatch011Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch011Lower j * hpThetaShiftOneBatch011Neg65WeightUpper j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftOneBatch011Neg65WeightUpper j) / 1600) ≤ (79267932321 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftOneBatch011Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (220 : ℝ) / 1600 = 11 / 80 by norm_num,
    show ((220 : ℝ) + 20) / 1600 = (11 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch011Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3072056759 / 500000000000 : ℝ)
  | 1 => (6172088417 / 1000000000000 : ℝ)
  | 2 => (1549931117 / 250000000000 : ℝ)
  | 3 => (6227016511 / 1000000000000 : ℝ)
  | 4 => (3126979693 / 500000000000 : ℝ)
  | 5 => (6280547937 / 1000000000000 : ℝ)
  | 6 => (6306777009 / 1000000000000 : ℝ)
  | 7 => (1583160363 / 250000000000 : ℝ)
  | 8 => (6358136117 / 1000000000000 : ℝ)
  | 9 => (6383255861 / 1000000000000 : ℝ)
  | 10 => (6407995543 / 1000000000000 : ℝ)
  | 11 => (6432350027 / 1000000000000 : ℝ)
  | 12 => (3228157091 / 500000000000 : ℝ)
  | 13 => (3239941441 / 500000000000 : ℝ)
  | 14 => (1300610201 / 200000000000 : ℝ)
  | 15 => (6525813437 / 1000000000000 : ℝ)
  | 16 => (6548165067 / 1000000000000 : ℝ)
  | 17 => (6570100793 / 1000000000000 : ℝ)
  | 18 => (1647903879 / 250000000000 : ℝ)
  | 19 => (6612704149 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch011Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3086044209 / 500000000000 : ℝ)
  | 1 => (6199724469 / 1000000000000 : ℝ)
  | 2 => (97297133 / 15625000000 : ℝ)
  | 3 => (6253959387 / 1000000000000 : ℝ)
  | 4 => (3140273969 / 500000000000 : ℝ)
  | 5 => (630677701 / 100000000000 : ℝ)
  | 6 => (6332641453 / 1000000000000 : ℝ)
  | 7 => (3179068059 / 500000000000 : ℝ)
  | 8 => (3191627931 / 500000000000 : ℝ)
  | 9 => (800999443 / 125000000000 : ℝ)
  | 10 => (1608087507 / 250000000000 : ℝ)
  | 11 => (6456314183 / 1000000000000 : ℝ)
  | 12 => (6479882883 / 1000000000000 : ℝ)
  | 13 => (3251525503 / 500000000000 : ℝ)
  | 14 => (3262906719 / 500000000000 : ℝ)
  | 15 => (1637041267 / 250000000000 : ℝ)
  | 16 => (3285050397 / 500000000000 : ℝ)
  | 17 => (6591615517 / 1000000000000 : ℝ)
  | 18 => (132254083 / 20000000000 : ℝ)
  | 19 => (829170201 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch011Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((220 : ℝ) + (j.val : ℝ)) / 1600)
      (((220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch011Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch011Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((220 : ℝ) + (j.val : ℝ)) / 1600)
    (((220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch011Neg40WeightLower j.val) (hpThetaShiftOneBatch011Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch011Neg40WeightLower, hpThetaShiftOneBatch011Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch011Neg40_integral_bounds :
    (116746344029 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (118534854857 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch011Lower hpThetaJensenCellsBatch011Upper
    hpThetaShiftOneBatch011Neg40WeightLower hpThetaShiftOneBatch011Neg40WeightUpper hpThetaJensenCellsBatch011_bounds hpThetaShiftOneBatch011Neg40_weight_bounds
  have hl : (116746344029 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch011Lower j * hpThetaShiftOneBatch011Neg40WeightLower j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftOneBatch011Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftOneBatch011Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch011Lower j * hpThetaShiftOneBatch011Neg40WeightUpper j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftOneBatch011Neg40WeightUpper j) / 1600) ≤ (118534854857 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftOneBatch011Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (220 : ℝ) / 1600 = 11 / 80 by norm_num,
    show ((220 : ℝ) + 20) / 1600 = (11 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch011Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (309314593 / 40000000000 : ℝ)
  | 1 => (1557624393 / 200000000000 : ℝ)
  | 2 => (1960841127 / 250000000000 : ℝ)
  | 3 => (1974647289 / 250000000000 : ℝ)
  | 4 => (7953792603 / 1000000000000 : ℝ)
  | 5 => (8008971533 / 1000000000000 : ℝ)
  | 6 => (64512981 / 8000000000 : ℝ)
  | 7 => (4059621273 / 500000000000 : ℝ)
  | 8 => (8174327961 / 1000000000000 : ℝ)
  | 9 => (8229375521 / 1000000000000 : ℝ)
  | 10 => (8284381873 / 1000000000000 : ℝ)
  | 11 => (1042417957 / 125000000000 : ℝ)
  | 12 => (8394257501 / 1000000000000 : ℝ)
  | 13 => (8449120031 / 1000000000000 : ℝ)
  | 14 => (8503927863 / 1000000000000 : ℝ)
  | 15 => (8558677607 / 1000000000000 : ℝ)
  | 16 => (1076670733 / 125000000000 : ℝ)
  | 17 => (866798923 / 100000000000 : ℝ)
  | 18 => (2180636073 / 250000000000 : ℝ)
  | 19 => (8777027633 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch011Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3894060983 / 500000000000 : ℝ)
  | 1 => (7843364509 / 1000000000000 : ℝ)
  | 2 => (7898589157 / 1000000000000 : ℝ)
  | 3 => (1988448151 / 250000000000 : ℝ)
  | 4 => (4004485767 / 500000000000 : ℝ)
  | 5 => (4032061313 / 500000000000 : ℝ)
  | 6 => (8119242547 / 1000000000000 : ℝ)
  | 7 => (4087163981 / 500000000000 : ℝ)
  | 8 => (4114687761 / 500000000000 : ℝ)
  | 9 => (4142190937 / 500000000000 : ℝ)
  | 10 => (8339343657 / 1000000000000 : ℝ)
  | 11 => (4197128751 / 500000000000 : ℝ)
  | 12 => (264035001 / 31250000000 : ℝ)
  | 13 => (1062990983 / 125000000000 : ℝ)
  | 14 => (1069834701 / 125000000000 : ℝ)
  | 15 => (1722673173 / 200000000000 : ℝ)
  | 16 => (8667989231 / 1000000000000 : ℝ)
  | 17 => (8722544293 / 1000000000000 : ℝ)
  | 18 => (4388513817 / 500000000000 : ℝ)
  | 19 => (4415717913 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch011Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((220 : ℝ) + (j.val : ℝ)) / 1600)
      (((220 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch011Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch011Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((220 : ℝ) + (j.val : ℝ)) / 1600)
    (((220 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch011Neg20WeightLower j.val) (hpThetaShiftOneBatch011Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch011Neg20WeightLower, hpThetaShiftOneBatch011Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch011Neg20_integral_bounds :
    (75416791581 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (11 / 80 : ℝ) ((11 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (153575037301 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (220 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch011Lower hpThetaJensenCellsBatch011Upper
    hpThetaShiftOneBatch011Neg20WeightLower hpThetaShiftOneBatch011Neg20WeightUpper hpThetaJensenCellsBatch011_bounds hpThetaShiftOneBatch011Neg20_weight_bounds
  have hl : (75416791581 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch011Lower j * hpThetaShiftOneBatch011Neg20WeightLower j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftOneBatch011Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftOneBatch011Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch011Lower j * hpThetaShiftOneBatch011Neg20WeightUpper j)
        (hpThetaJensenCellsBatch011Upper j * hpThetaShiftOneBatch011Neg20WeightUpper j) / 1600) ≤ (153575037301 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch011Lower, hpThetaJensenCellsBatch011Upper,
      hpThetaShiftOneBatch011Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (220 : ℝ) / 1600 = 11 / 80 by norm_num,
    show ((220 : ℝ) + 20) / 1600 = (11 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch011Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch011Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch011Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch011Neg20_integral_bounds
end HodgeProofHP
