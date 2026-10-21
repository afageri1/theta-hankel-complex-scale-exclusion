/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch025

/-! Exact signed weight and batch integral certificates, batch 25 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch025Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-10896399839 / 1000000000000 : ℝ)
  | 1 => (-1067826851 / 100000000000 : ℝ)
  | 2 => (-2091069093 / 200000000000 : ℝ)
  | 3 => (-25568997 / 2500000000 : ℝ)
  | 4 => (-2498749207 / 250000000000 : ℝ)
  | 5 => (-4878754043 / 500000000000 : ℝ)
  | 6 => (-4757550671 / 500000000000 : ℝ)
  | 7 => (-2316936401 / 250000000000 : ℝ)
  | 8 => (-9015410121 / 1000000000000 : ℝ)
  | 9 => (-8758064397 / 1000000000000 : ℝ)
  | 10 => (-8495678191 / 1000000000000 : ℝ)
  | 11 => (-8228221527 / 1000000000000 : ℝ)
  | 12 => (-7955664701 / 1000000000000 : ℝ)
  | 13 => (-479873643 / 62500000000 : ℝ)
  | 14 => (-1479026629 / 200000000000 : ℝ)
  | 15 => (-3553550213 / 500000000000 : ℝ)
  | 16 => (-3406925791 / 500000000000 : ℝ)
  | 17 => (-651535837 / 100000000000 : ℝ)
  | 18 => (-3105796431 / 500000000000 : ℝ)
  | 19 => (-118050549 / 20000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch025Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-10678268509 / 1000000000000 : ℝ)
  | 1 => (-1306918183 / 125000000000 : ℝ)
  | 2 => (-10227598799 / 1000000000000 : ℝ)
  | 3 => (-9994996827 / 1000000000000 : ℝ)
  | 4 => (-1951501617 / 200000000000 : ℝ)
  | 5 => (-9515101341 / 1000000000000 : ℝ)
  | 6 => (-9267745603 / 1000000000000 : ℝ)
  | 7 => (-225385253 / 25000000000 : ℝ)
  | 8 => (-2189516099 / 250000000000 : ℝ)
  | 9 => (-849567819 / 100000000000 : ℝ)
  | 10 => (-4114110763 / 500000000000 : ℝ)
  | 11 => (-79556647 / 10000000000 : ℝ)
  | 12 => (-7677978287 / 1000000000000 : ℝ)
  | 13 => (-924391643 / 125000000000 : ℝ)
  | 14 => (-284284017 / 40000000000 : ℝ)
  | 15 => (-6813851581 / 1000000000000 : ℝ)
  | 16 => (-6515358369 / 1000000000000 : ℝ)
  | 17 => (-6211592861 / 1000000000000 : ℝ)
  | 18 => (-5902527449 / 1000000000000 : ℝ)
  | 19 => (-698516857 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch025Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((500 : ℝ) + (j.val : ℝ)) / 1600)
      (((500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch025Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch025Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((500 : ℝ) + (j.val : ℝ)) / 1600)
    (((500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch025Neg100WeightLower j.val) (hpThetaShiftOneBatch025Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch025Neg100WeightLower, hpThetaShiftOneBatch025Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch025Neg100_integral_bounds :
    (-70285144631 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-33608868051 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch025Lower hpThetaJensenCellsBatch025Upper
    hpThetaShiftOneBatch025Neg100WeightLower hpThetaShiftOneBatch025Neg100WeightUpper hpThetaJensenCellsBatch025_bounds hpThetaShiftOneBatch025Neg100_weight_bounds
  have hl : (-70285144631 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch025Lower j * hpThetaShiftOneBatch025Neg100WeightLower j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftOneBatch025Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftOneBatch025Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch025Lower j * hpThetaShiftOneBatch025Neg100WeightUpper j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftOneBatch025Neg100WeightUpper j) / 1600) ≤ (-33608868051 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftOneBatch025Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (500 : ℝ) / 1600 = 25 / 80 by norm_num,
    show ((500 : ℝ) + 20) / 1600 = (25 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch025Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-11370718513 / 500000000000 : ℝ)
  | 1 => (-5710289431 / 250000000000 : ℝ)
  | 2 => (-458788051 / 20000000000 : ℝ)
  | 3 => (-23036146521 / 1000000000000 : ℝ)
  | 4 => (-5782841137 / 250000000000 : ℝ)
  | 5 => (-23225031439 / 1000000000000 : ℝ)
  | 6 => (-23317121899 / 1000000000000 : ℝ)
  | 7 => (-5851902633 / 250000000000 : ℝ)
  | 8 => (-146852949 / 6250000000 : ℝ)
  | 9 => (-5895920057 / 250000000000 : ℝ)
  | 10 => (-2366921 / 100000000 : ℝ)
  | 11 => (-23753035363 / 1000000000000 : ℝ)
  | 12 => (-23835130429 / 1000000000000 : ℝ)
  | 13 => (-11957734607 / 500000000000 : ℝ)
  | 14 => (-599850641 / 25000000000 : ℝ)
  | 15 => (-4814154707 / 200000000000 : ℝ)
  | 16 => (-24145686637 / 1000000000000 : ℝ)
  | 17 => (-756835581 / 31250000000 : ℝ)
  | 18 => (-24289902957 / 1000000000000 : ℝ)
  | 19 => (-24359153201 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch025Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-22640265333 / 1000000000000 : ℝ)
  | 1 => (-909657481 / 40000000000 : ℝ)
  | 2 => (-22841157723 / 1000000000000 : ℝ)
  | 3 => (-22939402549 / 1000000000000 : ℝ)
  | 4 => (-575903663 / 25000000000 : ℝ)
  | 5 => (-23131364547 / 1000000000000 : ℝ)
  | 6 => (-11612515719 / 500000000000 : ℝ)
  | 7 => (-11658560949 / 500000000000 : ℝ)
  | 8 => (-23407610531 / 1000000000000 : ℝ)
  | 9 => (-23496471839 / 1000000000000 : ℝ)
  | 10 => (-23583680227 / 1000000000000 : ℝ)
  | 11 => (-23669209999 / 1000000000000 : ℝ)
  | 12 => (-11876517681 / 500000000000 : ℝ)
  | 13 => (-5958782607 / 250000000000 : ℝ)
  | 14 => (-23915469213 / 1000000000000 : ℝ)
  | 15 => (-23994025639 / 1000000000000 : ℝ)
  | 16 => (-12035386767 / 500000000000 : ℝ)
  | 17 => (-6036421659 / 250000000000 : ℝ)
  | 18 => (-24218738591 / 1000000000000 : ℝ)
  | 19 => (-6072475739 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch025Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((500 : ℝ) + (j.val : ℝ)) / 1600)
      (((500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch025Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch025Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((500 : ℝ) + (j.val : ℝ)) / 1600)
    (((500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch025Neg65WeightLower j.val) (hpThetaShiftOneBatch025Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch025Neg65WeightLower, hpThetaShiftOneBatch025Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch025Neg65_integral_bounds :
    (-19321442453 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-189965798409 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch025Lower hpThetaJensenCellsBatch025Upper
    hpThetaShiftOneBatch025Neg65WeightLower hpThetaShiftOneBatch025Neg65WeightUpper hpThetaJensenCellsBatch025_bounds hpThetaShiftOneBatch025Neg65_weight_bounds
  have hl : (-19321442453 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch025Lower j * hpThetaShiftOneBatch025Neg65WeightLower j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftOneBatch025Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftOneBatch025Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch025Lower j * hpThetaShiftOneBatch025Neg65WeightUpper j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftOneBatch025Neg65WeightUpper j) / 1600) ≤ (-189965798409 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftOneBatch025Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (500 : ℝ) / 1600 = 25 / 80 by norm_num,
    show ((500 : ℝ) + 20) / 1600 = (25 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch025Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2585483677 / 200000000000 : ℝ)
  | 1 => (-1310417597 / 100000000000 : ℝ)
  | 2 => (-2656281973 / 200000000000 : ℝ)
  | 3 => (-13459111719 / 1000000000000 : ℝ)
  | 4 => (-1704659137 / 125000000000 : ℝ)
  | 5 => (-6907942737 / 500000000000 : ℝ)
  | 6 => (-2798988049 / 200000000000 : ℝ)
  | 7 => (-14174428717 / 1000000000000 : ℝ)
  | 8 => (-448573191 / 31250000000 : ℝ)
  | 9 => (-2906934313 / 200000000000 : ℝ)
  | 10 => (-57482063 / 3906250000 : ℝ)
  | 11 => (-2979308553 / 200000000000 : ℝ)
  | 12 => (-3015613271 / 200000000000 : ℝ)
  | 13 => (-1525996969 / 100000000000 : ℝ)
  | 14 => (-15442243477 / 1000000000000 : ℝ)
  | 15 => (-15624878337 / 1000000000000 : ℝ)
  | 16 => (-3951966201 / 250000000000 : ℝ)
  | 17 => (-15991193327 / 1000000000000 : ℝ)
  | 18 => (-8087427133 / 500000000000 : ℝ)
  | 19 => (-16358837897 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch025Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-12751145377 / 1000000000000 : ℝ)
  | 1 => (-807963649 / 62500000000 : ℝ)
  | 2 => (-13104175969 / 1000000000000 : ℝ)
  | 3 => (-1660176233 / 125000000000 : ℝ)
  | 4 => (-6729555859 / 500000000000 : ℝ)
  | 5 => (-2727454619 / 200000000000 : ℝ)
  | 6 => (-13815885473 / 1000000000000 : ℝ)
  | 7 => (-3498735061 / 250000000000 : ℝ)
  | 8 => (-3543607179 / 250000000000 : ℝ)
  | 9 => (-14354342111 / 1000000000000 : ℝ)
  | 10 => (-3633667891 / 250000000000 : ℝ)
  | 11 => (-14715408127 / 1000000000000 : ℝ)
  | 12 => (-3724135691 / 250000000000 : ℝ)
  | 13 => (-7539033177 / 500000000000 : ℝ)
  | 14 => (-15259969689 / 1000000000000 : ℝ)
  | 15 => (-3860560869 / 250000000000 : ℝ)
  | 16 => (-61034681 / 3906250000 : ℝ)
  | 17 => (-15807864803 / 1000000000000 : ℝ)
  | 18 => (-7995596663 / 500000000000 : ℝ)
  | 19 => (-3234970853 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch025Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((500 : ℝ) + (j.val : ℝ)) / 1600)
      (((500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch025Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch025Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((500 : ℝ) + (j.val : ℝ)) / 1600)
    (((500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch025Neg40WeightLower j.val) (hpThetaShiftOneBatch025Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch025Neg40WeightLower, hpThetaShiftOneBatch025Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch025Neg40_integral_bounds :
    (-11965199133 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-116613638027 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch025Lower hpThetaJensenCellsBatch025Upper
    hpThetaShiftOneBatch025Neg40WeightLower hpThetaShiftOneBatch025Neg40WeightUpper hpThetaJensenCellsBatch025_bounds hpThetaShiftOneBatch025Neg40_weight_bounds
  have hl : (-11965199133 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch025Lower j * hpThetaShiftOneBatch025Neg40WeightLower j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftOneBatch025Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftOneBatch025Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch025Lower j * hpThetaShiftOneBatch025Neg40WeightUpper j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftOneBatch025Neg40WeightUpper j) / 1600) ≤ (-116613638027 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftOneBatch025Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (500 : ℝ) / 1600 = 25 / 80 by norm_num,
    show ((500 : ℝ) + 20) / 1600 = (25 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch025Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (9942775171 / 1000000000000 : ℝ)
  | 1 => (2465032287 / 250000000000 : ℝ)
  | 2 => (9776602797 / 1000000000000 : ℝ)
  | 3 => (9692194801 / 1000000000000 : ℝ)
  | 4 => (1200862983 / 125000000000 : ℝ)
  | 5 => (4760364357 / 500000000000 : ℝ)
  | 6 => (4716834053 / 500000000000 : ℝ)
  | 7 => (4672860409 / 500000000000 : ℝ)
  | 8 => (9256885651 / 1000000000000 : ℝ)
  | 9 => (1145895179 / 125000000000 : ℝ)
  | 10 => (4538273507 / 500000000000 : ℝ)
  | 11 => (4492520637 / 500000000000 : ℝ)
  | 12 => (1111580389 / 125000000000 : ℝ)
  | 13 => (8799351457 / 1000000000000 : ℝ)
  | 14 => (8705165259 / 1000000000000 : ℝ)
  | 15 => (8610083497 / 1000000000000 : ℝ)
  | 16 => (8514105173 / 1000000000000 : ℝ)
  | 17 => (8417229317 / 1000000000000 : ℝ)
  | 18 => (4159727491 / 500000000000 : ℝ)
  | 19 => (8220781249 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch025Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (10024542211 / 1000000000000 : ℝ)
  | 1 => (2485693793 / 250000000000 : ℝ)
  | 2 => (9860129149 / 1000000000000 : ℝ)
  | 3 => (4888301399 / 500000000000 : ℝ)
  | 4 => (4846097401 / 500000000000 : ℝ)
  | 5 => (1921380773 / 200000000000 : ℝ)
  | 6 => (1904145743 / 200000000000 : ℝ)
  | 7 => (9433668107 / 1000000000000 : ℝ)
  | 8 => (9345720819 / 1000000000000 : ℝ)
  | 9 => (2314221413 / 250000000000 : ℝ)
  | 10 => (9167161433 / 1000000000000 : ℝ)
  | 11 => (1815309403 / 200000000000 : ℝ)
  | 12 => (359401651 / 40000000000 : ℝ)
  | 13 => (8892643113 / 1000000000000 : ℝ)
  | 14 => (4399675729 / 500000000000 : ℝ)
  | 15 => (435258263 / 50000000000 : ℝ)
  | 16 => (4305041749 / 500000000000 : ℝ)
  | 17 => (4257052587 / 500000000000 : ℝ)
  | 18 => (4208614659 / 500000000000 : ℝ)
  | 19 => (8319454983 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch025Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((500 : ℝ) + (j.val : ℝ)) / 1600)
      (((500 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch025Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch025Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((500 : ℝ) + (j.val : ℝ)) / 1600)
    (((500 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch025Neg20WeightLower j.val) (hpThetaShiftOneBatch025Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch025Neg20WeightLower, hpThetaShiftOneBatch025Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch025Neg20_integral_bounds :
    (73719937473 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (25 / 80 : ℝ) ((25 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (37722080281 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (500 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch025Lower hpThetaJensenCellsBatch025Upper
    hpThetaShiftOneBatch025Neg20WeightLower hpThetaShiftOneBatch025Neg20WeightUpper hpThetaJensenCellsBatch025_bounds hpThetaShiftOneBatch025Neg20_weight_bounds
  have hl : (73719937473 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch025Lower j * hpThetaShiftOneBatch025Neg20WeightLower j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftOneBatch025Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftOneBatch025Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch025Lower j * hpThetaShiftOneBatch025Neg20WeightUpper j)
        (hpThetaJensenCellsBatch025Upper j * hpThetaShiftOneBatch025Neg20WeightUpper j) / 1600) ≤ (37722080281 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch025Lower, hpThetaJensenCellsBatch025Upper,
      hpThetaShiftOneBatch025Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (500 : ℝ) / 1600 = 25 / 80 by norm_num,
    show ((500 : ℝ) + 20) / 1600 = (25 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch025Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch025Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch025Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch025Neg20_integral_bounds
end HodgeProofHP
