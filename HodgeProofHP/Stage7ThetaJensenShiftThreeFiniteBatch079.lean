/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch079

/-! Exact signed weight and batch integral certificates, batch 79 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch079Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-115312829331 / 200000000000 : ℝ)
  | 1 => (-116338639399 / 200000000000 : ℝ)
  | 2 => (-29343157949 / 50000000000 : ℝ)
  | 3 => (-296037161767 / 500000000000 : ℝ)
  | 4 => (-119465396681 / 200000000000 : ℝ)
  | 5 => (-602621433183 / 1000000000000 : ℝ)
  | 6 => (-607957969309 / 1000000000000 : ℝ)
  | 7 => (-306668445041 / 500000000000 : ℝ)
  | 8 => (-61875849567 / 100000000000 : ℝ)
  | 9 => (-624223088123 / 1000000000000 : ℝ)
  | 10 => (-314865485691 / 500000000000 : ℝ)
  | 11 => (-635282451287 / 1000000000000 : ℝ)
  | 12 => (-640877835591 / 1000000000000 : ℝ)
  | 13 => (-646517433967 / 1000000000000 : ℝ)
  | 14 => (-652201558023 / 1000000000000 : ℝ)
  | 15 => (-328965260653 / 500000000000 : ℝ)
  | 16 => (-663704639321 / 1000000000000 : ℝ)
  | 17 => (-669524229533 / 1000000000000 : ℝ)
  | 18 => (-135077922277 / 200000000000 : ℝ)
  | 19 => (-340650553151 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch079Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-571475718861 / 1000000000000 : ℝ)
  | 1 => (-288282073327 / 500000000000 : ℝ)
  | 2 => (-290846598497 / 500000000000 : ℝ)
  | 3 => (-586863158979 / 1000000000000 : ℝ)
  | 4 => (-592074323533 / 1000000000000 : ℝ)
  | 5 => (-149331745851 / 250000000000 : ℝ)
  | 6 => (-301310716591 / 500000000000 : ℝ)
  | 7 => (-151989492327 / 250000000000 : ℝ)
  | 8 => (-613336890081 / 1000000000000 : ℝ)
  | 9 => (-618758495669 / 1000000000000 : ℝ)
  | 10 => (-312111544061 / 500000000000 : ℝ)
  | 11 => (-629730971381 / 1000000000000 : ℝ)
  | 12 => (-317641225643 / 500000000000 : ℝ)
  | 13 => (-64087783559 / 100000000000 : ℝ)
  | 14 => (-323258716983 / 500000000000 : ℝ)
  | 15 => (-326100779011 / 500000000000 : ℝ)
  | 16 => (-131586104261 / 200000000000 : ℝ)
  | 17 => (-16592615983 / 25000000000 : ℝ)
  | 18 => (-167381057383 / 250000000000 : ℝ)
  | 19 => (-84423701423 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch079Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1580 : ℝ) + (j.val : ℝ)) / 1600)
      (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch079Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch079Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1580 : ℝ) + (j.val : ℝ)) / 1600)
    (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch079Neg100WeightLower j.val) (hpThetaShiftThreeBatch079Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch079Neg100WeightLower, hpThetaShiftThreeBatch079Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch079Neg100_integral_bounds :
    (-715723 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-5484227 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch079Lower hpThetaJensenCellsBatch079Upper
    hpThetaShiftThreeBatch079Neg100WeightLower hpThetaShiftThreeBatch079Neg100WeightUpper hpThetaJensenCellsBatch079_bounds hpThetaShiftThreeBatch079Neg100_weight_bounds
  have hl : (-715723 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch079Lower j * hpThetaShiftThreeBatch079Neg100WeightLower j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftThreeBatch079Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftThreeBatch079Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch079Lower j * hpThetaShiftThreeBatch079Neg100WeightUpper j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftThreeBatch079Neg100WeightUpper j) / 1600) ≤ (-5484227 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftThreeBatch079Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1580 : ℝ) / 1600 = 79 / 80 by norm_num,
    show ((1580 : ℝ) + 20) / 1600 = (79 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch079Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-121192433867 / 1000000000000 : ℝ)
  | 1 => (-122405274821 / 1000000000000 : ℝ)
  | 2 => (-123628706857 / 1000000000000 : ℝ)
  | 3 => (-124862810819 / 1000000000000 : ℝ)
  | 4 => (-12610766809 / 100000000000 : ℝ)
  | 5 => (-63681680297 / 500000000000 : ℝ)
  | 6 => (-64314985399 / 500000000000 : ℝ)
  | 7 => (-32476895429 / 250000000000 : ℝ)
  | 8 => (-131196276913 / 1000000000000 : ℝ)
  | 9 => (-66248070253 / 500000000000 : ℝ)
  | 10 => (-13380725717 / 100000000000 : ℝ)
  | 11 => (-67564856069 / 500000000000 : ℝ)
  | 12 => (-136463591207 / 1000000000000 : ℝ)
  | 13 => (-6890449037 / 50000000000 : ℝ)
  | 14 => (-139165967669 / 1000000000000 : ℝ)
  | 15 => (-140534639497 / 1000000000000 : ℝ)
  | 16 => (-141915084307 / 1000000000000 : ℝ)
  | 17 => (-35826847689 / 250000000000 : ℝ)
  | 18 => (-18088956011 / 125000000000 : ℝ)
  | 19 => (-9132996633 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch079Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-119990103683 / 1000000000000 : ℝ)
  | 1 => (-60596216933 / 500000000000 : ℝ)
  | 2 => (-6120263741 / 50000000000 : ℝ)
  | 3 => (-15453588357 / 125000000000 : ℝ)
  | 4 => (-62431405409 / 500000000000 : ℝ)
  | 5 => (-126107668089 / 1000000000000 : ℝ)
  | 6 => (-127363360593 / 1000000000000 : ℝ)
  | 7 => (-128629970797 / 1000000000000 : ℝ)
  | 8 => (-25981516343 / 200000000000 : ℝ)
  | 9 => (-8199767307 / 62500000000 : ℝ)
  | 10 => (-26499228101 / 200000000000 : ℝ)
  | 11 => (-133807257169 / 1000000000000 : ℝ)
  | 12 => (-135129712137 / 1000000000000 : ℝ)
  | 13 => (-68231795603 / 500000000000 : ℝ)
  | 14 => (-137808980739 / 1000000000000 : ℝ)
  | 15 => (-34791491917 / 250000000000 : ℝ)
  | 16 => (-17566829937 / 125000000000 : ℝ)
  | 17 => (-70957542153 / 500000000000 : ℝ)
  | 18 => (-28661478151 / 200000000000 : ℝ)
  | 19 => (-144711648087 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch079Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1580 : ℝ) + (j.val : ℝ)) / 1600)
      (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch079Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch079Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1580 : ℝ) + (j.val : ℝ)) / 1600)
    (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch079Neg70WeightLower j.val) (hpThetaShiftThreeBatch079Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch079Neg70WeightLower, hpThetaShiftThreeBatch079Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch079Neg70_integral_bounds :
    (-1215199 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-1162689 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch079Lower hpThetaJensenCellsBatch079Upper
    hpThetaShiftThreeBatch079Neg70WeightLower hpThetaShiftThreeBatch079Neg70WeightUpper hpThetaJensenCellsBatch079_bounds hpThetaShiftThreeBatch079Neg70_weight_bounds
  have hl : (-1215199 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch079Lower j * hpThetaShiftThreeBatch079Neg70WeightLower j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftThreeBatch079Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftThreeBatch079Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch079Lower j * hpThetaShiftThreeBatch079Neg70WeightUpper j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftThreeBatch079Neg70WeightUpper j) / 1600) ≤ (-1162689 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftThreeBatch079Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1580 : ℝ) / 1600 = 79 / 80 by norm_num,
    show ((1580 : ℝ) + 20) / 1600 = (79 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch079Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2841774809 / 500000000000 : ℝ)
  | 1 => (-5797565813 / 1000000000000 : ℝ)
  | 2 => (-2956493393 / 500000000000 : ℝ)
  | 3 => (-6029825827 / 1000000000000 : ℝ)
  | 4 => (-3074048163 / 500000000000 : ℝ)
  | 5 => (-250712471 / 40000000000 : ℝ)
  | 6 => (-6388985771 / 1000000000000 : ℝ)
  | 7 => (-6511632017 / 1000000000000 : ℝ)
  | 8 => (-3317882159 / 500000000000 : ℝ)
  | 9 => (-3380698293 / 500000000000 : ℝ)
  | 10 => (-172213571 / 25000000000 : ℝ)
  | 11 => (-1754304301 / 250000000000 : ℝ)
  | 12 => (-893429239 / 125000000000 : ℝ)
  | 13 => (-909900913 / 125000000000 : ℝ)
  | 14 => (-926568979 / 125000000000 : ℝ)
  | 15 => (-1509496411 / 200000000000 : ℝ)
  | 16 => (-7684012643 / 1000000000000 : ℝ)
  | 17 => (-7822158379 / 1000000000000 : ℝ)
  | 18 => (-1990483539 / 250000000000 : ℝ)
  | 19 => (-8103354979 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch079Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1114185003 / 200000000000 : ℝ)
  | 1 => (-5683549617 / 1000000000000 : ℝ)
  | 2 => (-1449391453 / 250000000000 : ℝ)
  | 3 => (-1182597357 / 200000000000 : ℝ)
  | 4 => (-3014912913 / 500000000000 : ℝ)
  | 5 => (-245923853 / 40000000000 : ℝ)
  | 6 => (-3133905887 / 500000000000 : ℝ)
  | 7 => (-638898577 / 100000000000 : ℝ)
  | 8 => (-406977001 / 62500000000 : ℝ)
  | 9 => (-6635764317 / 1000000000000 : ℝ)
  | 10 => (-1352279317 / 200000000000 : ℝ)
  | 11 => (-6888542839 / 1000000000000 : ℝ)
  | 12 => (-7017217203 / 1000000000000 : ℝ)
  | 13 => (-7147433911 / 1000000000000 : ℝ)
  | 14 => (-7279207303 / 1000000000000 : ℝ)
  | 15 => (-7412551831 / 1000000000000 : ℝ)
  | 16 => (-3773741027 / 500000000000 : ℝ)
  | 17 => (-3842006321 / 500000000000 : ℝ)
  | 18 => (-3911079189 / 500000000000 : ℝ)
  | 19 => (-1592386831 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch079Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1580 : ℝ) + (j.val : ℝ)) / 1600)
      (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch079Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch079Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1580 : ℝ) + (j.val : ℝ)) / 1600)
    (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch079Neg45WeightLower j.val) (hpThetaShiftThreeBatch079Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch079Neg45WeightLower, hpThetaShiftThreeBatch079Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch079Neg45_integral_bounds :
    (-30981 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-29379 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch079Lower hpThetaJensenCellsBatch079Upper
    hpThetaShiftThreeBatch079Neg45WeightLower hpThetaShiftThreeBatch079Neg45WeightUpper hpThetaJensenCellsBatch079_bounds hpThetaShiftThreeBatch079Neg45_weight_bounds
  have hl : (-30981 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch079Lower j * hpThetaShiftThreeBatch079Neg45WeightLower j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftThreeBatch079Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftThreeBatch079Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch079Lower j * hpThetaShiftThreeBatch079Neg45WeightUpper j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftThreeBatch079Neg45WeightUpper j) / 1600) ≤ (-29379 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftThreeBatch079Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1580 : ℝ) / 1600 = 79 / 80 by norm_num,
    show ((1580 : ℝ) + 20) / 1600 = (79 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch079Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1837895747 / 1000000000000 : ℝ)
  | 1 => (927772847 / 500000000000 : ℝ)
  | 2 => (1873286219 / 1000000000000 : ℝ)
  | 3 => (378223467 / 200000000000 : ℝ)
  | 4 => (1909039047 / 1000000000000 : ℝ)
  | 5 => (385410271 / 200000000000 : ℝ)
  | 6 => (972577129 / 500000000000 : ℝ)
  | 7 => (61354617 / 31250000000 : ℝ)
  | 8 => (990815901 / 500000000000 : ℝ)
  | 9 => (2000006411 / 1000000000000 : ℝ)
  | 10 => (504617887 / 250000000000 : ℝ)
  | 11 => (2037027183 / 1000000000000 : ℝ)
  | 12 => (1027836641 / 500000000000 : ℝ)
  | 13 => (414881961 / 200000000000 : ℝ)
  | 14 => (1046618353 / 500000000000 : ℝ)
  | 15 => (132009621 / 62500000000 : ℝ)
  | 16 => (2131161437 / 1000000000000 : ℝ)
  | 17 => (2150259147 / 1000000000000 : ℝ)
  | 18 => (2169447 / 1000000000 : ℝ)
  | 19 => (2188724921 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch079Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (371109139 / 200000000000 : ℝ)
  | 1 => (93664311 / 50000000000 : ℝ)
  | 2 => (236389667 / 125000000000 : ℝ)
  | 3 => (238629881 / 125000000000 : ℝ)
  | 4 => (481762839 / 250000000000 : ℝ)
  | 5 => (1945154259 / 1000000000000 : ℝ)
  | 6 => (392669549 / 200000000000 : ℝ)
  | 7 => (1981631803 / 1000000000000 : ℝ)
  | 8 => (500001603 / 250000000000 : ℝ)
  | 9 => (2018471549 / 1000000000000 : ℝ)
  | 10 => (127314199 / 62500000000 : ℝ)
  | 11 => (2055673283 / 1000000000000 : ℝ)
  | 12 => (1037204903 / 500000000000 : ℝ)
  | 13 => (2093236707 / 1000000000000 : ℝ)
  | 14 => (2112153937 / 1000000000000 : ℝ)
  | 15 => (1065580719 / 500000000000 : ℝ)
  | 16 => (537564787 / 250000000000 : ℝ)
  | 17 => (2169447001 / 1000000000000 : ℝ)
  | 18 => (1094362461 / 500000000000 : ℝ)
  | 19 => (1104046417 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch079Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1580 : ℝ) + (j.val : ℝ)) / 1600)
      (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch079Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch079Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1580 : ℝ) + (j.val : ℝ)) / 1600)
    (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch079Neg25WeightLower j.val) (hpThetaShiftThreeBatch079Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch079Neg25WeightLower, hpThetaShiftThreeBatch079Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch079Neg25_integral_bounds :
    (4429 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (3701 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch079Lower hpThetaJensenCellsBatch079Upper
    hpThetaShiftThreeBatch079Neg25WeightLower hpThetaShiftThreeBatch079Neg25WeightUpper hpThetaJensenCellsBatch079_bounds hpThetaShiftThreeBatch079Neg25_weight_bounds
  have hl : (4429 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch079Lower j * hpThetaShiftThreeBatch079Neg25WeightLower j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftThreeBatch079Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftThreeBatch079Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch079Lower j * hpThetaShiftThreeBatch079Neg25WeightUpper j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftThreeBatch079Neg25WeightUpper j) / 1600) ≤ (3701 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftThreeBatch079Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1580 : ℝ) / 1600 = 79 / 80 by norm_num,
    show ((1580 : ℝ) + 20) / 1600 = (79 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch079Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch079Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch079Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch079Neg25_integral_bounds
end HodgeProofHP
