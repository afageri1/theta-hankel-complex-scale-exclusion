/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch053

/-! Exact signed weight and batch integral certificates, batch 53 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch053Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-52460457 / 100000000000 : ℝ)
  | 1 => (-270131323 / 500000000000 : ℝ)
  | 2 => (-556208251 / 1000000000000 : ℝ)
  | 3 => (-286222719 / 500000000000 : ℝ)
  | 4 => (-588978309 / 1000000000000 : ℝ)
  | 5 => (-60581101 / 100000000000 : ℝ)
  | 6 => (-77868467 / 125000000000 : ℝ)
  | 7 => (-640392731 / 1000000000000 : ℝ)
  | 8 => (-329075143 / 500000000000 : ℝ)
  | 9 => (-676224739 / 1000000000000 : ℝ)
  | 10 => (-347310241 / 500000000000 : ℝ)
  | 11 => (-696623 / 976562500 : ℝ)
  | 12 => (-366196819 / 500000000000 : ℝ)
  | 13 => (-9397251 / 12500000000 : ℝ)
  | 14 => (-77150587 / 100000000000 : ℝ)
  | 15 => (-791575649 / 1000000000000 : ℝ)
  | 16 => (-792963 / 976562500 : ℝ)
  | 17 => (-416383003 / 500000000000 : ℝ)
  | 18 => (-213474033 / 250000000000 : ℝ)
  | 19 => (-437694671 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch053Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-509230013 / 1000000000000 : ℝ)
  | 1 => (-524604569 / 1000000000000 : ℝ)
  | 2 => (-108052529 / 200000000000 : ℝ)
  | 3 => (-2224833 / 4000000000 : ℝ)
  | 4 => (-572445437 / 1000000000000 : ℝ)
  | 5 => (-147244577 / 250000000000 : ℝ)
  | 6 => (-605811009 / 1000000000000 : ℝ)
  | 7 => (-124589547 / 200000000000 : ℝ)
  | 8 => (-64039273 / 100000000000 : ℝ)
  | 9 => (-131630057 / 200000000000 : ℝ)
  | 10 => (-338112369 / 500000000000 : ℝ)
  | 11 => (-694620481 / 1000000000000 : ℝ)
  | 12 => (-713341951 / 1000000000000 : ℝ)
  | 13 => (-732393637 / 1000000000000 : ℝ)
  | 14 => (-751780079 / 1000000000000 : ℝ)
  | 15 => (-771505869 / 1000000000000 : ℝ)
  | 16 => (-24736739 / 31250000000 : ℝ)
  | 17 => (-811994111 / 1000000000000 : ℝ)
  | 18 => (-166553201 / 200000000000 : ℝ)
  | 19 => (-853896131 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch053Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1060 : ℝ) + (j.val : ℝ)) / 1600)
      (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch053Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch053Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1060 : ℝ) + (j.val : ℝ)) / 1600)
    (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch053Neg100WeightLower j.val) (hpThetaShiftThreeBatch053Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch053Neg100WeightLower, hpThetaShiftThreeBatch053Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch053Neg100_integral_bounds :
    (-15387433 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-73363923 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1060 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch053Lower hpThetaJensenCellsBatch053Upper
    hpThetaShiftThreeBatch053Neg100WeightLower hpThetaShiftThreeBatch053Neg100WeightUpper hpThetaJensenCellsBatch053_bounds hpThetaShiftThreeBatch053Neg100_weight_bounds
  have hl : (-15387433 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch053Lower j * hpThetaShiftThreeBatch053Neg100WeightLower j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftThreeBatch053Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftThreeBatch053Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch053Lower j * hpThetaShiftThreeBatch053Neg100WeightUpper j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftThreeBatch053Neg100WeightUpper j) / 1600) ≤ (-73363923 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftThreeBatch053Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1060 : ℝ) / 1600 = 53 / 80 by norm_num,
    show ((1060 : ℝ) + 20) / 1600 = (53 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch053Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (148895163 / 500000000000 : ℝ)
  | 1 => (2997333 / 10000000000 : ℝ)
  | 2 => (301664557 / 1000000000000 : ℝ)
  | 3 => (303583547 / 1000000000000 : ℝ)
  | 4 => (30548971 / 100000000000 : ℝ)
  | 5 => (307382479 / 1000000000000 : ℝ)
  | 6 => (12370451 / 40000000000 : ℝ)
  | 7 => (311125511 / 1000000000000 : ℝ)
  | 8 => (312974589 / 1000000000000 : ℝ)
  | 9 => (314807903 / 1000000000000 : ℝ)
  | 10 => (79156209 / 250000000000 : ℝ)
  | 11 => (318424761 / 1000000000000 : ℝ)
  | 12 => (1000647 / 3125000000 : ℝ)
  | 13 => (160985513 / 500000000000 : ℝ)
  | 14 => (161858031 / 500000000000 : ℝ)
  | 15 => (8136037 / 25000000000 : ℝ)
  | 16 => (327146599 / 1000000000000 : ℝ)
  | 17 => (328830731 / 1000000000000 : ℝ)
  | 18 => (41311647 / 125000000000 : ℝ)
  | 19 => (332133221 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch053Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (299733301 / 1000000000000 : ℝ)
  | 1 => (150832279 / 500000000000 : ℝ)
  | 2 => (75895887 / 250000000000 : ℝ)
  | 3 => (305489711 / 1000000000000 : ℝ)
  | 4 => (3842281 / 12500000000 : ℝ)
  | 5 => (77315319 / 250000000000 : ℝ)
  | 6 => (38890689 / 125000000000 : ℝ)
  | 7 => (31297459 / 100000000000 : ℝ)
  | 8 => (9837747 / 31250000000 : ℝ)
  | 9 => (316624837 / 1000000000000 : ℝ)
  | 10 => (159212381 / 500000000000 : ℝ)
  | 11 => (320207041 / 1000000000000 : ℝ)
  | 12 => (321971027 / 1000000000000 : ℝ)
  | 13 => (323716063 / 1000000000000 : ℝ)
  | 14 => (325441481 / 1000000000000 : ℝ)
  | 15 => (1635733 / 5000000000 : ℝ)
  | 16 => (82207683 / 250000000000 : ℝ)
  | 17 => (330493177 / 1000000000000 : ℝ)
  | 18 => (166066611 / 500000000000 : ℝ)
  | 19 => (66750029 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch053Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1060 : ℝ) + (j.val : ℝ)) / 1600)
      (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch053Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch053Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1060 : ℝ) + (j.val : ℝ)) / 1600)
    (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch053Neg70WeightLower j.val) (hpThetaShiftThreeBatch053Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch053Neg70WeightLower, hpThetaShiftThreeBatch053Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch053Neg70_integral_bounds :
    (6941379 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (1425273 / 40000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1060 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch053Lower hpThetaJensenCellsBatch053Upper
    hpThetaShiftThreeBatch053Neg70WeightLower hpThetaShiftThreeBatch053Neg70WeightUpper hpThetaJensenCellsBatch053_bounds hpThetaShiftThreeBatch053Neg70_weight_bounds
  have hl : (6941379 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch053Lower j * hpThetaShiftThreeBatch053Neg70WeightLower j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftThreeBatch053Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftThreeBatch053Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch053Lower j * hpThetaShiftThreeBatch053Neg70WeightUpper j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftThreeBatch053Neg70WeightUpper j) / 1600) ≤ (1425273 / 40000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftThreeBatch053Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1060 : ℝ) / 1600 = 53 / 80 by norm_num,
    show ((1060 : ℝ) + 20) / 1600 = (53 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch053Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (15452219 / 1000000000000 : ℝ)
  | 1 => (669071 / 40000000000 : ℝ)
  | 2 => (180187 / 10000000000 : ℝ)
  | 3 => (9664059 / 500000000000 : ℝ)
  | 4 => (20655151 / 1000000000000 : ℝ)
  | 5 => (21999921 / 1000000000000 : ℝ)
  | 6 => (23362553 / 1000000000000 : ℝ)
  | 7 => (24743167 / 1000000000000 : ℝ)
  | 8 => (408467 / 15625000000 : ℝ)
  | 9 => (13779419 / 500000000000 : ℝ)
  | 10 => (1449707 / 50000000000 : ℝ)
  | 11 => (30447917 / 1000000000000 : ℝ)
  | 12 => (7980073 / 250000000000 : ℝ)
  | 13 => (33411387 / 1000000000000 : ℝ)
  | 14 => (1396853 / 40000000000 : ℝ)
  | 15 => (36450229 / 1000000000000 : ℝ)
  | 16 => (18999111 / 500000000000 : ℝ)
  | 17 => (1582617 / 40000000000 : ℝ)
  | 18 => (20575981 / 500000000000 : ℝ)
  | 19 => (21378977 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch053Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2090847 / 125000000000 : ℝ)
  | 1 => (18018701 / 1000000000000 : ℝ)
  | 2 => (19328119 / 1000000000000 : ℝ)
  | 3 => (1290947 / 62500000000 : ℝ)
  | 4 => (10999961 / 500000000000 : ℝ)
  | 5 => (11681277 / 500000000000 : ℝ)
  | 6 => (96653 / 3906250000 : ℝ)
  | 7 => (26141889 / 1000000000000 : ℝ)
  | 8 => (27558839 / 1000000000000 : ℝ)
  | 9 => (28994141 / 1000000000000 : ℝ)
  | 10 => (15223959 / 500000000000 : ℝ)
  | 11 => (31920293 / 1000000000000 : ℝ)
  | 12 => (8352847 / 250000000000 : ℝ)
  | 13 => (17460663 / 500000000000 : ℝ)
  | 14 => (3645023 / 100000000000 : ℝ)
  | 15 => (37998223 / 1000000000000 : ℝ)
  | 16 => (19782713 / 500000000000 : ℝ)
  | 17 => (41151963 / 1000000000000 : ℝ)
  | 18 => (8551591 / 200000000000 : ℝ)
  | 19 => (1775341 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch053Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1060 : ℝ) + (j.val : ℝ)) / 1600)
      (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch053Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch053Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1060 : ℝ) + (j.val : ℝ)) / 1600)
    (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch053Neg45WeightLower j.val) (hpThetaShiftThreeBatch053Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch053Neg45WeightLower, hpThetaShiftThreeBatch053Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch053Neg45_integral_bounds :
    (772211 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (663037 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1060 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch053Lower hpThetaJensenCellsBatch053Upper
    hpThetaShiftThreeBatch053Neg45WeightLower hpThetaShiftThreeBatch053Neg45WeightUpper hpThetaJensenCellsBatch053_bounds hpThetaShiftThreeBatch053Neg45_weight_bounds
  have hl : (772211 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch053Lower j * hpThetaShiftThreeBatch053Neg45WeightLower j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftThreeBatch053Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftThreeBatch053Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch053Lower j * hpThetaShiftThreeBatch053Neg45WeightUpper j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftThreeBatch053Neg45WeightUpper j) / 1600) ≤ (663037 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftThreeBatch053Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1060 : ℝ) / 1600 = 53 / 80 by norm_num,
    show ((1060 : ℝ) + 20) / 1600 = (53 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch053Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-110983597 / 1000000000000 : ℝ)
  | 1 => (-55937929 / 500000000000 : ℝ)
  | 2 => (-112770651 / 1000000000000 : ℝ)
  | 3 => (-22733589 / 200000000000 : ℝ)
  | 4 => (-3580241 / 31250000000 : ℝ)
  | 5 => (-115469921 / 1000000000000 : ℝ)
  | 6 => (-58187271 / 500000000000 : ℝ)
  | 7 => (-14660193 / 125000000000 : ℝ)
  | 8 => (-23638179 / 200000000000 : ℝ)
  | 9 => (-119102563 / 1000000000000 : ℝ)
  | 10 => (-30004129 / 250000000000 : ℝ)
  | 11 => (-120932721 / 1000000000000 : ℝ)
  | 12 => (-15231393 / 125000000000 : ℝ)
  | 13 => (-15346469 / 125000000000 : ℝ)
  | 14 => (-12369451 / 100000000000 : ℝ)
  | 15 => (-15577423 / 125000000000 : ℝ)
  | 16 => (-62773169 / 500000000000 : ℝ)
  | 17 => (-15809417 / 125000000000 : ℝ)
  | 18 => (-127406341 / 1000000000000 : ℝ)
  | 19 => (-64169659 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch053Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-22018779 / 200000000000 : ℝ)
  | 1 => (-27745899 / 250000000000 : ℝ)
  | 2 => (-111875857 / 1000000000000 : ℝ)
  | 3 => (-2255413 / 20000000000 : ℝ)
  | 4 => (-14208493 / 125000000000 : ℝ)
  | 5 => (-114567711 / 1000000000000 : ℝ)
  | 6 => (-721687 / 6250000000 : ℝ)
  | 7 => (-116374541 / 1000000000000 : ℝ)
  | 8 => (-117281543 / 1000000000000 : ℝ)
  | 9 => (-59095447 / 500000000000 : ℝ)
  | 10 => (-59551281 / 500000000000 : ℝ)
  | 11 => (-24003303 / 200000000000 : ℝ)
  | 12 => (-1511659 / 12500000000 : ℝ)
  | 13 => (-121851143 / 1000000000000 : ℝ)
  | 14 => (-122771751 / 1000000000000 : ℝ)
  | 15 => (-123694509 / 1000000000000 : ℝ)
  | 16 => (-124619383 / 1000000000000 : ℝ)
  | 17 => (-125546337 / 1000000000000 : ℝ)
  | 18 => (-25295067 / 200000000000 : ℝ)
  | 19 => (-6370317 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch053Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1060 : ℝ) + (j.val : ℝ)) / 1600)
      (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch053Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch053Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1060 : ℝ) + (j.val : ℝ)) / 1600)
    (((1060 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch053Neg25WeightLower j.val) (hpThetaShiftThreeBatch053Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch053Neg25WeightLower, hpThetaShiftThreeBatch053Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch053Neg25_integral_bounds :
    (-13422403 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (53 / 80 : ℝ) ((53 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-6524219 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1060 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch053Lower hpThetaJensenCellsBatch053Upper
    hpThetaShiftThreeBatch053Neg25WeightLower hpThetaShiftThreeBatch053Neg25WeightUpper hpThetaJensenCellsBatch053_bounds hpThetaShiftThreeBatch053Neg25_weight_bounds
  have hl : (-13422403 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch053Lower j * hpThetaShiftThreeBatch053Neg25WeightLower j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftThreeBatch053Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftThreeBatch053Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch053Lower j * hpThetaShiftThreeBatch053Neg25WeightUpper j)
        (hpThetaJensenCellsBatch053Upper j * hpThetaShiftThreeBatch053Neg25WeightUpper j) / 1600) ≤ (-6524219 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch053Lower, hpThetaJensenCellsBatch053Upper,
      hpThetaShiftThreeBatch053Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1060 : ℝ) / 1600 = 53 / 80 by norm_num,
    show ((1060 : ℝ) + 20) / 1600 = (53 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch053Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch053Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch053Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch053Neg25_integral_bounds
end HodgeProofHP
