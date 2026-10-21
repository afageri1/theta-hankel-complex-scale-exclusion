/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch046

/-! Exact signed weight and batch integral certificates, batch 46 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch046Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1374135269 / 1000000000000 : ℝ)
  | 1 => (1255571191 / 1000000000000 : ℝ)
  | 2 => (283518467 / 250000000000 : ℝ)
  | 3 => (252399939 / 250000000000 : ℝ)
  | 4 => (441052419 / 500000000000 : ℝ)
  | 5 => (150308923 / 200000000000 : ℝ)
  | 6 => (123574821 / 200000000000 : ℝ)
  | 7 => (481047839 / 1000000000000 : ℝ)
  | 8 => (170509927 / 500000000000 : ℝ)
  | 9 => (39548739 / 200000000000 : ℝ)
  | 10 => (51172403 / 1000000000000 : ℝ)
  | 11 => (-19748297 / 200000000000 : ℝ)
  | 12 => (-126022969 / 500000000000 : ℝ)
  | 13 => (-1277467 / 3125000000 : ℝ)
  | 14 => (-569020991 / 1000000000000 : ℝ)
  | 15 => (-732790113 / 1000000000000 : ℝ)
  | 16 => (-225036713 / 250000000000 : ℝ)
  | 17 => (-214228357 / 200000000000 : ℝ)
  | 18 => (-155728253 / 125000000000 : ℝ)
  | 19 => (-712125609 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch046Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1489809173 / 1000000000000 : ℝ)
  | 1 => (137413527 / 100000000000 : ℝ)
  | 2 => (156946399 / 125000000000 : ℝ)
  | 3 => (1134073869 / 1000000000000 : ℝ)
  | 4 => (1009599757 / 1000000000000 : ℝ)
  | 5 => (882104839 / 1000000000000 : ℝ)
  | 6 => (93943077 / 125000000000 : ℝ)
  | 7 => (308937053 / 500000000000 : ℝ)
  | 8 => (3006549 / 6250000000 : ℝ)
  | 9 => (68203971 / 200000000000 : ℝ)
  | 10 => (12358981 / 62500000000 : ℝ)
  | 11 => (12793101 / 250000000000 : ℝ)
  | 12 => (-24685371 / 250000000000 : ℝ)
  | 13 => (-252045937 / 1000000000000 : ℝ)
  | 14 => (-408789439 / 1000000000000 : ℝ)
  | 15 => (-56902099 / 100000000000 : ℝ)
  | 16 => (-22899691 / 31250000000 : ℝ)
  | 17 => (-900146851 / 1000000000000 : ℝ)
  | 18 => (-133892723 / 125000000000 : ℝ)
  | 19 => (-1245826023 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch046Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((920 : ℝ) + (j.val : ℝ)) / 1600)
      (((920 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch046Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch046Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((920 : ℝ) + (j.val : ℝ)) / 1600)
    (((920 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch046Neg100WeightLower j.val) (hpThetaShiftTwoBatch046Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch046Neg100WeightLower, hpThetaShiftTwoBatch046Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch046Neg100_integral_bounds :
    (54566581 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (33380237 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (920 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch046Lower hpThetaJensenCellsBatch046Upper
    hpThetaShiftTwoBatch046Neg100WeightLower hpThetaShiftTwoBatch046Neg100WeightUpper hpThetaJensenCellsBatch046_bounds hpThetaShiftTwoBatch046Neg100_weight_bounds
  have hl : (54566581 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch046Lower j * hpThetaShiftTwoBatch046Neg100WeightLower j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftTwoBatch046Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftTwoBatch046Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch046Lower j * hpThetaShiftTwoBatch046Neg100WeightUpper j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftTwoBatch046Neg100WeightUpper j) / 1600) ≤ (33380237 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftTwoBatch046Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (920 : ℝ) / 1600 = 46 / 80 by norm_num,
    show ((920 : ℝ) + 20) / 1600 = (46 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch046Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4653908149 / 1000000000000 : ℝ)
  | 1 => (2352272873 / 500000000000 : ℝ)
  | 2 => (237768873 / 50000000000 : ℝ)
  | 3 => (2403200069 / 500000000000 : ℝ)
  | 4 => (4857610561 / 1000000000000 : ℝ)
  | 5 => (613625679 / 125000000000 : ℝ)
  | 6 => (992116277 / 200000000000 : ℝ)
  | 7 => (5012334977 / 1000000000000 : ℝ)
  | 8 => (5064262691 / 1000000000000 : ℝ)
  | 9 => (2558180467 / 500000000000 : ℝ)
  | 10 => (1033725207 / 200000000000 : ℝ)
  | 11 => (652631781 / 125000000000 : ℝ)
  | 12 => (5273641747 / 1000000000000 : ℝ)
  | 13 => (5326384627 / 1000000000000 : ℝ)
  | 14 => (2689639451 / 500000000000 : ℝ)
  | 15 => (2716160253 / 500000000000 : ℝ)
  | 16 => (5485505291 / 1000000000000 : ℝ)
  | 17 => (2769414513 / 500000000000 : ℝ)
  | 18 => (1398071849 / 250000000000 : ℝ)
  | 19 => (2822938001 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch046Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (4704545747 / 1000000000000 : ℝ)
  | 1 => (4755377461 / 1000000000000 : ℝ)
  | 2 => (4806400139 / 1000000000000 : ℝ)
  | 3 => (2428805281 / 500000000000 : ℝ)
  | 4 => (4909005433 / 1000000000000 : ℝ)
  | 5 => (2480290693 / 500000000000 : ℝ)
  | 6 => (2506167489 / 500000000000 : ℝ)
  | 7 => (1266065673 / 250000000000 : ℝ)
  | 8 => (1023272187 / 200000000000 : ℝ)
  | 9 => (1292156509 / 250000000000 : ℝ)
  | 10 => (5221054249 / 1000000000000 : ℝ)
  | 11 => (1318410437 / 250000000000 : ℝ)
  | 12 => (1331596157 / 250000000000 : ℝ)
  | 13 => (5379278903 / 1000000000000 : ℝ)
  | 14 => (5432320507 / 1000000000000 : ℝ)
  | 15 => (1371376323 / 250000000000 : ℝ)
  | 16 => (5538829027 / 1000000000000 : ℝ)
  | 17 => (5592287397 / 1000000000000 : ℝ)
  | 18 => (5645876003 / 1000000000000 : ℝ)
  | 19 => (5699590361 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch046Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((920 : ℝ) + (j.val : ℝ)) / 1600)
      (((920 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch046Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch046Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((920 : ℝ) + (j.val : ℝ)) / 1600)
    (((920 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch046Neg65WeightLower j.val) (hpThetaShiftTwoBatch046Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch046Neg65WeightLower, hpThetaShiftTwoBatch046Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch046Neg65_integral_bounds :
    (2535241801 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (521632847 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (920 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch046Lower hpThetaJensenCellsBatch046Upper
    hpThetaShiftTwoBatch046Neg65WeightLower hpThetaShiftTwoBatch046Neg65WeightUpper hpThetaJensenCellsBatch046_bounds hpThetaShiftTwoBatch046Neg65_weight_bounds
  have hl : (2535241801 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch046Lower j * hpThetaShiftTwoBatch046Neg65WeightLower j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftTwoBatch046Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftTwoBatch046Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch046Lower j * hpThetaShiftTwoBatch046Neg65WeightUpper j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftTwoBatch046Neg65WeightUpper j) / 1600) ≤ (521632847 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftTwoBatch046Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (920 : ℝ) / 1600 = 46 / 80 by norm_num,
    show ((920 : ℝ) + 20) / 1600 = (46 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch046Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-245443889 / 1000000000000 : ℝ)
  | 1 => (-224534547 / 1000000000000 : ℝ)
  | 2 => (-203342591 / 1000000000000 : ℝ)
  | 3 => (-181866373 / 1000000000000 : ℝ)
  | 4 => (-20013031 / 125000000000 : ℝ)
  | 5 => (-5522183 / 40000000000 : ℝ)
  | 6 => (-57857857 / 500000000000 : ℝ)
  | 7 => (-93086031 / 1000000000000 : ℝ)
  | 8 => (-70163893 / 1000000000000 : ℝ)
  | 9 => (-46947671 / 1000000000000 : ℝ)
  | 10 => (-11717871 / 500000000000 : ℝ)
  | 11 => (74703 / 200000000000 : ℝ)
  | 12 => (6120429 / 250000000000 : ℝ)
  | 13 => (24445237 / 500000000000 : ℝ)
  | 14 => (18400349 / 250000000000 : ℝ)
  | 15 => (49308043 / 500000000000 : ℝ)
  | 16 => (6196807 / 50000000000 : ℝ)
  | 17 => (149563153 / 1000000000000 : ℝ)
  | 18 => (175498713 / 1000000000000 : ℝ)
  | 19 => (201744401 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch046Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-112267273 / 500000000000 : ℝ)
  | 1 => (-20334259 / 100000000000 : ℝ)
  | 2 => (-45466593 / 250000000000 : ℝ)
  | 3 => (-160104247 / 1000000000000 : ℝ)
  | 4 => (-69027287 / 500000000000 : ℝ)
  | 5 => (-115715713 / 1000000000000 : ℝ)
  | 6 => (-9308603 / 100000000000 : ℝ)
  | 7 => (-17540973 / 250000000000 : ℝ)
  | 8 => (-4694767 / 100000000000 : ℝ)
  | 9 => (-23435741 / 1000000000000 : ℝ)
  | 10 => (93379 / 250000000000 : ℝ)
  | 11 => (24481717 / 1000000000000 : ℝ)
  | 12 => (1955619 / 40000000000 : ℝ)
  | 13 => (73601397 / 1000000000000 : ℝ)
  | 14 => (98616087 / 1000000000000 : ℝ)
  | 15 => (123936141 / 1000000000000 : ℝ)
  | 16 => (74781577 / 500000000000 : ℝ)
  | 17 => (87749357 / 500000000000 : ℝ)
  | 18 => (100872201 / 500000000000 : ℝ)
  | 19 => (228301797 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch046Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((920 : ℝ) + (j.val : ℝ)) / 1600)
      (((920 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch046Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch046Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((920 : ℝ) + (j.val : ℝ)) / 1600)
    (((920 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch046Neg45WeightLower j.val) (hpThetaShiftTwoBatch046Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch046Neg45WeightLower, hpThetaShiftTwoBatch046Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch046Neg45_integral_bounds :
    (-19378879 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-6515593 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (920 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch046Lower hpThetaJensenCellsBatch046Upper
    hpThetaShiftTwoBatch046Neg45WeightLower hpThetaShiftTwoBatch046Neg45WeightUpper hpThetaJensenCellsBatch046_bounds hpThetaShiftTwoBatch046Neg45_weight_bounds
  have hl : (-19378879 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch046Lower j * hpThetaShiftTwoBatch046Neg45WeightLower j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftTwoBatch046Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftTwoBatch046Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch046Lower j * hpThetaShiftTwoBatch046Neg45WeightUpper j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftTwoBatch046Neg45WeightUpper j) / 1600) ≤ (-6515593 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftTwoBatch046Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (920 : ℝ) / 1600 = 46 / 80 by norm_num,
    show ((920 : ℝ) + 20) / 1600 = (46 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch046Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2198075417 / 1000000000000 : ℝ)
  | 1 => (-221201487 / 100000000000 : ℝ)
  | 2 => (-2225959157 / 1000000000000 : ℝ)
  | 3 => (-2239907597 / 1000000000000 : ℝ)
  | 4 => (-1126929751 / 500000000000 : ℝ)
  | 5 => (-113390709 / 50000000000 : ℝ)
  | 6 => (-2281770931 / 1000000000000 : ℝ)
  | 7 => (-286966131 / 125000000000 : ℝ)
  | 8 => (-2309687823 / 1000000000000 : ℝ)
  | 9 => (-290455817 / 125000000000 : ℝ)
  | 10 => (-146100279 / 62500000000 : ℝ)
  | 11 => (-2351560879 / 1000000000000 : ℝ)
  | 12 => (-473103009 / 200000000000 : ℝ)
  | 13 => (-118973311 / 50000000000 : ℝ)
  | 14 => (-2393413657 / 1000000000000 : ℝ)
  | 15 => (-2407356601 / 1000000000000 : ℝ)
  | 16 => (-1210647147 / 500000000000 : ℝ)
  | 17 => (-243522597 / 100000000000 : ℝ)
  | 18 => (-489830171 / 200000000000 : ℝ)
  | 19 => (-615767043 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch046Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1092070737 / 500000000000 : ℝ)
  | 1 => (-274759427 / 125000000000 : ℝ)
  | 2 => (-2212014869 / 1000000000000 : ℝ)
  | 3 => (-556489789 / 250000000000 : ℝ)
  | 4 => (-559976899 / 250000000000 : ℝ)
  | 5 => (-2253859501 / 1000000000000 : ℝ)
  | 6 => (-2267814179 / 1000000000000 : ℝ)
  | 7 => (-228177093 / 100000000000 : ℝ)
  | 8 => (-2295729047 / 1000000000000 : ℝ)
  | 9 => (-1154843911 / 500000000000 : ℝ)
  | 10 => (-464729307 / 200000000000 : ℝ)
  | 11 => (-2337604463 / 1000000000000 : ℝ)
  | 12 => (-1175780439 / 500000000000 : ℝ)
  | 13 => (-591378761 / 250000000000 : ℝ)
  | 14 => (-2379466219 / 1000000000000 : ℝ)
  | 15 => (-299176707 / 125000000000 : ℝ)
  | 16 => (-12036783 / 5000000000 : ℝ)
  | 17 => (-2421294293 / 1000000000000 : ℝ)
  | 18 => (-2435225969 / 1000000000000 : ℝ)
  | 19 => (-1224575427 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch046Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((920 : ℝ) + (j.val : ℝ)) / 1600)
      (((920 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch046Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch046Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((920 : ℝ) + (j.val : ℝ)) / 1600)
    (((920 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch046Neg25WeightLower j.val) (hpThetaShiftTwoBatch046Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch046Neg25WeightLower, hpThetaShiftTwoBatch046Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch046Neg25_integral_bounds :
    (-585522159 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (46 / 80 : ℝ) ((46 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-1143003951 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (920 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch046Lower hpThetaJensenCellsBatch046Upper
    hpThetaShiftTwoBatch046Neg25WeightLower hpThetaShiftTwoBatch046Neg25WeightUpper hpThetaJensenCellsBatch046_bounds hpThetaShiftTwoBatch046Neg25_weight_bounds
  have hl : (-585522159 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch046Lower j * hpThetaShiftTwoBatch046Neg25WeightLower j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftTwoBatch046Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftTwoBatch046Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch046Lower j * hpThetaShiftTwoBatch046Neg25WeightUpper j)
        (hpThetaJensenCellsBatch046Upper j * hpThetaShiftTwoBatch046Neg25WeightUpper j) / 1600) ≤ (-1143003951 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch046Lower, hpThetaJensenCellsBatch046Upper,
      hpThetaShiftTwoBatch046Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (920 : ℝ) / 1600 = 46 / 80 by norm_num,
    show ((920 : ℝ) + 20) / 1600 = (46 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch046Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch046Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch046Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch046Neg25_integral_bounds
end HodgeProofHP
