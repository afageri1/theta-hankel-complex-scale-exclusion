/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch003

/-! Exact signed weight and batch integral certificates, batch 3 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch003Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (20449357 / 31250000000 : ℝ)
  | 1 => (674705177 / 1000000000000 : ℝ)
  | 2 => (173814341 / 250000000000 : ℝ)
  | 3 => (44751923 / 62500000000 : ℝ)
  | 4 => (737020099 / 1000000000000 : ℝ)
  | 5 => (151643999 / 200000000000 : ℝ)
  | 6 => (389812513 / 500000000000 : ℝ)
  | 7 => (801229693 / 1000000000000 : ℝ)
  | 8 => (823028427 / 1000000000000 : ℝ)
  | 9 => (845015593 / 1000000000000 : ℝ)
  | 10 => (173437097 / 200000000000 : ℝ)
  | 11 => (177906467 / 200000000000 : ℝ)
  | 12 => (912050307 / 1000000000000 : ℝ)
  | 13 => (934733499 / 1000000000000 : ℝ)
  | 14 => (191515189 / 200000000000 : ℝ)
  | 15 => (490285809 / 500000000000 : ℝ)
  | 16 => (40148577 / 40000000000 : ℝ)
  | 17 => (256749553 / 250000000000 : ℝ)
  | 18 => (262604191 / 250000000000 : ℝ)
  | 19 => (268490951 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch003Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (337352589 / 500000000000 : ℝ)
  | 1 => (139051473 / 200000000000 : ℝ)
  | 2 => (716030769 / 1000000000000 : ℝ)
  | 3 => (7370201 / 10000000000 : ℝ)
  | 4 => (189554999 / 250000000000 : ℝ)
  | 5 => (779625027 / 1000000000000 : ℝ)
  | 6 => (400614847 / 500000000000 : ℝ)
  | 7 => (205757107 / 250000000000 : ℝ)
  | 8 => (422507797 / 500000000000 : ℝ)
  | 9 => (433592743 / 500000000000 : ℝ)
  | 10 => (55595771 / 62500000000 : ℝ)
  | 11 => (228012577 / 250000000000 : ℝ)
  | 12 => (1869467 / 2000000000 : ℝ)
  | 13 => (478787973 / 500000000000 : ℝ)
  | 14 => (980571619 / 1000000000000 : ℝ)
  | 15 => (501857213 / 500000000000 : ℝ)
  | 16 => (1026998213 / 1000000000000 : ℝ)
  | 17 => (210083353 / 200000000000 : ℝ)
  | 18 => (214792761 / 200000000000 : ℝ)
  | 19 => (1097632999 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch003Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((60 : ℝ) + (j.val : ℝ)) / 1600)
      (((60 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch003Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch003Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((60 : ℝ) + (j.val : ℝ)) / 1600)
    (((60 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch003Neg100WeightLower j.val) (hpThetaShiftOneBatch003Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch003Neg100WeightLower, hpThetaShiftOneBatch003Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch003Neg100_integral_bounds :
    (4685834571 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (9716988933 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (60 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch003Lower hpThetaJensenCellsBatch003Upper
    hpThetaShiftOneBatch003Neg100WeightLower hpThetaShiftOneBatch003Neg100WeightUpper hpThetaJensenCellsBatch003_bounds hpThetaShiftOneBatch003Neg100_weight_bounds
  have hl : (4685834571 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch003Lower j * hpThetaShiftOneBatch003Neg100WeightLower j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftOneBatch003Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftOneBatch003Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch003Lower j * hpThetaShiftOneBatch003Neg100WeightUpper j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftOneBatch003Neg100WeightUpper j) / 1600) ≤ (9716988933 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftOneBatch003Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (60 : ℝ) / 1600 = 3 / 80 by norm_num,
    show ((60 : ℝ) + 20) / 1600 = (3 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch003Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (134256617 / 200000000000 : ℝ)
  | 1 => (346374971 / 500000000000 : ℝ)
  | 2 => (357249653 / 500000000000 : ℝ)
  | 3 => (368263847 / 500000000000 : ℝ)
  | 4 => (47426973 / 62500000000 : ℝ)
  | 5 => (390703671 / 500000000000 : ℝ)
  | 6 => (804251379 / 1000000000000 : ℝ)
  | 7 => (103419999 / 125000000000 : ℝ)
  | 8 => (212682361 / 250000000000 : ℝ)
  | 9 => (218588987 / 250000000000 : ℝ)
  | 10 => (89823567 / 100000000000 : ℝ)
  | 11 => (36894589 / 40000000000 : ℝ)
  | 12 => (47336959 / 50000000000 : ℝ)
  | 13 => (485677527 / 500000000000 : ℝ)
  | 14 => (996208317 / 1000000000000 : ℝ)
  | 15 => (204258979 / 200000000000 : ℝ)
  | 16 => (1046610661 / 1000000000000 : ℝ)
  | 17 => (536075723 / 500000000000 : ℝ)
  | 18 => (137239129 / 125000000000 : ℝ)
  | 19 => (224778231 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch003Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (692749943 / 1000000000000 : ℝ)
  | 1 => (714499307 / 1000000000000 : ℝ)
  | 2 => (147305539 / 200000000000 : ℝ)
  | 3 => (758831569 / 1000000000000 : ℝ)
  | 4 => (781407343 / 1000000000000 : ℝ)
  | 5 => (40212569 / 50000000000 : ℝ)
  | 6 => (827359993 / 1000000000000 : ℝ)
  | 7 => (170145889 / 200000000000 : ℝ)
  | 8 => (874355949 / 1000000000000 : ℝ)
  | 9 => (898235671 / 1000000000000 : ℝ)
  | 10 => (461182363 / 500000000000 : ℝ)
  | 11 => (946739181 / 1000000000000 : ℝ)
  | 12 => (194271011 / 200000000000 : ℝ)
  | 13 => (498104159 / 500000000000 : ℝ)
  | 14 => (63830931 / 62500000000 : ℝ)
  | 15 => (523305331 / 500000000000 : ℝ)
  | 16 => (1072151447 / 1000000000000 : ℝ)
  | 17 => (1097913033 / 1000000000000 : ℝ)
  | 18 => (280972789 / 250000000000 : ℝ)
  | 19 => (575040753 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch003Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((60 : ℝ) + (j.val : ℝ)) / 1600)
      (((60 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch003Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch003Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((60 : ℝ) + (j.val : ℝ)) / 1600)
    (((60 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch003Neg65WeightLower j.val) (hpThetaShiftOneBatch003Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch003Neg65WeightLower, hpThetaShiftOneBatch003Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch003Neg65_integral_bounds :
    (4856889307 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (5041186823 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (60 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch003Lower hpThetaJensenCellsBatch003Upper
    hpThetaShiftOneBatch003Neg65WeightLower hpThetaShiftOneBatch003Neg65WeightUpper hpThetaJensenCellsBatch003_bounds hpThetaShiftOneBatch003Neg65_weight_bounds
  have hl : (4856889307 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch003Lower j * hpThetaShiftOneBatch003Neg65WeightLower j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftOneBatch003Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftOneBatch003Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch003Lower j * hpThetaShiftOneBatch003Neg65WeightUpper j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftOneBatch003Neg65WeightUpper j) / 1600) ≤ (5041186823 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftOneBatch003Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (60 : ℝ) / 1600 = 3 / 80 by norm_num,
    show ((60 : ℝ) + 20) / 1600 = (3 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch003Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (85432587 / 125000000000 : ℝ)
  | 1 => (705753399 / 1000000000000 : ℝ)
  | 2 => (728369579 / 1000000000000 : ℝ)
  | 3 => (751307049 / 1000000000000 : ℝ)
  | 4 => (77456359 / 100000000000 : ℝ)
  | 5 => (15962739 / 20000000000 : ℝ)
  | 6 => (822024843 / 1000000000000 : ℝ)
  | 7 => (846224951 / 1000000000000 : ℝ)
  | 8 => (435367461 / 500000000000 : ℝ)
  | 9 => (895552371 / 1000000000000 : ℝ)
  | 10 => (920674883 / 1000000000000 : ℝ)
  | 11 => (473050003 / 500000000000 : ℝ)
  | 12 => (48591263 / 50000000000 : ℝ)
  | 13 => (997848129 / 1000000000000 : ℝ)
  | 14 => (1024166067 / 1000000000000 : ℝ)
  | 15 => (65673531 / 62500000000 : ℝ)
  | 16 => (269419201 / 250000000000 : ℝ)
  | 17 => (22097287 / 20000000000 : ℝ)
  | 18 => (1132336459 / 1000000000000 : ℝ)
  | 19 => (46403617 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch003Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (3528767 / 5000000000 : ℝ)
  | 1 => (36418479 / 50000000000 : ℝ)
  | 2 => (15026141 / 20000000000 : ℝ)
  | 3 => (774563591 / 1000000000000 : ℝ)
  | 4 => (798136951 / 1000000000000 : ℝ)
  | 5 => (205506211 / 250000000000 : ℝ)
  | 6 => (105778119 / 125000000000 : ℝ)
  | 7 => (870734923 / 1000000000000 : ℝ)
  | 8 => (223888093 / 250000000000 : ℝ)
  | 9 => (230168721 / 250000000000 : ℝ)
  | 10 => (946100007 / 1000000000000 : ℝ)
  | 11 => (971825261 / 1000000000000 : ℝ)
  | 12 => (99784813 / 100000000000 : ℝ)
  | 13 => (256041517 / 250000000000 : ℝ)
  | 14 => (1050776497 / 1000000000000 : ℝ)
  | 15 => (215535361 / 200000000000 : ℝ)
  | 16 => (1104864351 / 1000000000000 : ℝ)
  | 17 => (56616823 / 50000000000 : ℝ)
  | 18 => (580045213 / 500000000000 : ℝ)
  | 19 => (148515439 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch003Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((60 : ℝ) + (j.val : ℝ)) / 1600)
      (((60 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch003Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch003Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((60 : ℝ) + (j.val : ℝ)) / 1600)
    (((60 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch003Neg40WeightLower j.val) (hpThetaShiftOneBatch003Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch003Neg40WeightLower, hpThetaShiftOneBatch003Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch003Neg40_integral_bounds :
    (19922289191 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (20693317891 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (60 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch003Lower hpThetaJensenCellsBatch003Upper
    hpThetaShiftOneBatch003Neg40WeightLower hpThetaShiftOneBatch003Neg40WeightUpper hpThetaJensenCellsBatch003_bounds hpThetaShiftOneBatch003Neg40_weight_bounds
  have hl : (19922289191 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch003Lower j * hpThetaShiftOneBatch003Neg40WeightLower j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftOneBatch003Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftOneBatch003Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch003Lower j * hpThetaShiftOneBatch003Neg40WeightUpper j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftOneBatch003Neg40WeightUpper j) / 1600) ≤ (20693317891 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftOneBatch003Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (60 : ℝ) / 1600 = 3 / 80 by norm_num,
    show ((60 : ℝ) + 20) / 1600 = (3 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch003Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (138653019 / 200000000000 : ℝ)
  | 1 => (716224961 / 1000000000000 : ℝ)
  | 2 => (739541631 / 1000000000000 : ℝ)
  | 3 => (190803499 / 250000000000 : ℝ)
  | 4 => (24601279 / 31250000000 : ℝ)
  | 5 => (202905321 / 250000000000 : ℝ)
  | 6 => (8363539 / 10000000000 : ℝ)
  | 7 => (861437599 / 1000000000000 : ℝ)
  | 8 => (886871183 / 1000000000000 : ℝ)
  | 9 => (456326719 / 500000000000 : ℝ)
  | 10 => (469391567 / 500000000000 : ℝ)
  | 11 => (48262951 / 50000000000 : ℝ)
  | 12 => (124009979 / 125000000000 : ℝ)
  | 13 => (509622143 / 500000000000 : ℝ)
  | 14 => (1046751083 / 1000000000000 : ℝ)
  | 15 => (1074598903 / 1000000000000 : ℝ)
  | 16 => (551393207 / 500000000000 : ℝ)
  | 17 => (1131312263 / 1000000000000 : ℝ)
  | 18 => (29004377 / 25000000000 : ℝ)
  | 19 => (594686741 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch003Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (358112481 / 500000000000 : ℝ)
  | 1 => (5777669 / 7812500000 : ℝ)
  | 2 => (763213997 / 1000000000000 : ℝ)
  | 3 => (787240929 / 1000000000000 : ℝ)
  | 4 => (162324257 / 200000000000 : ℝ)
  | 5 => (836353901 / 1000000000000 : ℝ)
  | 6 => (1076797 / 1250000000 : ℝ)
  | 7 => (55429449 / 62500000000 : ℝ)
  | 8 => (912653439 / 1000000000000 : ℝ)
  | 9 => (187756627 / 200000000000 : ℝ)
  | 10 => (965259021 / 1000000000000 : ℝ)
  | 11 => (992079833 / 1000000000000 : ℝ)
  | 12 => (1019244287 / 1000000000000 : ℝ)
  | 13 => (261687771 / 250000000000 : ℝ)
  | 14 => (134324863 / 125000000000 : ℝ)
  | 15 => (220557283 / 200000000000 : ℝ)
  | 16 => (141414033 / 125000000000 : ℝ)
  | 17 => (1160175081 / 1000000000000 : ℝ)
  | 18 => (1189373483 / 1000000000000 : ℝ)
  | 19 => (76181629 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch003Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((60 : ℝ) + (j.val : ℝ)) / 1600)
      (((60 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch003Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch003Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((60 : ℝ) + (j.val : ℝ)) / 1600)
    (((60 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch003Neg20WeightLower j.val) (hpThetaShiftOneBatch003Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch003Neg20WeightLower, hpThetaShiftOneBatch003Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch003Neg20_integral_bounds :
    (20321691433 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (3 / 80 : ℝ) ((3 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (21120145829 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (60 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch003Lower hpThetaJensenCellsBatch003Upper
    hpThetaShiftOneBatch003Neg20WeightLower hpThetaShiftOneBatch003Neg20WeightUpper hpThetaJensenCellsBatch003_bounds hpThetaShiftOneBatch003Neg20_weight_bounds
  have hl : (20321691433 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch003Lower j * hpThetaShiftOneBatch003Neg20WeightLower j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftOneBatch003Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftOneBatch003Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch003Lower j * hpThetaShiftOneBatch003Neg20WeightUpper j)
        (hpThetaJensenCellsBatch003Upper j * hpThetaShiftOneBatch003Neg20WeightUpper j) / 1600) ≤ (21120145829 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch003Lower, hpThetaJensenCellsBatch003Upper,
      hpThetaShiftOneBatch003Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (60 : ℝ) / 1600 = 3 / 80 by norm_num,
    show ((60 : ℝ) + 20) / 1600 = (3 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch003Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch003Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch003Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch003Neg20_integral_bounds
end HodgeProofHP
