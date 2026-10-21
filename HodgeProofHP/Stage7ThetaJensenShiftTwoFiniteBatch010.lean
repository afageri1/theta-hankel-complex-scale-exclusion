/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch010

/-! Exact signed weight and batch integral certificates, batch 10 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch010Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (11841879 / 1000000000000 : ℝ)
  | 1 => (3000973 / 250000000000 : ℝ)
  | 2 => (3041559 / 250000000000 : ℝ)
  | 3 => (1232887 / 100000000000 : ℝ)
  | 4 => (1561469 / 125000000000 : ℝ)
  | 5 => (6327419 / 500000000000 : ℝ)
  | 6 => (6409043 / 500000000000 : ℝ)
  | 7 => (12981449 / 1000000000000 : ℝ)
  | 8 => (3286221 / 250000000000 : ℝ)
  | 9 => (1663543 / 125000000000 : ℝ)
  | 10 => (13471781 / 1000000000000 : ℝ)
  | 11 => (13635147 / 1000000000000 : ℝ)
  | 12 => (6899197 / 500000000000 : ℝ)
  | 13 => (13961473 / 1000000000000 : ℝ)
  | 14 => (3531083 / 250000000000 : ℝ)
  | 15 => (14286921 / 1000000000000 : ℝ)
  | 16 => (3612297 / 250000000000 : ℝ)
  | 17 => (7305539 / 500000000000 : ℝ)
  | 18 => (738627 / 50000000000 : ℝ)
  | 19 => (14933517 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch010Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (12003893 / 1000000000000 : ℝ)
  | 1 => (12166237 / 1000000000000 : ℝ)
  | 2 => (12328871 / 1000000000000 : ℝ)
  | 3 => (12491753 / 1000000000000 : ℝ)
  | 4 => (12654839 / 1000000000000 : ℝ)
  | 5 => (12818087 / 1000000000000 : ℝ)
  | 6 => (259629 / 20000000000 : ℝ)
  | 7 => (2628977 / 200000000000 : ℝ)
  | 8 => (2661669 / 200000000000 : ℝ)
  | 9 => (6735891 / 500000000000 : ℝ)
  | 10 => (3408787 / 250000000000 : ℝ)
  | 11 => (2759679 / 200000000000 : ℝ)
  | 12 => (6980737 / 500000000000 : ℝ)
  | 13 => (14124333 / 1000000000000 : ℝ)
  | 14 => (7143461 / 500000000000 : ℝ)
  | 15 => (14449189 / 1000000000000 : ℝ)
  | 16 => (14611079 / 1000000000000 : ℝ)
  | 17 => (14772541 / 1000000000000 : ℝ)
  | 18 => (7466759 / 500000000000 : ℝ)
  | 19 => (3773489 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch010Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((200 : ℝ) + (j.val : ℝ)) / 1600)
      (((200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch010Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch010Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((200 : ℝ) + (j.val : ℝ)) / 1600)
    (((200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch010Neg100WeightLower j.val) (hpThetaShiftTwoBatch010Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch010Neg100WeightLower, hpThetaShiftTwoBatch010Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch010Neg100_integral_bounds :
    (252745427 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (129359151 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch010Lower hpThetaJensenCellsBatch010Upper
    hpThetaShiftTwoBatch010Neg100WeightLower hpThetaShiftTwoBatch010Neg100WeightUpper hpThetaJensenCellsBatch010_bounds hpThetaShiftTwoBatch010Neg100_weight_bounds
  have hl : (252745427 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch010Lower j * hpThetaShiftTwoBatch010Neg100WeightLower j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftTwoBatch010Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftTwoBatch010Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch010Lower j * hpThetaShiftTwoBatch010Neg100WeightUpper j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftTwoBatch010Neg100WeightUpper j) / 1600) ≤ (129359151 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftTwoBatch010Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (200 : ℝ) / 1600 = 10 / 80 by norm_num,
    show ((200 : ℝ) + 20) / 1600 = (10 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch010Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (7293703 / 500000000000 : ℝ)
  | 1 => (1853367 / 125000000000 : ℝ)
  | 2 => (3767129 / 250000000000 : ℝ)
  | 3 => (15312133 / 1000000000000 : ℝ)
  | 4 => (15557769 / 1000000000000 : ℝ)
  | 5 => (1580541 / 100000000000 : ℝ)
  | 6 => (16055039 / 1000000000000 : ℝ)
  | 7 => (8153319 / 500000000000 : ℝ)
  | 8 => (4140047 / 250000000000 : ℝ)
  | 9 => (2101959 / 125000000000 : ℝ)
  | 10 => (1707307 / 100000000000 : ℝ)
  | 11 => (17332361 / 1000000000000 : ℝ)
  | 12 => (703741 / 40000000000 : ℝ)
  | 13 => (892827 / 50000000000 : ℝ)
  | 14 => (2265173 / 125000000000 : ℝ)
  | 15 => (9194017 / 500000000000 : ℝ)
  | 16 => (9328233 / 500000000000 : ℝ)
  | 17 => (3785331 / 200000000000 : ℝ)
  | 18 => (9599289 / 500000000000 : ℝ)
  | 19 => (19472207 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch010Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (14826937 / 1000000000000 : ℝ)
  | 1 => (15068517 / 1000000000000 : ℝ)
  | 2 => (7656067 / 500000000000 : ℝ)
  | 3 => (1555777 / 100000000000 : ℝ)
  | 4 => (15805411 / 1000000000000 : ℝ)
  | 5 => (12543 / 781250000 : ℝ)
  | 6 => (16306639 / 1000000000000 : ℝ)
  | 7 => (16560189 / 1000000000000 : ℝ)
  | 8 => (16815673 / 1000000000000 : ℝ)
  | 9 => (17073071 / 1000000000000 : ℝ)
  | 10 => (8666181 / 500000000000 : ℝ)
  | 11 => (8796763 / 500000000000 : ℝ)
  | 12 => (17856541 / 1000000000000 : ℝ)
  | 13 => (3624277 / 200000000000 : ℝ)
  | 14 => (3677607 / 200000000000 : ℝ)
  | 15 => (18656467 / 1000000000000 : ℝ)
  | 16 => (295729 / 15625000000 : ℝ)
  | 17 => (19198579 / 1000000000000 : ℝ)
  | 18 => (1217013 / 62500000000 : ℝ)
  | 19 => (19747517 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch010Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((200 : ℝ) + (j.val : ℝ)) / 1600)
      (((200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch010Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch010Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((200 : ℝ) + (j.val : ℝ)) / 1600)
    (((200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch010Neg65WeightLower j.val) (hpThetaShiftTwoBatch010Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch010Neg65WeightLower, hpThetaShiftTwoBatch010Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch010Neg65_integral_bounds :
    (32039697 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (82239447 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch010Lower hpThetaJensenCellsBatch010Upper
    hpThetaShiftTwoBatch010Neg65WeightLower hpThetaShiftTwoBatch010Neg65WeightUpper hpThetaJensenCellsBatch010_bounds hpThetaShiftTwoBatch010Neg65_weight_bounds
  have hl : (32039697 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch010Lower j * hpThetaShiftTwoBatch010Neg65WeightLower j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftTwoBatch010Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftTwoBatch010Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch010Lower j * hpThetaShiftTwoBatch010Neg65WeightUpper j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftTwoBatch010Neg65WeightUpper j) / 1600) ≤ (82239447 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftTwoBatch010Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (200 : ℝ) / 1600 = 10 / 80 by norm_num,
    show ((200 : ℝ) + 20) / 1600 = (10 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch010Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3253249 / 200000000000 : ℝ)
  | 1 => (2069309 / 125000000000 : ℝ)
  | 2 => (3369177 / 200000000000 : ℝ)
  | 3 => (2142561 / 125000000000 : ℝ)
  | 4 => (8719143 / 500000000000 : ℝ)
  | 5 => (8869641 / 500000000000 : ℝ)
  | 6 => (451087 / 25000000000 : ℝ)
  | 7 => (9175441 / 500000000000 : ℝ)
  | 8 => (18661493 / 1000000000000 : ℝ)
  | 9 => (1185957 / 62500000000 : ℝ)
  | 10 => (9646171 / 500000000000 : ℝ)
  | 11 => (2451573 / 125000000000 : ℝ)
  | 12 => (19936039 / 1000000000000 : ℝ)
  | 13 => (10131353 / 500000000000 : ℝ)
  | 14 => (4118517 / 200000000000 : ℝ)
  | 15 => (10462837 / 500000000000 : ℝ)
  | 16 => (21261973 / 1000000000000 : ℝ)
  | 17 => (21601479 / 1000000000000 : ℝ)
  | 18 => (2194419 / 100000000000 : ℝ)
  | 19 => (22290103 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch010Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (16554473 / 1000000000000 : ℝ)
  | 1 => (8422943 / 500000000000 : ℝ)
  | 2 => (17140489 / 1000000000000 : ℝ)
  | 3 => (17438287 / 1000000000000 : ℝ)
  | 4 => (17739283 / 1000000000000 : ℝ)
  | 5 => (18043481 / 1000000000000 : ℝ)
  | 6 => (18350883 / 1000000000000 : ℝ)
  | 7 => (9330747 / 500000000000 : ℝ)
  | 8 => (18975313 / 1000000000000 : ℝ)
  | 9 => (19292343 / 1000000000000 : ℝ)
  | 10 => (3922517 / 200000000000 : ℝ)
  | 11 => (498401 / 25000000000 : ℝ)
  | 12 => (20262707 / 1000000000000 : ℝ)
  | 13 => (10296293 / 500000000000 : ℝ)
  | 14 => (837027 / 40000000000 : ℝ)
  | 15 => (10630987 / 500000000000 : ℝ)
  | 16 => (540037 / 25000000000 : ℝ)
  | 17 => (21944191 / 1000000000000 : ℝ)
  | 18 => (2786263 / 125000000000 : ℝ)
  | 19 => (4527843 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch010Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((200 : ℝ) + (j.val : ℝ)) / 1600)
      (((200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch010Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch010Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((200 : ℝ) + (j.val : ℝ)) / 1600)
    (((200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch010Neg45WeightLower j.val) (hpThetaShiftTwoBatch010Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch010Neg45WeightLower, hpThetaShiftTwoBatch010Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch010Neg45_integral_bounds :
    (90525481 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (186146499 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch010Lower hpThetaJensenCellsBatch010Upper
    hpThetaShiftTwoBatch010Neg45WeightLower hpThetaShiftTwoBatch010Neg45WeightUpper hpThetaJensenCellsBatch010_bounds hpThetaShiftTwoBatch010Neg45_weight_bounds
  have hl : (90525481 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch010Lower j * hpThetaShiftTwoBatch010Neg45WeightLower j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftTwoBatch010Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftTwoBatch010Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch010Lower j * hpThetaShiftTwoBatch010Neg45WeightUpper j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftTwoBatch010Neg45WeightUpper j) / 1600) ≤ (186146499 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftTwoBatch010Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (200 : ℝ) / 1600 = 10 / 80 by norm_num,
    show ((200 : ℝ) + 20) / 1600 = (10 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch010Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4506727 / 250000000000 : ℝ)
  | 1 => (2295891 / 125000000000 : ℝ)
  | 2 => (2338973 / 125000000000 : ℝ)
  | 3 => (2382613 / 125000000000 : ℝ)
  | 4 => (19414513 / 1000000000000 : ℝ)
  | 5 => (9886321 / 500000000000 : ℝ)
  | 6 => (4027063 / 200000000000 : ℝ)
  | 7 => (20502561 / 1000000000000 : ℝ)
  | 8 => (10437203 / 500000000000 : ℝ)
  | 9 => (10625439 / 500000000000 : ℝ)
  | 10 => (21632001 / 1000000000000 : ℝ)
  | 11 => (5504451 / 250000000000 : ℝ)
  | 12 => (2801039 / 125000000000 : ℝ)
  | 13 => (456071 / 20000000000 : ℝ)
  | 14 => (4640709 / 200000000000 : ℝ)
  | 15 => (11804161 / 500000000000 : ℝ)
  | 16 => (12008953 / 500000000000 : ℝ)
  | 17 => (12216161 / 500000000000 : ℝ)
  | 18 => (4970319 / 200000000000 : ℝ)
  | 19 => (25275749 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch010Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (18367129 / 1000000000000 : ℝ)
  | 1 => (3742357 / 200000000000 : ℝ)
  | 2 => (3812181 / 200000000000 : ℝ)
  | 3 => (9707257 / 500000000000 : ℝ)
  | 4 => (19772643 / 1000000000000 : ℝ)
  | 5 => (5033829 / 250000000000 : ℝ)
  | 6 => (10251281 / 500000000000 : ℝ)
  | 7 => (20874407 / 1000000000000 : ℝ)
  | 8 => (21250879 / 1000000000000 : ℝ)
  | 9 => (10816001 / 500000000000 : ℝ)
  | 10 => (4403561 / 200000000000 : ℝ)
  | 11 => (22408313 / 1000000000000 : ℝ)
  | 12 => (22803551 / 1000000000000 : ℝ)
  | 13 => (11601773 / 500000000000 : ℝ)
  | 14 => (23608323 / 1000000000000 : ℝ)
  | 15 => (24017907 / 1000000000000 : ℝ)
  | 16 => (24432323 / 1000000000000 : ℝ)
  | 17 => (6212899 / 250000000000 : ℝ)
  | 18 => (101103 / 4000000000 : ℝ)
  | 19 => (25704811 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch010Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((200 : ℝ) + (j.val : ℝ)) / 1600)
      (((200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch010Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch010Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((200 : ℝ) + (j.val : ℝ)) / 1600)
    (((200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch010Neg25WeightLower j.val) (hpThetaShiftTwoBatch010Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch010Neg25WeightLower, hpThetaShiftTwoBatch010Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch010Neg25_integral_bounds :
    (406080113 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (10 / 80 : ℝ) ((10 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (418015029 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch010Lower hpThetaJensenCellsBatch010Upper
    hpThetaShiftTwoBatch010Neg25WeightLower hpThetaShiftTwoBatch010Neg25WeightUpper hpThetaJensenCellsBatch010_bounds hpThetaShiftTwoBatch010Neg25_weight_bounds
  have hl : (406080113 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch010Lower j * hpThetaShiftTwoBatch010Neg25WeightLower j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftTwoBatch010Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftTwoBatch010Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch010Lower j * hpThetaShiftTwoBatch010Neg25WeightUpper j)
        (hpThetaJensenCellsBatch010Upper j * hpThetaShiftTwoBatch010Neg25WeightUpper j) / 1600) ≤ (418015029 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch010Lower, hpThetaJensenCellsBatch010Upper,
      hpThetaShiftTwoBatch010Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (200 : ℝ) / 1600 = 10 / 80 by norm_num,
    show ((200 : ℝ) + 20) / 1600 = (10 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch010Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch010Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch010Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch010Neg25_integral_bounds
end HodgeProofHP
