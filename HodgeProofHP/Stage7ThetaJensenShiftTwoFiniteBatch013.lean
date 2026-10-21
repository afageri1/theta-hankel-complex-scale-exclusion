/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch013

/-! Exact signed weight and batch integral certificates, batch 13 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch013Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (813331 / 40000000000 : ℝ)
  | 1 => (20414021 / 1000000000000 : ℝ)
  | 2 => (4098239 / 200000000000 : ℝ)
  | 3 => (20564709 / 1000000000000 : ℝ)
  | 4 => (825379 / 40000000000 : ℝ)
  | 5 => (5175101 / 250000000000 : ℝ)
  | 6 => (2595301 / 125000000000 : ℝ)
  | 7 => (10410199 / 500000000000 : ℝ)
  | 8 => (10437141 / 500000000000 : ℝ)
  | 9 => (5230993 / 250000000000 : ℝ)
  | 10 => (33551 / 1600000000 : ℝ)
  | 11 => (26263 / 1250000000 : ℝ)
  | 12 => (4209391 / 200000000000 : ℝ)
  | 13 => (21078949 / 1000000000000 : ℝ)
  | 14 => (21106287 / 1000000000000 : ℝ)
  | 15 => (5282219 / 250000000000 : ℝ)
  | 16 => (21146623 / 1000000000000 : ℝ)
  | 17 => (10579717 / 500000000000 : ℝ)
  | 18 => (10583607 / 500000000000 : ℝ)
  | 19 => (21167299 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch013Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (10207011 / 500000000000 : ℝ)
  | 1 => (5122799 / 250000000000 : ℝ)
  | 2 => (2056471 / 100000000000 : ℝ)
  | 3 => (5158619 / 250000000000 : ℝ)
  | 4 => (4140081 / 200000000000 : ℝ)
  | 5 => (20762409 / 1000000000000 : ℝ)
  | 6 => (20820399 / 1000000000000 : ℝ)
  | 7 => (20874283 / 1000000000000 : ℝ)
  | 8 => (20923973 / 1000000000000 : ℝ)
  | 9 => (655293 / 31250000000 : ℝ)
  | 10 => (21010401 / 1000000000000 : ℝ)
  | 11 => (5261739 / 250000000000 : ℝ)
  | 12 => (421579 / 20000000000 : ℝ)
  | 13 => (1319143 / 62500000000 : ℝ)
  | 14 => (21128877 / 1000000000000 : ℝ)
  | 15 => (20651 / 976562500 : ℝ)
  | 16 => (4231887 / 200000000000 : ℝ)
  | 17 => (4233443 / 200000000000 : ℝ)
  | 18 => (5292467 / 250000000000 : ℝ)
  | 19 => (10584937 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch013Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((260 : ℝ) + (j.val : ℝ)) / 1600)
      (((260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch013Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch013Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((260 : ℝ) + (j.val : ℝ)) / 1600)
    (((260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch013Neg100WeightLower j.val) (hpThetaShiftTwoBatch013Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch013Neg100WeightLower, hpThetaShiftTwoBatch013Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch013Neg100_integral_bounds :
    (35373313 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (358582733 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch013Lower hpThetaJensenCellsBatch013Upper
    hpThetaShiftTwoBatch013Neg100WeightLower hpThetaShiftTwoBatch013Neg100WeightUpper hpThetaJensenCellsBatch013_bounds hpThetaShiftTwoBatch013Neg100_weight_bounds
  have hl : (35373313 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch013Lower j * hpThetaShiftTwoBatch013Neg100WeightLower j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftTwoBatch013Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftTwoBatch013Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch013Lower j * hpThetaShiftTwoBatch013Neg100WeightUpper j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftTwoBatch013Neg100WeightUpper j) / 1600) ≤ (358582733 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftTwoBatch013Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (260 : ℝ) / 1600 = 13 / 80 by norm_num,
    show ((260 : ℝ) + 20) / 1600 = (13 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch013Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (15869193 / 500000000000 : ℝ)
  | 1 => (8012551 / 250000000000 : ℝ)
  | 2 => (32361881 / 1000000000000 : ℝ)
  | 3 => (16336679 / 500000000000 : ℝ)
  | 4 => (8246143 / 250000000000 : ℝ)
  | 5 => (33295461 / 1000000000000 : ℝ)
  | 6 => (16802981 / 500000000000 : ℝ)
  | 7 => (33916011 / 1000000000000 : ℝ)
  | 8 => (34225541 / 1000000000000 : ℝ)
  | 9 => (34534489 / 1000000000000 : ℝ)
  | 10 => (17421393 / 500000000000 : ℝ)
  | 11 => (17575183 / 500000000000 : ℝ)
  | 12 => (886429 / 25000000000 : ℝ)
  | 13 => (35763099 / 1000000000000 : ℝ)
  | 14 => (18034057 / 500000000000 : ℝ)
  | 15 => (9093033 / 250000000000 : ℝ)
  | 16 => (36675083 / 1000000000000 : ℝ)
  | 17 => (7395379 / 200000000000 : ℝ)
  | 18 => (37277493 / 1000000000000 : ℝ)
  | 19 => (9394201 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch013Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (6410041 / 200000000000 : ℝ)
  | 1 => (16180941 / 500000000000 : ℝ)
  | 2 => (32673359 / 1000000000000 : ℝ)
  | 3 => (32984573 / 1000000000000 : ℝ)
  | 4 => (16647731 / 500000000000 : ℝ)
  | 5 => (33605963 / 1000000000000 : ℝ)
  | 6 => (8479003 / 250000000000 : ℝ)
  | 7 => (17112771 / 500000000000 : ℝ)
  | 8 => (3453449 / 100000000000 : ℝ)
  | 9 => (34842787 / 1000000000000 : ℝ)
  | 10 => (35150367 / 1000000000000 : ℝ)
  | 11 => (35457161 / 1000000000000 : ℝ)
  | 12 => (357631 / 10000000000 : ℝ)
  | 13 => (7213623 / 200000000000 : ℝ)
  | 14 => (36372133 / 1000000000000 : ℝ)
  | 15 => (9168771 / 250000000000 : ℝ)
  | 16 => (144441 / 3906250000 : ℝ)
  | 17 => (18638747 / 500000000000 : ℝ)
  | 18 => (7515361 / 200000000000 : ℝ)
  | 19 => (18937377 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch013Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((260 : ℝ) + (j.val : ℝ)) / 1600)
      (((260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch013Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch013Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((260 : ℝ) + (j.val : ℝ)) / 1600)
    (((260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch013Neg65WeightLower j.val) (hpThetaShiftTwoBatch013Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch013Neg65WeightLower, hpThetaShiftTwoBatch013Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch013Neg65_integral_bounds :
    (587346459 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (599458127 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch013Lower hpThetaJensenCellsBatch013Upper
    hpThetaShiftTwoBatch013Neg65WeightLower hpThetaShiftTwoBatch013Neg65WeightUpper hpThetaJensenCellsBatch013_bounds hpThetaShiftTwoBatch013Neg65_weight_bounds
  have hl : (587346459 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch013Lower j * hpThetaShiftTwoBatch013Neg65WeightLower j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftTwoBatch013Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftTwoBatch013Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch013Lower j * hpThetaShiftTwoBatch013Neg65WeightUpper j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftTwoBatch013Neg65WeightUpper j) / 1600) ≤ (599458127 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftTwoBatch013Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (260 : ℝ) / 1600 = 13 / 80 by norm_num,
    show ((260 : ℝ) + 20) / 1600 = (13 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch013Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (39112579 / 1000000000000 : ℝ)
  | 1 => (2473899 / 62500000000 : ℝ)
  | 2 => (20027343 / 500000000000 : ℝ)
  | 3 => (40529453 / 1000000000000 : ℝ)
  | 4 => (41006653 / 1000000000000 : ℝ)
  | 5 => (8297251 / 200000000000 : ℝ)
  | 6 => (1678729 / 40000000000 : ℝ)
  | 7 => (2653283 / 62500000000 : ℝ)
  | 8 => (4293913 / 100000000000 : ℝ)
  | 9 => (8685599 / 200000000000 : ℝ)
  | 10 => (21959543 / 500000000000 : ℝ)
  | 11 => (2775773 / 62500000000 : ℝ)
  | 12 => (22453901 / 500000000000 : ℝ)
  | 13 => (45405349 / 1000000000000 : ℝ)
  | 14 => (45904969 / 1000000000000 : ℝ)
  | 15 => (1450207 / 31250000000 : ℝ)
  | 16 => (732973 / 15625000000 : ℝ)
  | 17 => (47415871 / 1000000000000 : ℝ)
  | 18 => (47923379 / 1000000000000 : ℝ)
  | 19 => (48432753 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch013Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (7916477 / 200000000000 : ℝ)
  | 1 => (40054687 / 1000000000000 : ℝ)
  | 2 => (20264727 / 500000000000 : ℝ)
  | 3 => (20503327 / 500000000000 : ℝ)
  | 4 => (2592891 / 62500000000 : ℝ)
  | 5 => (20984113 / 500000000000 : ℝ)
  | 6 => (42452529 / 1000000000000 : ℝ)
  | 7 => (42939131 / 1000000000000 : ℝ)
  | 8 => (10856999 / 250000000000 : ℝ)
  | 9 => (43919087 / 1000000000000 : ℝ)
  | 10 => (44412369 / 1000000000000 : ℝ)
  | 11 => (44907803 / 1000000000000 : ℝ)
  | 12 => (908107 / 20000000000 : ℝ)
  | 13 => (4590497 / 100000000000 : ℝ)
  | 14 => (371253 / 8000000000 : ℝ)
  | 15 => (46910273 / 1000000000000 : ℝ)
  | 16 => (740873 / 15625000000 : ℝ)
  | 17 => (2396169 / 50000000000 : ℝ)
  | 18 => (24216377 / 500000000000 : ℝ)
  | 19 => (48943949 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch013Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((260 : ℝ) + (j.val : ℝ)) / 1600)
      (((260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch013Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch013Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((260 : ℝ) + (j.val : ℝ)) / 1600)
    (((260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch013Neg45WeightLower j.val) (hpThetaShiftTwoBatch013Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch013Neg45WeightLower, hpThetaShiftTwoBatch013Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch013Neg45_integral_bounds :
    (46263607 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (75727689 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch013Lower hpThetaJensenCellsBatch013Upper
    hpThetaShiftTwoBatch013Neg45WeightLower hpThetaShiftTwoBatch013Neg45WeightUpper hpThetaJensenCellsBatch013_bounds hpThetaShiftTwoBatch013Neg45_weight_bounds
  have hl : (46263607 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch013Lower j * hpThetaShiftTwoBatch013Neg45WeightLower j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftTwoBatch013Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftTwoBatch013Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch013Lower j * hpThetaShiftTwoBatch013Neg45WeightUpper j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftTwoBatch013Neg45WeightUpper j) / 1600) ≤ (75727689 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftTwoBatch013Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (260 : ℝ) / 1600 = 13 / 80 by norm_num,
    show ((260 : ℝ) + 20) / 1600 = (13 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch013Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (11783877 / 250000000000 : ℝ)
  | 1 => (186653 / 3906250000 : ℝ)
  | 2 => (48436487 / 1000000000000 : ℝ)
  | 3 => (12273869 / 250000000000 : ℝ)
  | 4 => (3110009 / 62500000000 : ℝ)
  | 5 => (100861 / 2000000000 : ℝ)
  | 6 => (25553277 / 500000000000 : ℝ)
  | 7 => (10357663 / 200000000000 : ℝ)
  | 8 => (5247579 / 100000000000 : ℝ)
  | 9 => (53168987 / 1000000000000 : ℝ)
  | 10 => (53867913 / 1000000000000 : ℝ)
  | 11 => (2182903 / 40000000000 : ℝ)
  | 12 => (2764149 / 50000000000 : ℝ)
  | 13 => (55999133 / 1000000000000 : ℝ)
  | 14 => (709013 / 12500000000 : ℝ)
  | 15 => (28724353 / 500000000000 : ℝ)
  | 16 => (11636427 / 200000000000 : ℝ)
  | 17 => (14730333 / 250000000000 : ℝ)
  | 18 => (59666299 / 1000000000000 : ℝ)
  | 19 => (60417041 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch013Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (47783169 / 1000000000000 : ℝ)
  | 1 => (6054561 / 125000000000 : ℝ)
  | 2 => (49095477 / 1000000000000 : ℝ)
  | 3 => (9952029 / 200000000000 : ℝ)
  | 4 => (50430501 / 1000000000000 : ℝ)
  | 5 => (10221311 / 200000000000 : ℝ)
  | 6 => (12947079 / 250000000000 : ℝ)
  | 7 => (52475791 / 1000000000000 : ℝ)
  | 8 => (13292247 / 250000000000 : ℝ)
  | 9 => (26933957 / 500000000000 : ℝ)
  | 10 => (1705393 / 31250000000 : ℝ)
  | 11 => (55282981 / 1000000000000 : ℝ)
  | 12 => (27999567 / 500000000000 : ℝ)
  | 13 => (56721041 / 1000000000000 : ℝ)
  | 14 => (57448707 / 1000000000000 : ℝ)
  | 15 => (7272767 / 125000000000 : ℝ)
  | 16 => (58921333 / 1000000000000 : ℝ)
  | 17 => (596663 / 10000000000 : ℝ)
  | 18 => (30208521 / 500000000000 : ℝ)
  | 19 => (1529339 / 25000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch013Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((260 : ℝ) + (j.val : ℝ)) / 1600)
      (((260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch013Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch013Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((260 : ℝ) + (j.val : ℝ)) / 1600)
    (((260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch013Neg25WeightLower j.val) (hpThetaShiftTwoBatch013Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch013Neg25WeightLower, hpThetaShiftTwoBatch013Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch013Neg25_integral_bounds :
    (226953049 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (13 / 80 : ℝ) ((13 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (11630357 / 12500000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch013Lower hpThetaJensenCellsBatch013Upper
    hpThetaShiftTwoBatch013Neg25WeightLower hpThetaShiftTwoBatch013Neg25WeightUpper hpThetaJensenCellsBatch013_bounds hpThetaShiftTwoBatch013Neg25_weight_bounds
  have hl : (226953049 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch013Lower j * hpThetaShiftTwoBatch013Neg25WeightLower j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftTwoBatch013Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftTwoBatch013Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch013Lower j * hpThetaShiftTwoBatch013Neg25WeightUpper j)
        (hpThetaJensenCellsBatch013Upper j * hpThetaShiftTwoBatch013Neg25WeightUpper j) / 1600) ≤ (11630357 / 12500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch013Lower, hpThetaJensenCellsBatch013Upper,
      hpThetaShiftTwoBatch013Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (260 : ℝ) / 1600 = 13 / 80 by norm_num,
    show ((260 : ℝ) + 20) / 1600 = (13 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch013Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch013Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch013Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch013Neg25_integral_bounds
end HodgeProofHP
