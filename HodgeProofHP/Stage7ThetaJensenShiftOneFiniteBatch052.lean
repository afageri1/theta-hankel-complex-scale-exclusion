/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch052

/-! Exact signed weight and batch integral certificates, batch 52 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch052Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4417771658973 / 1000000000000 : ℝ)
  | 1 => (-2236209254089 / 500000000000 : ℝ)
  | 2 => (-2263790535653 / 500000000000 : ℝ)
  | 3 => (-2291631575883 / 500000000000 : ℝ)
  | 4 => (-4639468574771 / 1000000000000 : ℝ)
  | 5 => (-2348100593721 / 500000000000 : ℝ)
  | 6 => (-4753464858897 / 1000000000000 : ℝ)
  | 7 => (-96225269607 / 20000000000 : ℝ)
  | 8 => (-2434800482601 / 500000000000 : ℝ)
  | 9 => (-4928481249143 / 1000000000000 : ℝ)
  | 10 => (-2493954145121 / 500000000000 : ℝ)
  | 11 => (-2523943034523 / 500000000000 : ℝ)
  | 12 => (-5108418588679 / 1000000000000 : ℝ)
  | 13 => (-1033901974987 / 200000000000 : ℝ)
  | 14 => (-5231163976377 / 1000000000000 : ℝ)
  | 15 => (-1058676992887 / 200000000000 : ℝ)
  | 16 => (-41845132293 / 7812500000 : ℝ)
  | 17 => (-67744300013 / 12500000000 : ℝ)
  | 18 => (-5483490307663 / 1000000000000 : ℝ)
  | 19 => (-22192080069 / 4000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch052Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4363636742001 / 1000000000000 : ℝ)
  | 1 => (-1104442914743 / 250000000000 : ℝ)
  | 2 => (-4472418508177 / 1000000000000 : ℝ)
  | 3 => (-905516214261 / 200000000000 : ℝ)
  | 4 => (-916652630353 / 200000000000 : ℝ)
  | 5 => (-463946857477 / 100000000000 : ℝ)
  | 6 => (-4696201187441 / 1000000000000 : ℝ)
  | 7 => (-297091553681 / 62500000000 : ℝ)
  | 8 => (-4811263480349 / 1000000000000 : ℝ)
  | 9 => (-4869600965201 / 1000000000000 : ℝ)
  | 10 => (-2464240624571 / 500000000000 : ℝ)
  | 11 => (-4987908290241 / 1000000000000 : ℝ)
  | 12 => (-1009577213809 / 200000000000 : ℝ)
  | 13 => (-2554209294339 / 500000000000 : ℝ)
  | 14 => (-2584754937467 / 500000000000 : ℝ)
  | 15 => (-653895497047 / 125000000000 : ℝ)
  | 16 => (-2646692482217 / 500000000000 : ℝ)
  | 17 => (-5356176933503 / 1000000000000 : ℝ)
  | 18 => (-5419544001039 / 1000000000000 : ℝ)
  | 19 => (-2741745153831 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch052Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1040 : ℝ) + (j.val : ℝ)) / 1600)
      (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch052Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch052Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1040 : ℝ) + (j.val : ℝ)) / 1600)
    (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch052Neg100WeightLower j.val) (hpThetaShiftOneBatch052Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch052Neg100WeightLower, hpThetaShiftOneBatch052Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch052Neg100_integral_bounds :
    (-176061533209 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-681910991031 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1040 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch052Lower hpThetaJensenCellsBatch052Upper
    hpThetaShiftOneBatch052Neg100WeightLower hpThetaShiftOneBatch052Neg100WeightUpper hpThetaJensenCellsBatch052_bounds hpThetaShiftOneBatch052Neg100_weight_bounds
  have hl : (-176061533209 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch052Lower j * hpThetaShiftOneBatch052Neg100WeightLower j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftOneBatch052Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftOneBatch052Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch052Lower j * hpThetaShiftOneBatch052Neg100WeightUpper j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftOneBatch052Neg100WeightUpper j) / 1600) ≤ (-681910991031 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftOneBatch052Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1040 : ℝ) / 1600 = 52 / 80 by norm_num,
    show ((1040 : ℝ) + 20) / 1600 = (52 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch052Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (31472084129 / 500000000000 : ℝ)
  | 1 => (5796278959 / 100000000000 : ℝ)
  | 2 => (1653104369 / 31250000000 : ℝ)
  | 3 => (23876519081 / 500000000000 : ℝ)
  | 4 => (5315387343 / 125000000000 : ℝ)
  | 5 => (37208730457 / 1000000000000 : ℝ)
  | 6 => (7952284249 / 250000000000 : ℝ)
  | 7 => (13161758411 / 500000000000 : ℝ)
  | 8 => (10375531569 / 500000000000 : ℝ)
  | 9 => (15090963861 / 1000000000000 : ℝ)
  | 10 => (2335600401 / 250000000000 : ℝ)
  | 11 => (700910729 / 200000000000 : ℝ)
  | 12 => (-1211704049 / 500000000000 : ℝ)
  | 13 => (-2110579271 / 250000000000 : ℝ)
  | 14 => (-2910602437 / 200000000000 : ℝ)
  | 15 => (-2594542213 / 125000000000 : ℝ)
  | 16 => (-13526571701 / 500000000000 : ℝ)
  | 17 => (-16722142261 / 500000000000 : ℝ)
  | 18 => (-19965310909 / 500000000000 : ℝ)
  | 19 => (-46513021577 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch052Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (16961062857 / 250000000000 : ℝ)
  | 1 => (62944168259 / 1000000000000 : ℝ)
  | 2 => (57962789591 / 1000000000000 : ℝ)
  | 3 => (52899339809 / 1000000000000 : ℝ)
  | 4 => (47753038163 / 1000000000000 : ℝ)
  | 5 => (8504619749 / 200000000000 : ℝ)
  | 6 => (18604365229 / 500000000000 : ℝ)
  | 7 => (31809136997 / 1000000000000 : ℝ)
  | 8 => (26323516823 / 1000000000000 : ℝ)
  | 9 => (20751063139 / 1000000000000 : ℝ)
  | 10 => (7545481931 / 500000000000 : ℝ)
  | 11 => (1868480321 / 200000000000 : ℝ)
  | 12 => (1752276823 / 500000000000 : ℝ)
  | 13 => (-2423408097 / 1000000000000 : ℝ)
  | 14 => (-8442317083 / 1000000000000 : ℝ)
  | 15 => (-1819126523 / 125000000000 : ℝ)
  | 16 => (-20756337703 / 1000000000000 : ℝ)
  | 17 => (-27053143401 / 1000000000000 : ℝ)
  | 18 => (-33444284521 / 1000000000000 : ℝ)
  | 19 => (-39930621817 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch052Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1040 : ℝ) + (j.val : ℝ)) / 1600)
      (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch052Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch052Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1040 : ℝ) + (j.val : ℝ)) / 1600)
    (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch052Neg65WeightLower j.val) (hpThetaShiftOneBatch052Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch052Neg65WeightLower, hpThetaShiftOneBatch052Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch052Neg65_integral_bounds :
    (223055287 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (334383843 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1040 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch052Lower hpThetaJensenCellsBatch052Upper
    hpThetaShiftOneBatch052Neg65WeightLower hpThetaShiftOneBatch052Neg65WeightUpper hpThetaJensenCellsBatch052_bounds hpThetaShiftOneBatch052Neg65_weight_bounds
  have hl : (223055287 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch052Lower j * hpThetaShiftOneBatch052Neg65WeightLower j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftOneBatch052Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftOneBatch052Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch052Lower j * hpThetaShiftOneBatch052Neg65WeightUpper j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftOneBatch052Neg65WeightUpper j) / 1600) ≤ (334383843 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftOneBatch052Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1040 : ℝ) / 1600 = 52 / 80 by norm_num,
    show ((1040 : ℝ) + 20) / 1600 = (52 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch052Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (229058123511 / 1000000000000 : ℝ)
  | 1 => (28833277951 / 125000000000 : ℝ)
  | 2 => (232275656023 / 1000000000000 : ℝ)
  | 3 => (233886340621 / 1000000000000 : ℝ)
  | 4 => (235498196409 / 1000000000000 : ℝ)
  | 5 => (59277785381 / 250000000000 : ℝ)
  | 6 => (14920318327 / 62500000000 : ℝ)
  | 7 => (9613598717 / 40000000000 : ℝ)
  | 8 => (241955681113 / 1000000000000 : ℝ)
  | 9 => (243572147417 / 1000000000000 : ℝ)
  | 10 => (245189280569 / 1000000000000 : ℝ)
  | 11 => (61701748351 / 250000000000 : ℝ)
  | 12 => (248425197857 / 1000000000000 : ℝ)
  | 13 => (250043804953 / 1000000000000 : ℝ)
  | 14 => (251662724807 / 1000000000000 : ℝ)
  | 15 => (253281866617 / 1000000000000 : ℝ)
  | 16 => (12745056933 / 50000000000 : ℝ)
  | 17 => (256520448283 / 1000000000000 : ℝ)
  | 18 => (258139701903 / 1000000000000 : ℝ)
  | 19 => (259758804997 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch052Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (230666223609 / 1000000000000 : ℝ)
  | 1 => (29034457003 / 125000000000 : ℝ)
  | 2 => (116943170311 / 500000000000 : ℝ)
  | 3 => (23549819641 / 100000000000 : ℝ)
  | 4 => (9484445661 / 40000000000 : ℝ)
  | 5 => (238725093233 / 1000000000000 : ℝ)
  | 6 => (120169983963 / 500000000000 : ℝ)
  | 7 => (120977840557 / 500000000000 : ℝ)
  | 8 => (121786073709 / 500000000000 : ℝ)
  | 9 => (24518928057 / 100000000000 : ℝ)
  | 10 => (49361398681 / 200000000000 : ℝ)
  | 11 => (124212598929 / 500000000000 : ℝ)
  | 12 => (125021902477 / 500000000000 : ℝ)
  | 13 => (31457840601 / 125000000000 : ℝ)
  | 14 => (126640933309 / 500000000000 : ℝ)
  | 15 => (254901138661 / 1000000000000 : ℝ)
  | 16 => (64130112071 / 250000000000 : ℝ)
  | 17 => (16133731369 / 62500000000 : ℝ)
  | 18 => (129879402499 / 500000000000 : ℝ)
  | 19 => (261377662103 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch052Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1040 : ℝ) + (j.val : ℝ)) / 1600)
      (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch052Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch052Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1040 : ℝ) + (j.val : ℝ)) / 1600)
    (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch052Neg40WeightLower j.val) (hpThetaShiftOneBatch052Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch052Neg40WeightLower, hpThetaShiftOneBatch052Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch052Neg40_integral_bounds :
    (2126619241 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (8737756579 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1040 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch052Lower hpThetaJensenCellsBatch052Upper
    hpThetaShiftOneBatch052Neg40WeightLower hpThetaShiftOneBatch052Neg40WeightUpper hpThetaJensenCellsBatch052_bounds hpThetaShiftOneBatch052Neg40_weight_bounds
  have hl : (2126619241 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch052Lower j * hpThetaShiftOneBatch052Neg40WeightLower j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftOneBatch052Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftOneBatch052Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch052Lower j * hpThetaShiftOneBatch052Neg40WeightUpper j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftOneBatch052Neg40WeightUpper j) / 1600) ≤ (8737756579 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftOneBatch052Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1040 : ℝ) / 1600 = 52 / 80 by norm_num,
    show ((1040 : ℝ) + 20) / 1600 = (52 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch052Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-78827968937 / 1000000000000 : ℝ)
  | 1 => (-19667215151 / 250000000000 : ℝ)
  | 2 => (-78506185337 / 1000000000000 : ℝ)
  | 3 => (-78339927051 / 1000000000000 : ℝ)
  | 4 => (-78170069669 / 1000000000000 : ℝ)
  | 5 => (-77996597117 / 1000000000000 : ℝ)
  | 6 => (-7781949333 / 100000000000 : ℝ)
  | 7 => (-15527748449 / 200000000000 : ℝ)
  | 8 => (-18909748 / 244140625 : ℝ)
  | 9 => (-19316558493 / 250000000000 : ℝ)
  | 10 => (-77074444697 / 1000000000000 : ℝ)
  | 11 => (-76878943949 / 1000000000000 : ℝ)
  | 12 => (-38339857853 / 500000000000 : ℝ)
  | 13 => (-1529534879 / 20000000000 : ℝ)
  | 14 => (-3050800507 / 40000000000 : ℝ)
  | 15 => (-76059505883 / 1000000000000 : ℝ)
  | 16 => (-18961301897 / 250000000000 : ℝ)
  | 17 => (-75627101811 / 1000000000000 : ℝ)
  | 18 => (-37702586293 / 500000000000 : ℝ)
  | 19 => (-37589701979 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch052Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-78668860603 / 1000000000000 : ℝ)
  | 1 => (-9813273167 / 125000000000 : ℝ)
  | 2 => (-1566798541 / 20000000000 : ℝ)
  | 3 => (-19542517417 / 250000000000 : ℝ)
  | 4 => (-19499149279 / 250000000000 : ℝ)
  | 5 => (-77819493329 / 1000000000000 : ℝ)
  | 6 => (-19409685561 / 250000000000 : ℝ)
  | 7 => (-77454327807 / 1000000000000 : ℝ)
  | 8 => (-77266233971 / 1000000000000 : ℝ)
  | 9 => (-9634305587 / 125000000000 : ℝ)
  | 10 => (-19219735987 / 250000000000 : ℝ)
  | 11 => (-15335943141 / 200000000000 : ℝ)
  | 12 => (-76476743949 / 1000000000000 : ℝ)
  | 13 => (-38135006337 / 500000000000 : ℝ)
  | 14 => (-38029752941 / 500000000000 : ℝ)
  | 15 => (-75845207587 / 1000000000000 : ℝ)
  | 16 => (-7562710181 / 100000000000 : ℝ)
  | 17 => (-15081034517 / 200000000000 : ℝ)
  | 18 => (-75179403957 / 1000000000000 : ℝ)
  | 19 => (-3747488999 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch052Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1040 : ℝ) + (j.val : ℝ)) / 1600)
      (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch052Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch052Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1040 : ℝ) + (j.val : ℝ)) / 1600)
    (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch052Neg20WeightLower j.val) (hpThetaShiftOneBatch052Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch052Neg20WeightLower, hpThetaShiftOneBatch052Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch052Neg20_integral_bounds :
    (-1374180779 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-10746590633 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1040 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch052Lower hpThetaJensenCellsBatch052Upper
    hpThetaShiftOneBatch052Neg20WeightLower hpThetaShiftOneBatch052Neg20WeightUpper hpThetaJensenCellsBatch052_bounds hpThetaShiftOneBatch052Neg20_weight_bounds
  have hl : (-1374180779 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch052Lower j * hpThetaShiftOneBatch052Neg20WeightLower j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftOneBatch052Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftOneBatch052Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch052Lower j * hpThetaShiftOneBatch052Neg20WeightUpper j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftOneBatch052Neg20WeightUpper j) / 1600) ≤ (-10746590633 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftOneBatch052Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1040 : ℝ) / 1600 = 52 / 80 by norm_num,
    show ((1040 : ℝ) + 20) / 1600 = (52 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch052Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch052Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch052Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch052Neg20_integral_bounds
end HodgeProofHP
