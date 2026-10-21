/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch052

/-! Exact signed weight and batch integral certificates, batch 52 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch052Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1587509473 / 31250000000 : ℝ)
  | 1 => (-51753740249 / 1000000000000 : ℝ)
  | 2 => (-10544019667 / 200000000000 : ℝ)
  | 3 => (-53699515109 / 1000000000000 : ℝ)
  | 4 => (-5469212947 / 100000000000 : ℝ)
  | 5 => (-13924520377 / 250000000000 : ℝ)
  | 6 => (-56717512509 / 1000000000000 : ℝ)
  | 7 => (-57750564971 / 1000000000000 : ℝ)
  | 8 => (-29398691303 / 500000000000 : ℝ)
  | 9 => (-59858110349 / 1000000000000 : ℝ)
  | 10 => (-60932894371 / 1000000000000 : ℝ)
  | 11 => (-387636763 / 6250000000 : ℝ)
  | 12 => (-31562611069 / 500000000000 : ℝ)
  | 13 => (-32121532231 / 500000000000 : ℝ)
  | 14 => (-65375560237 / 1000000000000 : ℝ)
  | 15 => (-16630715481 / 250000000000 : ℝ)
  | 16 => (-67685123267 / 1000000000000 : ℝ)
  | 17 => (-8607812413 / 125000000000 : ℝ)
  | 18 => (-35027573187 / 500000000000 : ℝ)
  | 19 => (-71263222127 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch052Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-9971930091 / 200000000000 : ℝ)
  | 1 => (-10160060627 / 200000000000 : ℝ)
  | 2 => (-6469217531 / 125000000000 : ℝ)
  | 3 => (-26360049167 / 500000000000 : ℝ)
  | 4 => (-13424878777 / 250000000000 : ℝ)
  | 5 => (-54692129469 / 1000000000000 : ℝ)
  | 6 => (-55698081507 / 1000000000000 : ℝ)
  | 7 => (-14179378127 / 250000000000 : ℝ)
  | 8 => (-5775056497 / 100000000000 : ℝ)
  | 9 => (-11759476521 / 200000000000 : ℝ)
  | 10 => (-14964527587 / 250000000000 : ℝ)
  | 11 => (-6093289437 / 100000000000 : ℝ)
  | 12 => (-62021882079 / 1000000000000 : ℝ)
  | 13 => (-63125222137 / 1000000000000 : ℝ)
  | 14 => (-64243064461 / 1000000000000 : ℝ)
  | 15 => (-16343890059 / 250000000000 : ℝ)
  | 16 => (-66522861923 / 1000000000000 : ℝ)
  | 17 => (-33842561633 / 500000000000 : ℝ)
  | 18 => (-68862499303 / 1000000000000 : ℝ)
  | 19 => (-70055146373 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch052Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1040 : ℝ) + (j.val : ℝ)) / 1600)
      (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch052Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch052Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1040 : ℝ) + (j.val : ℝ)) / 1600)
    (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch052Neg100WeightLower j.val) (hpThetaShiftTwoBatch052Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch052Neg100WeightLower, hpThetaShiftTwoBatch052Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch052Neg100_integral_bounds :
    (-536039759 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-8256285579 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1040 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch052Lower hpThetaJensenCellsBatch052Upper
    hpThetaShiftTwoBatch052Neg100WeightLower hpThetaShiftTwoBatch052Neg100WeightUpper hpThetaJensenCellsBatch052_bounds hpThetaShiftTwoBatch052Neg100_weight_bounds
  have hl : (-536039759 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch052Lower j * hpThetaShiftTwoBatch052Neg100WeightLower j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftTwoBatch052Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftTwoBatch052Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch052Lower j * hpThetaShiftTwoBatch052Neg100WeightUpper j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftTwoBatch052Neg100WeightUpper j) / 1600) ≤ (-8256285579 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftTwoBatch052Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1040 : ℝ) / 1600 = 52 / 80 by norm_num,
    show ((1040 : ℝ) + 20) / 1600 = (52 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch052Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (10463855151 / 1000000000000 : ℝ)
  | 1 => (2621803473 / 250000000000 : ℝ)
  | 2 => (10509592677 / 1000000000000 : ℝ)
  | 3 => (10530971973 / 1000000000000 : ℝ)
  | 4 => (10551332021 / 1000000000000 : ℝ)
  | 5 => (10570652841 / 1000000000000 : ℝ)
  | 6 => (661807139 / 62500000000 : ℝ)
  | 7 => (2121219147 / 200000000000 : ℝ)
  | 8 => (1062217671 / 100000000000 : ℝ)
  | 9 => (8509709 / 800000000 : ℝ)
  | 10 => (5325476613 / 500000000000 : ℝ)
  | 11 => (5206839 / 488281250 : ℝ)
  | 12 => (1334384223 / 125000000000 : ℝ)
  | 13 => (66783337 / 6250000000 : ℝ)
  | 14 => (5347182299 / 500000000000 : ℝ)
  | 15 => (10702143489 / 1000000000000 : ℝ)
  | 16 => (1338581003 / 125000000000 : ℝ)
  | 17 => (10713855383 / 1000000000000 : ℝ)
  | 18 => (10717742499 / 1000000000000 : ℝ)
  | 19 => (2144057211 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch052Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (10487213893 / 1000000000000 : ℝ)
  | 1 => (5254796339 / 500000000000 : ℝ)
  | 2 => (5265485987 / 500000000000 : ℝ)
  | 3 => (5275666011 / 500000000000 : ℝ)
  | 4 => (5285326421 / 500000000000 : ℝ)
  | 5 => (423556569 / 40000000000 : ℝ)
  | 6 => (1325761967 / 125000000000 : ℝ)
  | 7 => (10622176711 / 1000000000000 : ℝ)
  | 8 => (10637136251 / 1000000000000 : ℝ)
  | 9 => (10650953227 / 1000000000000 : ℝ)
  | 10 => (10663606273 / 1000000000000 : ℝ)
  | 11 => (2135014757 / 200000000000 : ℝ)
  | 12 => (10685333921 / 1000000000000 : ℝ)
  | 13 => (10694364599 / 1000000000000 : ℝ)
  | 14 => (1070214349 / 100000000000 : ℝ)
  | 15 => (428345921 / 40000000000 : ℝ)
  | 16 => (1339231923 / 125000000000 : ℝ)
  | 17 => (4287097 / 400000000 : ℝ)
  | 18 => (1340035757 / 125000000000 : ℝ)
  | 19 => (10721462481 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch052Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1040 : ℝ) + (j.val : ℝ)) / 1600)
      (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch052Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch052Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1040 : ℝ) + (j.val : ℝ)) / 1600)
    (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch052Neg65WeightLower j.val) (hpThetaShiftTwoBatch052Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch052Neg65WeightLower, hpThetaShiftTwoBatch052Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch052Neg65_integral_bounds :
    (1482334179 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (189313069 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1040 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch052Lower hpThetaJensenCellsBatch052Upper
    hpThetaShiftTwoBatch052Neg65WeightLower hpThetaShiftTwoBatch052Neg65WeightUpper hpThetaJensenCellsBatch052_bounds hpThetaShiftTwoBatch052Neg65_weight_bounds
  have hl : (1482334179 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch052Lower j * hpThetaShiftTwoBatch052Neg65WeightLower j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftTwoBatch052Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftTwoBatch052Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch052Lower j * hpThetaShiftTwoBatch052Neg65WeightUpper j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftTwoBatch052Neg65WeightUpper j) / 1600) ≤ (189313069 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftTwoBatch052Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1040 : ℝ) / 1600 = 52 / 80 by norm_num,
    show ((1040 : ℝ) + 20) / 1600 = (52 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch052Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4684974623 / 1000000000000 : ℝ)
  | 1 => (4749149619 / 1000000000000 : ℝ)
  | 2 => (2406863019 / 500000000000 : ℝ)
  | 3 => (975740709 / 200000000000 : ℝ)
  | 4 => (988816353 / 200000000000 : ℝ)
  | 5 => (1252465073 / 250000000000 : ℝ)
  | 6 => (5076038679 / 1000000000000 : ℝ)
  | 7 => (1285654111 / 250000000000 : ℝ)
  | 8 => (1041918613 / 200000000000 : ℝ)
  | 9 => (1055393597 / 200000000000 : ℝ)
  | 10 => (2672370303 / 500000000000 : ℝ)
  | 11 => (1353227573 / 250000000000 : ℝ)
  | 12 => (5481476367 / 1000000000000 : ℝ)
  | 13 => (1110087623 / 200000000000 : ℝ)
  | 14 => (280989739 / 50000000000 : ℝ)
  | 15 => (1137909113 / 200000000000 : ℝ)
  | 16 => (179990301 / 31250000000 : ℝ)
  | 17 => (5830226101 / 1000000000000 : ℝ)
  | 18 => (5901154049 / 1000000000000 : ℝ)
  | 19 => (5972472511 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch052Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (237457481 / 50000000000 : ℝ)
  | 1 => (4813726039 / 1000000000000 : ℝ)
  | 2 => (2439351773 / 500000000000 : ℝ)
  | 3 => (2472040883 / 500000000000 : ℝ)
  | 4 => (5009860293 / 1000000000000 : ℝ)
  | 5 => (126900967 / 25000000000 : ℝ)
  | 6 => (1028523289 / 200000000000 : ℝ)
  | 7 => (2604796533 / 500000000000 : ℝ)
  | 8 => (2638483993 / 500000000000 : ℝ)
  | 9 => (5344740607 / 1000000000000 : ℝ)
  | 10 => (5412910293 / 1000000000000 : ℝ)
  | 11 => (342592273 / 62500000000 : ℝ)
  | 12 => (1387609529 / 250000000000 : ℝ)
  | 13 => (5619794781 / 1000000000000 : ℝ)
  | 14 => (2844772783 / 500000000000 : ℝ)
  | 15 => (5759689633 / 1000000000000 : ℝ)
  | 16 => (2915113051 / 500000000000 : ℝ)
  | 17 => (118023081 / 20000000000 : ℝ)
  | 18 => (93319883 / 15625000000 : ℝ)
  | 19 => (295126 / 48828125 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch052Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1040 : ℝ) + (j.val : ℝ)) / 1600)
      (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch052Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch052Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1040 : ℝ) + (j.val : ℝ)) / 1600)
    (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch052Neg45WeightLower j.val) (hpThetaShiftTwoBatch052Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch052Neg45WeightLower, hpThetaShiftTwoBatch052Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch052Neg45_integral_bounds :
    (184644153 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (47707683 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1040 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch052Lower hpThetaJensenCellsBatch052Upper
    hpThetaShiftTwoBatch052Neg45WeightLower hpThetaShiftTwoBatch052Neg45WeightUpper hpThetaJensenCellsBatch052_bounds hpThetaShiftTwoBatch052Neg45_weight_bounds
  have hl : (184644153 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch052Lower j * hpThetaShiftTwoBatch052Neg45WeightLower j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftTwoBatch052Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftTwoBatch052Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch052Lower j * hpThetaShiftTwoBatch052Neg45WeightUpper j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftTwoBatch052Neg45WeightUpper j) / 1600) ≤ (47707683 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftTwoBatch052Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1040 : ℝ) / 1600 = 52 / 80 by norm_num,
    show ((1040 : ℝ) + 20) / 1600 = (52 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch052Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1831219273 / 500000000000 : ℝ)
  | 1 => (-1835155487 / 500000000000 : ℝ)
  | 2 => (-3678060393 / 1000000000000 : ℝ)
  | 3 => (-1842842663 / 500000000000 : ℝ)
  | 4 => (-3693184291 / 1000000000000 : ℝ)
  | 5 => (-3700555797 / 1000000000000 : ℝ)
  | 6 => (-926949587 / 250000000000 : ℝ)
  | 7 => (-3714910439 / 1000000000000 : ℝ)
  | 8 => (-2907727 / 781250000 : ℝ)
  | 9 => (-3728737193 / 1000000000000 : ℝ)
  | 10 => (-3735448813 / 1000000000000 : ℝ)
  | 11 => (-374202389 / 100000000000 : ℝ)
  | 12 => (-749692177 / 200000000000 : ℝ)
  | 13 => (-1877379127 / 500000000000 : ℝ)
  | 14 => (-940228611 / 250000000000 : ℝ)
  | 15 => (-3766927897 / 1000000000000 : ℝ)
  | 16 => (-3772797047 / 1000000000000 : ℝ)
  | 17 => (-3778520323 / 1000000000000 : ℝ)
  | 18 => (-756819229 / 200000000000 : ℝ)
  | 19 => (-236845183 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch052Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1827222289 / 500000000000 : ℝ)
  | 1 => (-732487709 / 200000000000 : ℝ)
  | 2 => (-3670310973 / 1000000000000 : ℝ)
  | 3 => (-459757549 / 125000000000 : ℝ)
  | 4 => (-147427413 / 40000000000 : ℝ)
  | 5 => (-369318429 / 100000000000 : ℝ)
  | 6 => (-925138949 / 250000000000 : ℝ)
  | 7 => (-3707798347 / 1000000000000 : ℝ)
  | 8 => (-1857455219 / 500000000000 : ℝ)
  | 9 => (-3721890559 / 1000000000000 : ℝ)
  | 10 => (-466092149 / 125000000000 : ℝ)
  | 11 => (-933862203 / 250000000000 : ℝ)
  | 12 => (-3742023889 / 1000000000000 : ℝ)
  | 13 => (-937115221 / 250000000000 : ℝ)
  | 14 => (-3754758253 / 1000000000000 : ℝ)
  | 15 => (-3760914443 / 1000000000000 : ℝ)
  | 16 => (-470865987 / 125000000000 : ℝ)
  | 17 => (-1886398523 / 500000000000 : ℝ)
  | 18 => (-1889260161 / 500000000000 : ℝ)
  | 19 => (-236506009 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch052Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1040 : ℝ) + (j.val : ℝ)) / 1600)
      (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch052Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch052Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1040 : ℝ) + (j.val : ℝ)) / 1600)
    (((1040 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch052Neg25WeightLower j.val) (hpThetaShiftTwoBatch052Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch052Neg25WeightLower, hpThetaShiftTwoBatch052Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch052Neg25_integral_bounds :
    (-530888533 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (52 / 80 : ℝ) ((52 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-64914207 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1040 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch052Lower hpThetaJensenCellsBatch052Upper
    hpThetaShiftTwoBatch052Neg25WeightLower hpThetaShiftTwoBatch052Neg25WeightUpper hpThetaJensenCellsBatch052_bounds hpThetaShiftTwoBatch052Neg25_weight_bounds
  have hl : (-530888533 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch052Lower j * hpThetaShiftTwoBatch052Neg25WeightLower j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftTwoBatch052Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftTwoBatch052Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch052Lower j * hpThetaShiftTwoBatch052Neg25WeightUpper j)
        (hpThetaJensenCellsBatch052Upper j * hpThetaShiftTwoBatch052Neg25WeightUpper j) / 1600) ≤ (-64914207 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch052Lower, hpThetaJensenCellsBatch052Upper,
      hpThetaShiftTwoBatch052Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1040 : ℝ) / 1600 = 52 / 80 by norm_num,
    show ((1040 : ℝ) + 20) / 1600 = (52 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch052Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch052Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch052Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch052Neg25_integral_bounds
end HodgeProofHP
