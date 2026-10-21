/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch037

/-! Exact signed weight and batch integral certificates, batch 37 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch037Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (40933099193 / 250000000000 : ℝ)
  | 1 => (164196265241 / 1000000000000 : ℝ)
  | 2 => (658566751 / 4000000000 : ℝ)
  | 3 => (25791919 / 156250000 : ℝ)
  | 4 => (82737829949 / 500000000000 : ℝ)
  | 5 => (41465857881 / 250000000000 : ℝ)
  | 6 => (1662312011 / 10000000000 : ℝ)
  | 7 => (41644642241 / 250000000000 : ℝ)
  | 8 => (166905131137 / 1000000000000 : ℝ)
  | 9 => (167210479289 / 1000000000000 : ℝ)
  | 10 => (33498840143 / 200000000000 : ℝ)
  | 11 => (167755878297 / 1000000000000 : ℝ)
  | 12 => (83997545239 / 500000000000 : ℝ)
  | 13 => (42052852807 / 250000000000 : ℝ)
  | 14 => (168404410013 / 1000000000000 : ℝ)
  | 15 => (33714730353 / 200000000000 : ℝ)
  | 16 => (84359348423 / 500000000000 : ℝ)
  | 17 => (84419550511 / 500000000000 : ℝ)
  | 18 => (84467207713 / 500000000000 : ℝ)
  | 19 => (5281380829 / 31250000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch037Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (82098132621 / 500000000000 : ℝ)
  | 1 => (164641687751 / 1000000000000 : ℝ)
  | 2 => (165068281601 / 1000000000000 : ℝ)
  | 3 => (165475659899 / 1000000000000 : ℝ)
  | 4 => (6634537261 / 40000000000 : ℝ)
  | 5 => (166231201101 / 1000000000000 : ℝ)
  | 6 => (33315713793 / 200000000000 : ℝ)
  | 7 => (83452565569 / 500000000000 : ℝ)
  | 8 => (16721047929 / 100000000000 : ℝ)
  | 9 => (41873550179 / 250000000000 : ℝ)
  | 10 => (83877939149 / 500000000000 : ℝ)
  | 11 => (167995090479 / 1000000000000 : ℝ)
  | 12 => (168211411229 / 1000000000000 : ℝ)
  | 13 => (84202205007 / 500000000000 : ℝ)
  | 14 => (84286825883 / 500000000000 : ℝ)
  | 15 => (168718696847 / 1000000000000 : ℝ)
  | 16 => (168839101023 / 1000000000000 : ℝ)
  | 17 => (168934415427 / 1000000000000 : ℝ)
  | 18 => (169004186529 / 1000000000000 : ℝ)
  | 19 => (21130994513 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch037Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((740 : ℝ) + (j.val : ℝ)) / 1600)
      (((740 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch037Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch037Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((740 : ℝ) + (j.val : ℝ)) / 1600)
    (((740 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch037Neg100WeightLower j.val) (hpThetaShiftOneBatch037Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch037Neg100WeightLower, hpThetaShiftOneBatch037Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch037Neg100_integral_bounds :
    (360050260683 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (366362878063 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (740 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch037Lower hpThetaJensenCellsBatch037Upper
    hpThetaShiftOneBatch037Neg100WeightLower hpThetaShiftOneBatch037Neg100WeightUpper hpThetaJensenCellsBatch037_bounds hpThetaShiftOneBatch037Neg100_weight_bounds
  have hl : (360050260683 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch037Lower j * hpThetaShiftOneBatch037Neg100WeightLower j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftOneBatch037Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftOneBatch037Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch037Lower j * hpThetaShiftOneBatch037Neg100WeightUpper j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftOneBatch037Neg100WeightUpper j) / 1600) ≤ (366362878063 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftOneBatch037Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (740 : ℝ) / 1600 = 37 / 80 by norm_num,
    show ((740 : ℝ) + 20) / 1600 = (37 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch037Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2199450971 / 40000000000 : ℝ)
  | 1 => (447531493 / 8000000000 : ℝ)
  | 2 => (7112788961 / 125000000000 : ℝ)
  | 3 => (57868876683 / 1000000000000 : ℝ)
  | 4 => (14710277021 / 250000000000 : ℝ)
  | 5 => (59818981603 / 1000000000000 : ℝ)
  | 6 => (60802472193 / 1000000000000 : ℝ)
  | 7 => (61791554031 / 1000000000000 : ℝ)
  | 8 => (62786200519 / 1000000000000 : ℝ)
  | 9 => (63786384271 / 1000000000000 : ℝ)
  | 10 => (64792077109 / 1000000000000 : ℝ)
  | 11 => (13160650011 / 200000000000 : ℝ)
  | 12 => (33409936661 / 500000000000 : ℝ)
  | 13 => (67841916309 / 1000000000000 : ℝ)
  | 14 => (8608668449 / 125000000000 : ℝ)
  | 15 => (17475533729 / 250000000000 : ℝ)
  | 16 => (70940245189 / 1000000000000 : ℝ)
  | 17 => (2879345779 / 40000000000 : ℝ)
  | 18 => (73032297983 / 1000000000000 : ℝ)
  | 19 => (74086170063 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch037Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (27970718313 / 500000000000 : ℝ)
  | 1 => (56902311689 / 1000000000000 : ℝ)
  | 2 => (14467219171 / 250000000000 : ℝ)
  | 3 => (11768221617 / 200000000000 : ℝ)
  | 4 => (14954745401 / 250000000000 : ℝ)
  | 5 => (30401236097 / 500000000000 : ℝ)
  | 6 => (3861972127 / 62500000000 : ℝ)
  | 7 => (1569655013 / 25000000000 : ℝ)
  | 8 => (3986649017 / 62500000000 : ℝ)
  | 9 => (6479207711 / 100000000000 : ℝ)
  | 10 => (8225406257 / 125000000000 : ℝ)
  | 11 => (66819873323 / 1000000000000 : ℝ)
  | 12 => (6784191631 / 100000000000 : ℝ)
  | 13 => (68869347593 / 1000000000000 : ℝ)
  | 14 => (69902134917 / 1000000000000 : ℝ)
  | 15 => (7094024519 / 100000000000 : ℝ)
  | 16 => (17995911119 / 250000000000 : ℝ)
  | 17 => (142641207 / 1953125000 : ℝ)
  | 18 => (4630385629 / 62500000000 : ℝ)
  | 19 => (37572612099 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch037Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((740 : ℝ) + (j.val : ℝ)) / 1600)
      (((740 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch037Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch037Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((740 : ℝ) + (j.val : ℝ)) / 1600)
    (((740 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch037Neg65WeightLower j.val) (hpThetaShiftOneBatch037Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch037Neg65WeightLower, hpThetaShiftOneBatch037Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch037Neg65_integral_bounds :
    (27672639037 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (142767623437 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (740 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch037Lower hpThetaJensenCellsBatch037Upper
    hpThetaShiftOneBatch037Neg65WeightLower hpThetaShiftOneBatch037Neg65WeightUpper hpThetaJensenCellsBatch037_bounds hpThetaShiftOneBatch037Neg65_weight_bounds
  have hl : (27672639037 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch037Lower j * hpThetaShiftOneBatch037Neg65WeightLower j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftOneBatch037Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftOneBatch037Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch037Lower j * hpThetaShiftOneBatch037Neg65WeightUpper j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftOneBatch037Neg65WeightUpper j) / 1600) ≤ (142767623437 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftOneBatch037Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (740 : ℝ) / 1600 = 37 / 80 by norm_num,
    show ((740 : ℝ) + 20) / 1600 = (37 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch037Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-38863157033 / 1000000000000 : ℝ)
  | 1 => (-38733468977 / 1000000000000 : ℝ)
  | 2 => (-38600102609 / 1000000000000 : ℝ)
  | 3 => (-38463035247 / 1000000000000 : ℝ)
  | 4 => (-299392533 / 7812500000 : ℝ)
  | 5 => (-38177706889 / 1000000000000 : ℝ)
  | 6 => (-3802940061 / 100000000000 : ℝ)
  | 7 => (-1515092111 / 40000000000 : ℝ)
  | 8 => (-4715173849 / 125000000000 : ℝ)
  | 9 => (-3756164209 / 100000000000 : ℝ)
  | 10 => (-37398034121 / 1000000000000 : ℝ)
  | 11 => (-18615272181 / 500000000000 : ℝ)
  | 12 => (-18529575157 / 500000000000 : ℝ)
  | 13 => (-18441914753 / 500000000000 : ℝ)
  | 14 => (-36704559493 / 1000000000000 : ℝ)
  | 15 => (-36521317861 / 1000000000000 : ℝ)
  | 16 => (-2270880139 / 62500000000 : ℝ)
  | 17 => (-36142830231 / 1000000000000 : ℝ)
  | 18 => (-898688489 / 25000000000 : ℝ)
  | 19 => (-1429927517 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch037Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2420841811 / 62500000000 : ℝ)
  | 1 => (-2412506413 / 62500000000 : ℝ)
  | 2 => (-19231517623 / 500000000000 : ℝ)
  | 3 => (-38322244223 / 1000000000000 : ℝ)
  | 4 => (-4772213361 / 125000000000 : ℝ)
  | 5 => (-38029400609 / 1000000000000 : ℝ)
  | 6 => (-18938651387 / 500000000000 : ℝ)
  | 7 => (-37721390791 / 1000000000000 : ℝ)
  | 8 => (-37561642089 / 1000000000000 : ℝ)
  | 9 => (-934950853 / 25000000000 : ℝ)
  | 10 => (-37230544361 / 1000000000000 : ℝ)
  | 11 => (-37059150313 / 1000000000000 : ℝ)
  | 12 => (-7376765901 / 200000000000 : ℝ)
  | 13 => (-9176139873 / 250000000000 : ℝ)
  | 14 => (-1826065893 / 50000000000 : ℝ)
  | 15 => (-36334082223 / 1000000000000 : ℝ)
  | 16 => (-3614283023 / 100000000000 : ℝ)
  | 17 => (-35947539559 / 1000000000000 : ℝ)
  | 18 => (-8937046981 / 250000000000 : ℝ)
  | 19 => (-1421790123 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch037Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((740 : ℝ) + (j.val : ℝ)) / 1600)
      (((740 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch037Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch037Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((740 : ℝ) + (j.val : ℝ)) / 1600)
    (((740 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch037Neg40WeightLower j.val) (hpThetaShiftOneBatch037Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch037Neg40WeightLower, hpThetaShiftOneBatch037Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch037Neg40_integral_bounds :
    (-2051701463 / 25000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-80429100431 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (740 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch037Lower hpThetaJensenCellsBatch037Upper
    hpThetaShiftOneBatch037Neg40WeightLower hpThetaShiftOneBatch037Neg40WeightUpper hpThetaJensenCellsBatch037_bounds hpThetaShiftOneBatch037Neg40_weight_bounds
  have hl : (-2051701463 / 25000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch037Lower j * hpThetaShiftOneBatch037Neg40WeightLower j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftOneBatch037Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftOneBatch037Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch037Lower j * hpThetaShiftOneBatch037Neg40WeightUpper j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftOneBatch037Neg40WeightUpper j) / 1600) ≤ (-80429100431 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftOneBatch037Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (740 : ℝ) / 1600 = 37 / 80 by norm_num,
    show ((740 : ℝ) + 20) / 1600 = (37 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch037Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-854576223 / 25000000000 : ℝ)
  | 1 => (-34445244081 / 1000000000000 : ℝ)
  | 2 => (-3470770513 / 100000000000 : ℝ)
  | 3 => (-3497042479 / 100000000000 : ℝ)
  | 4 => (-35233395743 / 1000000000000 : ℝ)
  | 5 => (-554634541 / 15625000000 : ℝ)
  | 6 => (-35760062029 / 1000000000000 : ℝ)
  | 7 => (-9005935627 / 250000000000 : ℝ)
  | 8 => (-36287644567 / 1000000000000 : ℝ)
  | 9 => (-3655176067 / 100000000000 : ℝ)
  | 10 => (-36816083237 / 1000000000000 : ℝ)
  | 11 => (-7416120929 / 200000000000 : ℝ)
  | 12 => (-18672658613 / 500000000000 : ℝ)
  | 13 => (-4701276659 / 125000000000 : ℝ)
  | 14 => (-37875285027 / 1000000000000 : ℝ)
  | 15 => (-7628104939 / 200000000000 : ℝ)
  | 16 => (-19202962217 / 500000000000 : ℝ)
  | 17 => (-38671476361 / 1000000000000 : ℝ)
  | 18 => (-9734293137 / 250000000000 : ℝ)
  | 19 => (-1225093907 / 31250000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch037Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-33921126879 / 1000000000000 : ℝ)
  | 1 => (-34183048919 / 1000000000000 : ℝ)
  | 2 => (-430565551 / 12500000000 : ℝ)
  | 3 => (-34707705129 / 1000000000000 : ℝ)
  | 4 => (-34970424789 / 1000000000000 : ℝ)
  | 5 => (-17616697871 / 500000000000 : ℝ)
  | 6 => (-35496610623 / 1000000000000 : ℝ)
  | 7 => (-8940015507 / 250000000000 : ℝ)
  | 8 => (-36023742507 / 1000000000000 : ℝ)
  | 9 => (-18143822283 / 500000000000 : ℝ)
  | 10 => (-36551760669 / 1000000000000 : ℝ)
  | 11 => (-9204020809 / 250000000000 : ℝ)
  | 12 => (-9270151161 / 250000000000 : ℝ)
  | 13 => (-1493812689 / 40000000000 : ℝ)
  | 14 => (-37610213271 / 1000000000000 : ℝ)
  | 15 => (-18937642513 / 500000000000 : ℝ)
  | 16 => (-19070262347 / 500000000000 : ℝ)
  | 17 => (-38405924433 / 1000000000000 : ℝ)
  | 18 => (-966786909 / 25000000000 : ℝ)
  | 19 => (-38937172547 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch037Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((740 : ℝ) + (j.val : ℝ)) / 1600)
      (((740 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch037Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch037Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((740 : ℝ) + (j.val : ℝ)) / 1600)
    (((740 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch037Neg20WeightLower j.val) (hpThetaShiftOneBatch037Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch037Neg20WeightLower, hpThetaShiftOneBatch037Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch037Neg20_integral_bounds :
    (-80255592939 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (37 / 80 : ℝ) ((37 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-39215511071 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (740 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch037Lower hpThetaJensenCellsBatch037Upper
    hpThetaShiftOneBatch037Neg20WeightLower hpThetaShiftOneBatch037Neg20WeightUpper hpThetaJensenCellsBatch037_bounds hpThetaShiftOneBatch037Neg20_weight_bounds
  have hl : (-80255592939 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch037Lower j * hpThetaShiftOneBatch037Neg20WeightLower j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftOneBatch037Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftOneBatch037Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch037Lower j * hpThetaShiftOneBatch037Neg20WeightUpper j)
        (hpThetaJensenCellsBatch037Upper j * hpThetaShiftOneBatch037Neg20WeightUpper j) / 1600) ≤ (-39215511071 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch037Lower, hpThetaJensenCellsBatch037Upper,
      hpThetaShiftOneBatch037Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (740 : ℝ) / 1600 = 37 / 80 by norm_num,
    show ((740 : ℝ) + 20) / 1600 = (37 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch037Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch037Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch037Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch037Neg20_integral_bounds
end HodgeProofHP
