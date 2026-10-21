/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch072

/-! Exact signed weight and batch integral certificates, batch 72 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch072Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2580145927669 / 500000000000 : ℝ)
  | 1 => (-1300878178573 / 250000000000 : ℝ)
  | 2 => (-5247049293257 / 1000000000000 : ℝ)
  | 3 => (-1322725896801 / 250000000000 : ℝ)
  | 4 => (-333442350117 / 62500000000 : ℝ)
  | 5 => (-672446669227 / 125000000000 : ℝ)
  | 6 => (-5424392870459 / 1000000000000 : ℝ)
  | 7 => (-683692273767 / 125000000000 : ℝ)
  | 8 => (-1378752840537 / 250000000000 : ℝ)
  | 9 => (-5560814446809 / 1000000000000 : ℝ)
  | 10 => (-5606949515497 / 1000000000000 : ℝ)
  | 11 => (-56534186507 / 10000000000 : ℝ)
  | 12 => (-2850111973037 / 500000000000 : ℝ)
  | 13 => (-1436841876621 / 250000000000 : ℝ)
  | 14 => (-289742572403 / 50000000000 : ℝ)
  | 15 => (-5842677898249 / 1000000000000 : ℝ)
  | 16 => (-2945424497929 / 500000000000 : ℝ)
  | 17 => (-2969683445557 / 500000000000 : ℝ)
  | 18 => (-598823374571 / 100000000000 : ℝ)
  | 19 => (-6037451732857 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch072Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2558692366071 / 500000000000 : ℝ)
  | 1 => (-5160291855337 / 1000000000000 : ℝ)
  | 2 => (-5203512714291 / 1000000000000 : ℝ)
  | 3 => (-655881161657 / 125000000000 : ℝ)
  | 4 => (-5290903587203 / 1000000000000 : ℝ)
  | 5 => (-5335077601871 / 1000000000000 : ℝ)
  | 6 => (-1075914670763 / 200000000000 : ℝ)
  | 7 => (-2712196435229 / 500000000000 : ℝ)
  | 8 => (-1093907638027 / 200000000000 : ℝ)
  | 9 => (-5515011362147 / 1000000000000 : ℝ)
  | 10 => (-695101805851 / 125000000000 : ℝ)
  | 11 => (-700868689437 / 125000000000 : ℝ)
  | 12 => (-5653418650699 / 1000000000000 : ℝ)
  | 13 => (-5700223946073 / 1000000000000 : ℝ)
  | 14 => (-5747367506483 / 1000000000000 : ℝ)
  | 15 => (-5794851448059 / 1000000000000 : ℝ)
  | 16 => (-730334737281 / 125000000000 : ℝ)
  | 17 => (-5890848995857 / 1000000000000 : ℝ)
  | 18 => (-5939366891113 / 1000000000000 : ℝ)
  | 19 => (-5988233745709 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch072Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1440 : ℝ) + (j.val : ℝ)) / 1600)
      (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch072Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch072Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1440 : ℝ) + (j.val : ℝ)) / 1600)
    (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch072Neg100WeightLower j.val) (hpThetaShiftTwoBatch072Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch072Neg100WeightLower, hpThetaShiftTwoBatch072Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch072Neg100_integral_bounds :
    (-1340269753 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-1290457863 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch072Lower hpThetaJensenCellsBatch072Upper
    hpThetaShiftTwoBatch072Neg100WeightLower hpThetaShiftTwoBatch072Neg100WeightUpper hpThetaJensenCellsBatch072_bounds hpThetaShiftTwoBatch072Neg100_weight_bounds
  have hl : (-1340269753 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch072Lower j * hpThetaShiftTwoBatch072Neg100WeightLower j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftTwoBatch072Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftTwoBatch072Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch072Lower j * hpThetaShiftTwoBatch072Neg100WeightUpper j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftTwoBatch072Neg100WeightUpper j) / 1600) ≤ (-1290457863 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftTwoBatch072Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1440 : ℝ) / 1600 = 72 / 80 by norm_num,
    show ((1440 : ℝ) + 20) / 1600 = (72 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch072Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-367573961407 / 500000000000 : ℝ)
  | 1 => (-742634593761 / 1000000000000 : ℝ)
  | 2 => (-750184039947 / 1000000000000 : ℝ)
  | 3 => (-47362293753 / 62500000000 : ℝ)
  | 4 => (-95684126911 / 125000000000 : ℝ)
  | 5 => (-48325839341 / 62500000000 : ℝ)
  | 6 => (-195254597229 / 250000000000 : ℝ)
  | 7 => (-788888342619 / 1000000000000 : ℝ)
  | 8 => (-796823742117 / 1000000000000 : ℝ)
  | 9 => (-32193001663 / 40000000000 : ℝ)
  | 10 => (-406446348891 / 500000000000 : ℝ)
  | 11 => (-164205434033 / 200000000000 : ℝ)
  | 12 => (-829228920801 / 1000000000000 : ℝ)
  | 13 => (-837498414429 / 1000000000000 : ℝ)
  | 14 => (-845836118463 / 1000000000000 : ℝ)
  | 15 => (-427121251503 / 500000000000 : ℝ)
  | 16 => (-862718040861 / 1000000000000 : ℝ)
  | 17 => (-174252641509 / 200000000000 : ℝ)
  | 18 => (-8798784813 / 10000000000 : ℝ)
  | 19 => (-888564343107 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch072Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-72772359097 / 100000000000 : ℝ)
  | 1 => (-735147922813 / 1000000000000 : ℝ)
  | 2 => (-4641466211 / 6250000000 : ℝ)
  | 3 => (-375092019973 / 500000000000 : ℝ)
  | 4 => (-757796700047 / 1000000000000 : ℝ)
  | 5 => (-765473015287 / 1000000000000 : ℝ)
  | 6 => (-154642685891 / 200000000000 : ℝ)
  | 7 => (-156203677783 / 200000000000 : ℝ)
  | 8 => (-394444171309 / 500000000000 : ℝ)
  | 9 => (-199205935529 / 250000000000 : ℝ)
  | 10 => (-402412520787 / 500000000000 : ℝ)
  | 11 => (-812892697781 / 1000000000000 : ℝ)
  | 12 => (-205256792541 / 250000000000 : ℝ)
  | 13 => (-1036536151 / 1250000000 : ℝ)
  | 14 => (-209374603607 / 250000000000 : ℝ)
  | 15 => (-422918059231 / 500000000000 : ℝ)
  | 16 => (-170848500601 / 200000000000 : ℝ)
  | 17 => (-43135902043 / 50000000000 : ℝ)
  | 18 => (-108907900943 / 125000000000 : ℝ)
  | 19 => (-879878481299 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch072Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1440 : ℝ) + (j.val : ℝ)) / 1600)
      (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch072Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch072Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1440 : ℝ) + (j.val : ℝ)) / 1600)
    (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch072Neg65WeightLower j.val) (hpThetaShiftTwoBatch072Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch072Neg65WeightLower, hpThetaShiftTwoBatch072Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch072Neg65_integral_bounds :
    (-96992763 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-93227319 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch072Lower hpThetaJensenCellsBatch072Upper
    hpThetaShiftTwoBatch072Neg65WeightLower hpThetaShiftTwoBatch072Neg65WeightUpper hpThetaJensenCellsBatch072_bounds hpThetaShiftTwoBatch072Neg65_weight_bounds
  have hl : (-96992763 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch072Lower j * hpThetaShiftTwoBatch072Neg65WeightLower j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftTwoBatch072Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftTwoBatch072Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch072Lower j * hpThetaShiftTwoBatch072Neg65WeightUpper j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftTwoBatch072Neg65WeightUpper j) / 1600) ≤ (-93227319 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftTwoBatch072Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1440 : ℝ) / 1600 = 72 / 80 by norm_num,
    show ((1440 : ℝ) + 20) / 1600 = (72 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch072Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-19147536297 / 500000000000 : ℝ)
  | 1 => (-39301079603 / 1000000000000 : ℝ)
  | 2 => (-20159595321 / 500000000000 : ℝ)
  | 3 => (-10337377297 / 250000000000 : ℝ)
  | 4 => (-10598034851 / 250000000000 : ℝ)
  | 5 => (-43447186137 / 1000000000000 : ℝ)
  | 6 => (-44514754927 / 1000000000000 : ℝ)
  | 7 => (-45594952007 / 1000000000000 : ℝ)
  | 8 => (-46687884309 / 1000000000000 : ℝ)
  | 9 => (-23896829733 / 500000000000 : ℝ)
  | 10 => (-24456192909 / 500000000000 : ℝ)
  | 11 => (-50044172411 / 1000000000000 : ℝ)
  | 12 => (-3199320563 / 62500000000 : ℝ)
  | 13 => (-13086841521 / 250000000000 : ℝ)
  | 14 => (-10703798967 / 200000000000 : ℝ)
  | 15 => (-3419007949 / 62500000000 : ℝ)
  | 16 => (-55902875777 / 1000000000000 : ℝ)
  | 17 => (-11423070799 / 200000000000 : ℝ)
  | 18 => (-1166833519 / 20000000000 : ℝ)
  | 19 => (-3723872281 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch072Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-37301066819 / 1000000000000 : ℝ)
  | 1 => (-38295072593 / 1000000000000 : ℝ)
  | 2 => (-19650539801 / 500000000000 : ℝ)
  | 3 => (-40319190641 / 1000000000000 : ℝ)
  | 4 => (-41349509187 / 1000000000000 : ℝ)
  | 5 => (-42392139403 / 1000000000000 : ℝ)
  | 6 => (-5430898267 / 125000000000 : ℝ)
  | 7 => (-22257377463 / 500000000000 : ℝ)
  | 8 => (-22797476003 / 500000000000 : ℝ)
  | 9 => (-11671971077 / 250000000000 : ℝ)
  | 10 => (-9558731893 / 200000000000 : ℝ)
  | 11 => (-48912385817 / 1000000000000 : ℝ)
  | 12 => (-5004417241 / 100000000000 : ℝ)
  | 13 => (-51189129007 / 1000000000000 : ℝ)
  | 14 => (-52347366083 / 1000000000000 : ℝ)
  | 15 => (-26759497417 / 500000000000 : ℝ)
  | 16 => (-54704127183 / 1000000000000 : ℝ)
  | 17 => (-436741217 / 7812500000 : ℝ)
  | 18 => (-28557676997 / 500000000000 : ℝ)
  | 19 => (-58341675949 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch072Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1440 : ℝ) + (j.val : ℝ)) / 1600)
      (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch072Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch072Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1440 : ℝ) + (j.val : ℝ)) / 1600)
    (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch072Neg45WeightLower j.val) (hpThetaShiftTwoBatch072Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch072Neg45WeightLower, hpThetaShiftTwoBatch072Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch072Neg45_integral_bounds :
    (-11524863 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-2732449 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch072Lower hpThetaJensenCellsBatch072Upper
    hpThetaShiftTwoBatch072Neg45WeightLower hpThetaShiftTwoBatch072Neg45WeightUpper hpThetaJensenCellsBatch072_bounds hpThetaShiftTwoBatch072Neg45_weight_bounds
  have hl : (-11524863 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch072Lower j * hpThetaShiftTwoBatch072Neg45WeightLower j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftTwoBatch072Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftTwoBatch072Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch072Lower j * hpThetaShiftTwoBatch072Neg45WeightUpper j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftTwoBatch072Neg45WeightUpper j) / 1600) ≤ (-2732449 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftTwoBatch072Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1440 : ℝ) / 1600 = 72 / 80 by norm_num,
    show ((1440 : ℝ) + 20) / 1600 = (72 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch072Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (22794471261 / 1000000000000 : ℝ)
  | 1 => (2872582513 / 125000000000 : ℝ)
  | 2 => (11583756357 / 500000000000 : ℝ)
  | 3 => (23355026723 / 1000000000000 : ℝ)
  | 4 => (4708639943 / 200000000000 : ℝ)
  | 5 => (23732029217 / 1000000000000 : ℝ)
  | 6 => (11960756353 / 500000000000 : ℝ)
  | 7 => (24111647607 / 1000000000000 : ℝ)
  | 8 => (24302431289 / 1000000000000 : ℝ)
  | 9 => (24493861069 / 1000000000000 : ℝ)
  | 10 => (2468593421 / 100000000000 : ℝ)
  | 11 => (24878647919 / 1000000000000 : ℝ)
  | 12 => (6267999837 / 250000000000 : ℝ)
  | 13 => (6316496399 / 250000000000 : ℝ)
  | 14 => (3182575463 / 125000000000 : ℝ)
  | 15 => (801745333 / 31250000000 : ℝ)
  | 16 => (1292586169 / 50000000000 : ℝ)
  | 17 => (26048218749 / 1000000000000 : ℝ)
  | 18 => (3280666697 / 125000000000 : ℝ)
  | 19 => (5288612923 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch072Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (4596132021 / 200000000000 : ℝ)
  | 1 => (4633502543 / 200000000000 : ℝ)
  | 2 => (5838756681 / 250000000000 : ℝ)
  | 3 => (5885799929 / 250000000000 : ℝ)
  | 4 => (11866014609 / 500000000000 : ℝ)
  | 5 => (23921512707 / 1000000000000 : ℝ)
  | 6 => (3013955951 / 125000000000 : ℝ)
  | 7 => (2430243129 / 100000000000 : ℝ)
  | 8 => (2449386107 / 100000000000 : ℝ)
  | 9 => (24685934211 / 1000000000000 : ℝ)
  | 10 => (310983099 / 12500000000 : ℝ)
  | 11 => (25071999349 / 1000000000000 : ℝ)
  | 12 => (25265985597 / 1000000000000 : ℝ)
  | 13 => (5092120741 / 200000000000 : ℝ)
  | 14 => (25655850657 / 1000000000000 : ℝ)
  | 15 => (25851723381 / 1000000000000 : ℝ)
  | 16 => (833543 / 32000000 : ℝ)
  | 17 => (26245333577 / 1000000000000 : ℝ)
  | 18 => (3305383077 / 125000000000 : ℝ)
  | 19 => (13320704283 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch072Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1440 : ℝ) + (j.val : ℝ)) / 1600)
      (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch072Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch072Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1440 : ℝ) + (j.val : ℝ)) / 1600)
    (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch072Neg25WeightLower j.val) (hpThetaShiftTwoBatch072Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch072Neg25WeightLower, hpThetaShiftTwoBatch072Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch072Neg25_integral_bounds :
    (1145731 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (2973529 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch072Lower hpThetaJensenCellsBatch072Upper
    hpThetaShiftTwoBatch072Neg25WeightLower hpThetaShiftTwoBatch072Neg25WeightUpper hpThetaJensenCellsBatch072_bounds hpThetaShiftTwoBatch072Neg25_weight_bounds
  have hl : (1145731 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch072Lower j * hpThetaShiftTwoBatch072Neg25WeightLower j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftTwoBatch072Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftTwoBatch072Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch072Lower j * hpThetaShiftTwoBatch072Neg25WeightUpper j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftTwoBatch072Neg25WeightUpper j) / 1600) ≤ (2973529 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftTwoBatch072Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1440 : ℝ) / 1600 = 72 / 80 by norm_num,
    show ((1440 : ℝ) + 20) / 1600 = (72 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch072Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch072Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch072Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch072Neg25_integral_bounds
end HodgeProofHP
