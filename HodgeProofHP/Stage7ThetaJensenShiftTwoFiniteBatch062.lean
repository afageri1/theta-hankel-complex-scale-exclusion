/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch062

/-! Exact signed weight and batch integral certificates, batch 62 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch062Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-39047375459 / 50000000000 : ℝ)
  | 1 => (-394720089107 / 500000000000 : ℝ)
  | 2 => (-798011049779 / 1000000000000 : ℝ)
  | 3 => (-100832591761 / 125000000000 : ℝ)
  | 4 => (-815389845361 / 1000000000000 : ℝ)
  | 5 => (-164839800369 / 200000000000 : ℝ)
  | 6 => (-166617765167 / 200000000000 : ℝ)
  | 7 => (-842059943701 / 1000000000000 : ℝ)
  | 8 => (-53194561619 / 62500000000 : ℝ)
  | 9 => (-430124293511 / 500000000000 : ℝ)
  | 10 => (-217366846443 / 250000000000 : ℝ)
  | 11 => (-87877002503 / 100000000000 : ℝ)
  | 12 => (-888157151857 / 1000000000000 : ℝ)
  | 13 => (-448814708759 / 500000000000 : ℝ)
  | 14 => (-226796869377 / 250000000000 : ℝ)
  | 15 => (-916831991571 / 1000000000000 : ℝ)
  | 16 => (-926563623727 / 1000000000000 : ℝ)
  | 17 => (-234095760573 / 250000000000 : ℝ)
  | 18 => (-29571591247 / 31250000000 : ℝ)
  | 19 => (-47814396677 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch062Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-24141638639 / 31250000000 : ℝ)
  | 1 => (-780947509179 / 1000000000000 : ℝ)
  | 2 => (-789440178213 / 1000000000000 : ℝ)
  | 3 => (-399005524889 / 500000000000 : ℝ)
  | 4 => (-806660734087 / 1000000000000 : ℝ)
  | 5 => (-10192373067 / 12500000000 : ℝ)
  | 6 => (-206049750461 / 250000000000 : ℝ)
  | 7 => (-416544412917 / 500000000000 : ℝ)
  | 8 => (-8420599437 / 10000000000 : ℝ)
  | 9 => (-851112985903 / 1000000000000 : ℝ)
  | 10 => (-860248587021 / 1000000000000 : ℝ)
  | 11 => (-869467385771 / 1000000000000 : ℝ)
  | 12 => (-878770025029 / 1000000000000 : ℝ)
  | 13 => (-55509821991 / 62500000000 : ℝ)
  | 14 => (-897629417517 / 1000000000000 : ℝ)
  | 15 => (-907187477507 / 1000000000000 : ℝ)
  | 16 => (-91683199157 / 100000000000 : ℝ)
  | 17 => (-463281811863 / 500000000000 : ℝ)
  | 18 => (-936383042291 / 1000000000000 : ℝ)
  | 19 => (-946290919903 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch062Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1240 : ℝ) + (j.val : ℝ)) / 1600)
      (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch062Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch062Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1240 : ℝ) + (j.val : ℝ)) / 1600)
    (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch062Neg100WeightLower j.val) (hpThetaShiftTwoBatch062Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch062Neg100WeightLower, hpThetaShiftTwoBatch062Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch062Neg100_integral_bounds :
    (-81082999 / 10000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-1565898543 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch062Lower hpThetaJensenCellsBatch062Upper
    hpThetaShiftTwoBatch062Neg100WeightLower hpThetaShiftTwoBatch062Neg100WeightUpper hpThetaJensenCellsBatch062_bounds hpThetaShiftTwoBatch062Neg100_weight_bounds
  have hl : (-81082999 / 10000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch062Lower j * hpThetaShiftTwoBatch062Neg100WeightLower j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftTwoBatch062Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftTwoBatch062Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch062Lower j * hpThetaShiftTwoBatch062Neg100WeightUpper j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftTwoBatch062Neg100WeightUpper j) / 1600) ≤ (-1565898543 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftTwoBatch062Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1240 : ℝ) / 1600 = 62 / 80 by norm_num,
    show ((1240 : ℝ) + 20) / 1600 = (62 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch062Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-25518298349 / 500000000000 : ℝ)
  | 1 => (-52052187117 / 1000000000000 : ℝ)
  | 2 => (-26540219249 / 500000000000 : ℝ)
  | 3 => (-54121469847 / 1000000000000 : ℝ)
  | 4 => (-1724231283 / 31250000000 : ℝ)
  | 5 => (-56242352903 / 1000000000000 : ℝ)
  | 6 => (-57322447063 / 1000000000000 : ℝ)
  | 7 => (-58415806111 / 1000000000000 : ℝ)
  | 8 => (-59522553529 / 1000000000000 : ℝ)
  | 9 => (-15160703427 / 250000000000 : ℝ)
  | 10 => (-12355342391 / 200000000000 : ℝ)
  | 11 => (-62924374501 / 1000000000000 : ℝ)
  | 12 => (-32042964251 / 500000000000 : ℝ)
  | 13 => (-2039421939 / 31250000000 : ℝ)
  | 14 => (-13290244833 / 200000000000 : ℝ)
  | 15 => (-2706208993 / 40000000000 : ℝ)
  | 16 => (-34436817473 / 500000000000 : ℝ)
  | 17 => (-14021317281 / 200000000000 : ℝ)
  | 18 => (-14270842407 / 200000000000 : ℝ)
  | 19 => (-18154161409 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch062Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-10006709823 / 200000000000 : ℝ)
  | 1 => (-51036596697 / 1000000000000 : ℝ)
  | 2 => (-13013046779 / 250000000000 : ℝ)
  | 3 => (-53080438497 / 1000000000000 : ℝ)
  | 4 => (-27060734923 / 500000000000 : ℝ)
  | 5 => (-11035080211 / 200000000000 : ℝ)
  | 6 => (-28121176451 / 500000000000 : ℝ)
  | 7 => (-28661223531 / 500000000000 : ℝ)
  | 8 => (-5841580611 / 100000000000 : ℝ)
  | 9 => (-7440319191 / 125000000000 : ℝ)
  | 10 => (-60642813707 / 1000000000000 : ℝ)
  | 11 => (-30888355977 / 500000000000 : ℝ)
  | 12 => (-125848749 / 2000000000 : ℝ)
  | 13 => (-64085928501 / 1000000000000 : ℝ)
  | 14 => (-65261502047 / 1000000000000 : ℝ)
  | 15 => (-16612806041 / 250000000000 : ℝ)
  | 16 => (-8456903103 / 125000000000 : ℝ)
  | 17 => (-13774726989 / 200000000000 : ℝ)
  | 18 => (-17526646601 / 250000000000 : ℝ)
  | 19 => (-35677106017 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch062Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1240 : ℝ) + (j.val : ℝ)) / 1600)
      (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch062Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch062Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1240 : ℝ) + (j.val : ℝ)) / 1600)
    (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch062Neg65WeightLower j.val) (hpThetaShiftTwoBatch062Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch062Neg65WeightLower, hpThetaShiftTwoBatch062Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch062Neg65_integral_bounds :
    (-286348947 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-548627827 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch062Lower hpThetaJensenCellsBatch062Upper
    hpThetaShiftTwoBatch062Neg65WeightLower hpThetaShiftTwoBatch062Neg65WeightUpper hpThetaJensenCellsBatch062_bounds hpThetaShiftTwoBatch062Neg65_weight_bounds
  have hl : (-286348947 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch062Lower j * hpThetaShiftTwoBatch062Neg65WeightLower j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftTwoBatch062Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftTwoBatch062Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch062Lower j * hpThetaShiftTwoBatch062Neg65WeightUpper j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftTwoBatch062Neg65WeightUpper j) / 1600) ≤ (-548627827 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftTwoBatch062Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1240 : ℝ) / 1600 = 62 / 80 by norm_num,
    show ((1240 : ℝ) + 20) / 1600 = (62 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch062Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (21356557277 / 1000000000000 : ℝ)
  | 1 => (4282005763 / 200000000000 : ℝ)
  | 2 => (10731155103 / 500000000000 : ℝ)
  | 3 => (67229313 / 3125000000 : ℝ)
  | 4 => (10781608591 / 500000000000 : ℝ)
  | 5 => (10805899783 / 500000000000 : ℝ)
  | 6 => (108295527 / 5000000000 : ℝ)
  | 7 => (4341022511 / 200000000000 : ℝ)
  | 8 => (5437449673 / 250000000000 : ℝ)
  | 9 => (21793141257 / 1000000000000 : ℝ)
  | 10 => (545877937 / 25000000000 : ℝ)
  | 11 => (10937852187 / 500000000000 : ℝ)
  | 12 => (2191487873 / 100000000000 : ℝ)
  | 13 => (21952617123 / 1000000000000 : ℝ)
  | 14 => (10994447951 / 500000000000 : ℝ)
  | 15 => (4404738239 / 200000000000 : ℝ)
  | 16 => (2757122363 / 125000000000 : ℝ)
  | 17 => (4417746941 / 200000000000 : ℝ)
  | 18 => (11059467023 / 500000000000 : ℝ)
  | 19 => (22147552143 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch062Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1338126801 / 62500000000 : ℝ)
  | 1 => (21462310207 / 1000000000000 : ℝ)
  | 2 => (21513380161 / 1000000000000 : ℝ)
  | 3 => (21563217183 / 1000000000000 : ℝ)
  | 4 => (21611799567 / 1000000000000 : ℝ)
  | 5 => (21659105401 / 1000000000000 : ℝ)
  | 6 => (5426278139 / 250000000000 : ℝ)
  | 7 => (21749798693 / 1000000000000 : ℝ)
  | 8 => (10896570629 / 500000000000 : ℝ)
  | 9 => (21835117481 / 1000000000000 : ℝ)
  | 10 => (35001127 / 1600000000 : ℝ)
  | 11 => (21914878731 / 1000000000000 : ℝ)
  | 12 => (5488154281 / 250000000000 : ℝ)
  | 13 => (21988895903 / 1000000000000 : ℝ)
  | 14 => (5505922799 / 250000000000 : ℝ)
  | 15 => (4411395781 / 200000000000 : ℝ)
  | 16 => (11044367353 / 500000000000 : ℝ)
  | 17 => (22118934047 / 1000000000000 : ℝ)
  | 18 => (1384222009 / 62500000000 : ℝ)
  | 19 => (11087281993 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch062Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1240 : ℝ) + (j.val : ℝ)) / 1600)
      (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch062Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch062Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1240 : ℝ) + (j.val : ℝ)) / 1600)
    (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch062Neg45WeightLower j.val) (hpThetaShiftTwoBatch062Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch062Neg45WeightLower, hpThetaShiftTwoBatch062Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch062Neg45_integral_bounds :
    (4999747 / 25000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (20530337 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch062Lower hpThetaJensenCellsBatch062Upper
    hpThetaShiftTwoBatch062Neg45WeightLower hpThetaShiftTwoBatch062Neg45WeightUpper hpThetaJensenCellsBatch062_bounds hpThetaShiftTwoBatch062Neg45_weight_bounds
  have hl : (4999747 / 25000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch062Lower j * hpThetaShiftTwoBatch062Neg45WeightLower j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftTwoBatch062Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftTwoBatch062Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch062Lower j * hpThetaShiftTwoBatch062Neg45WeightUpper j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftTwoBatch062Neg45WeightUpper j) / 1600) ≤ (20530337 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftTwoBatch062Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1240 : ℝ) / 1600 = 62 / 80 by norm_num,
    show ((1240 : ℝ) + 20) / 1600 = (62 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch062Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-250787621 / 500000000000 : ℝ)
  | 1 => (-44824689 / 100000000000 : ℝ)
  | 2 => (-394398041 / 1000000000000 : ℝ)
  | 3 => (-340026497 / 1000000000000 : ℝ)
  | 4 => (-285130069 / 1000000000000 : ℝ)
  | 5 => (-28713321 / 125000000000 : ℝ)
  | 6 => (-173753811 / 1000000000000 : ℝ)
  | 7 => (-117269617 / 1000000000000 : ℝ)
  | 8 => (-60251809 / 1000000000000 : ℝ)
  | 9 => (-539643 / 200000000000 : ℝ)
  | 10 => (13848333 / 250000000000 : ℝ)
  | 11 => (57012499 / 500000000000 : ℝ)
  | 12 => (173198941 / 1000000000000 : ℝ)
  | 13 => (46583463 / 200000000000 : ℝ)
  | 14 => (293182273 / 1000000000000 : ℝ)
  | 15 => (176997979 / 500000000000 : ℝ)
  | 16 => (811251 / 1953125000 : ℝ)
  | 17 => (47727807 / 100000000000 : ℝ)
  | 18 => (269875381 / 500000000000 : ℝ)
  | 19 => (602780713 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch062Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-448246889 / 1000000000000 : ℝ)
  | 1 => (-9859951 / 25000000000 : ℝ)
  | 2 => (-2656457 / 7812500000 : ℝ)
  | 3 => (-71282517 / 250000000000 : ℝ)
  | 4 => (-229706567 / 1000000000000 : ℝ)
  | 5 => (-17375381 / 100000000000 : ℝ)
  | 6 => (-7329351 / 62500000000 : ℝ)
  | 7 => (-1882869 / 31250000000 : ℝ)
  | 8 => (-1349107 / 500000000000 : ℝ)
  | 9 => (55393333 / 1000000000000 : ℝ)
  | 10 => (114024999 / 1000000000000 : ℝ)
  | 11 => (86599471 / 500000000000 : ℝ)
  | 12 => (58229329 / 250000000000 : ℝ)
  | 13 => (146591137 / 500000000000 : ℝ)
  | 14 => (353995959 / 1000000000000 : ℝ)
  | 15 => (415360513 / 1000000000000 : ℝ)
  | 16 => (477278071 / 1000000000000 : ℝ)
  | 17 => (539750763 / 1000000000000 : ℝ)
  | 18 => (301390357 / 500000000000 : ℝ)
  | 19 => (166592511 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch062Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1240 : ℝ) + (j.val : ℝ)) / 1600)
      (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch062Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch062Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1240 : ℝ) + (j.val : ℝ)) / 1600)
    (((1240 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch062Neg25WeightLower j.val) (hpThetaShiftTwoBatch062Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch062Neg25WeightLower, hpThetaShiftTwoBatch062Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch062Neg25_integral_bounds :
    (12361 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (62 / 80 : ℝ) ((62 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (123677 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1240 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch062Lower hpThetaJensenCellsBatch062Upper
    hpThetaShiftTwoBatch062Neg25WeightLower hpThetaShiftTwoBatch062Neg25WeightUpper hpThetaJensenCellsBatch062_bounds hpThetaShiftTwoBatch062Neg25_weight_bounds
  have hl : (12361 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch062Lower j * hpThetaShiftTwoBatch062Neg25WeightLower j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftTwoBatch062Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftTwoBatch062Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch062Lower j * hpThetaShiftTwoBatch062Neg25WeightUpper j)
        (hpThetaJensenCellsBatch062Upper j * hpThetaShiftTwoBatch062Neg25WeightUpper j) / 1600) ≤ (123677 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch062Lower, hpThetaJensenCellsBatch062Upper,
      hpThetaShiftTwoBatch062Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1240 : ℝ) / 1600 = 62 / 80 by norm_num,
    show ((1240 : ℝ) + 20) / 1600 = (62 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch062Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch062Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch062Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch062Neg25_integral_bounds
end HodgeProofHP
