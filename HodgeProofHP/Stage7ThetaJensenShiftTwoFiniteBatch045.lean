/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch045

/-! Exact signed weight and batch integral certificates, batch 45 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch045Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (798111099 / 250000000000 : ℝ)
  | 1 => (3124099453 / 1000000000000 : ℝ)
  | 2 => (1526799083 / 500000000000 : ℝ)
  | 3 => (372613213 / 125000000000 : ℝ)
  | 4 => (581197367 / 200000000000 : ℝ)
  | 5 => (1414402961 / 500000000000 : ℝ)
  | 6 => (2749326923 / 1000000000000 : ℝ)
  | 7 => (133375669 / 50000000000 : ℝ)
  | 8 => (2583328423 / 1000000000000 : ℝ)
  | 9 => (2496734763 / 1000000000000 : ℝ)
  | 10 => (75240459 / 31250000000 : ℝ)
  | 11 => (2316170061 / 1000000000000 : ℝ)
  | 12 => (1111061157 / 500000000000 : ℝ)
  | 13 => (8302783 / 3906250000 : ℝ)
  | 14 => (81052041 / 40000000000 : ℝ)
  | 15 => (962224083 / 500000000000 : ℝ)
  | 16 => (1819913549 / 1000000000000 : ℝ)
  | 17 => (856328201 / 500000000000 : ℝ)
  | 18 => (1602635503 / 1000000000000 : ℝ)
  | 19 => (372452293 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch045Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (325866743 / 100000000000 : ℝ)
  | 1 => (3192444397 / 1000000000000 : ℝ)
  | 2 => (1562049727 / 500000000000 : ℝ)
  | 3 => (3053598167 / 1000000000000 : ℝ)
  | 4 => (596181141 / 200000000000 : ℝ)
  | 5 => (726496709 / 250000000000 : ℝ)
  | 6 => (2828805923 / 1000000000000 : ℝ)
  | 7 => (687331731 / 250000000000 : ℝ)
  | 8 => (2667513381 / 1000000000000 : ℝ)
  | 9 => (322916053 / 125000000000 : ℝ)
  | 10 => (624183691 / 250000000000 : ℝ)
  | 11 => (2407694689 / 1000000000000 : ℝ)
  | 12 => (1158085031 / 500000000000 : ℝ)
  | 13 => (444424463 / 200000000000 : ℝ)
  | 14 => (2125512449 / 1000000000000 : ℝ)
  | 15 => (1013150513 / 500000000000 : ℝ)
  | 16 => (1924448167 / 1000000000000 : ℝ)
  | 17 => (36398271 / 20000000000 : ℝ)
  | 18 => (1712656403 / 1000000000000 : ℝ)
  | 19 => (100164719 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch045Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((900 : ℝ) + (j.val : ℝ)) / 1600)
      (((900 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch045Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch045Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((900 : ℝ) + (j.val : ℝ)) / 1600)
    (((900 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch045Neg100WeightLower j.val) (hpThetaShiftTwoBatch045Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch045Neg100WeightLower, hpThetaShiftTwoBatch045Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch045Neg100_integral_bounds :
    (1454081941 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (306714287 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (900 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch045Lower hpThetaJensenCellsBatch045Upper
    hpThetaShiftTwoBatch045Neg100WeightLower hpThetaShiftTwoBatch045Neg100WeightUpper hpThetaJensenCellsBatch045_bounds hpThetaShiftTwoBatch045Neg100_weight_bounds
  have hl : (1454081941 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch045Lower j * hpThetaShiftTwoBatch045Neg100WeightLower j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftTwoBatch045Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftTwoBatch045Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch045Lower j * hpThetaShiftTwoBatch045Neg100WeightUpper j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftTwoBatch045Neg100WeightUpper j) / 1600) ≤ (306714287 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftTwoBatch045Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (900 : ℝ) / 1600 = 45 / 80 by norm_num,
    show ((900 : ℝ) + 20) / 1600 = (45 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch045Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (230385563 / 62500000000 : ℝ)
  | 1 => (746473293 / 200000000000 : ℝ)
  | 2 => (75576143 / 20000000000 : ℝ)
  | 3 => (3825489189 / 1000000000000 : ℝ)
  | 4 => (77448213 / 20000000000 : ℝ)
  | 5 => (783913909 / 200000000000 : ℝ)
  | 6 => (3966963827 / 1000000000000 : ℝ)
  | 7 => (1003647847 / 250000000000 : ℝ)
  | 8 => (812490013 / 200000000000 : ℝ)
  | 9 => (411053763 / 100000000000 : ℝ)
  | 10 => (4158851797 / 1000000000000 : ℝ)
  | 11 => (525923777 / 125000000000 : ℝ)
  | 12 => (170246019 / 40000000000 : ℝ)
  | 13 => (43051301 / 10000000000 : ℝ)
  | 14 => (87086531 / 20000000000 : ℝ)
  | 15 => (4403737223 / 1000000000000 : ℝ)
  | 16 => (4453359449 / 1000000000000 : ℝ)
  | 17 => (4503190491 / 1000000000000 : ℝ)
  | 18 => (4553227547 / 1000000000000 : ℝ)
  | 19 => (2301733873 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch045Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1866183233 / 500000000000 : ℝ)
  | 1 => (3778807151 / 1000000000000 : ℝ)
  | 2 => (382548919 / 100000000000 : ℝ)
  | 3 => (3872410651 / 1000000000000 : ℝ)
  | 4 => (1959784773 / 500000000000 : ℝ)
  | 5 => (991740957 / 250000000000 : ℝ)
  | 6 => (4014591389 / 1000000000000 : ℝ)
  | 7 => (2031225033 / 500000000000 : ℝ)
  | 8 => (4110537631 / 1000000000000 : ℝ)
  | 9 => (2079425899 / 500000000000 : ℝ)
  | 10 => (4207390217 / 1000000000000 : ℝ)
  | 11 => (1064037619 / 250000000000 : ℝ)
  | 12 => (4305130101 / 1000000000000 : ℝ)
  | 13 => (4354326551 / 1000000000000 : ℝ)
  | 14 => (550467153 / 125000000000 : ℝ)
  | 15 => (89067189 / 20000000000 : ℝ)
  | 16 => (1125797623 / 250000000000 : ℝ)
  | 17 => (1138306887 / 250000000000 : ℝ)
  | 18 => (4603467747 / 1000000000000 : ℝ)
  | 19 => (93078163 / 20000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch045Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((900 : ℝ) + (j.val : ℝ)) / 1600)
      (((900 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch045Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch045Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((900 : ℝ) + (j.val : ℝ)) / 1600)
    (((900 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch045Neg65WeightLower j.val) (hpThetaShiftTwoBatch045Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch045Neg65WeightLower, hpThetaShiftTwoBatch045Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch045Neg65_integral_bounds :
    (2458575453 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (506472889 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (900 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch045Lower hpThetaJensenCellsBatch045Upper
    hpThetaShiftTwoBatch045Neg65WeightLower hpThetaShiftTwoBatch045Neg65WeightUpper hpThetaJensenCellsBatch045_bounds hpThetaShiftTwoBatch045Neg65_weight_bounds
  have hl : (2458575453 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch045Lower j * hpThetaShiftTwoBatch045Neg65WeightLower j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftTwoBatch045Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftTwoBatch045Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch045Lower j * hpThetaShiftTwoBatch045Neg65WeightUpper j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftTwoBatch045Neg65WeightUpper j) / 1600) ≤ (506472889 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftTwoBatch045Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (900 : ℝ) / 1600 = 45 / 80 by norm_num,
    show ((900 : ℝ) + 20) / 1600 = (45 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch045Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-303419177 / 500000000000 : ℝ)
  | 1 => (-591232161 / 1000000000000 : ℝ)
  | 2 => (-287688343 / 500000000000 : ℝ)
  | 3 => (-279635127 / 500000000000 : ℝ)
  | 4 => (-54291119 / 100000000000 : ℝ)
  | 5 => (-526297819 / 1000000000000 : ℝ)
  | 6 => (-509428467 / 1000000000000 : ℝ)
  | 7 => (-24615073 / 50000000000 : ℝ)
  | 8 => (-3799321 / 8000000000 : ℝ)
  | 9 => (-45726779 / 100000000000 : ℝ)
  | 10 => (-439357783 / 1000000000000 : ℝ)
  | 11 => (-210591717 / 500000000000 : ℝ)
  | 12 => (-12585721 / 31250000000 : ℝ)
  | 13 => (-38403503 / 100000000000 : ℝ)
  | 14 => (-365057641 / 1000000000000 : ℝ)
  | 15 => (-345809239 / 1000000000000 : ℝ)
  | 16 => (-163144081 / 500000000000 : ℝ)
  | 17 => (-306492747 / 1000000000000 : ℝ)
  | 18 => (-57284267 / 200000000000 : ℝ)
  | 19 => (-266072267 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch045Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3695201 / 6250000000 : ℝ)
  | 1 => (-115075337 / 200000000000 : ℝ)
  | 2 => (-559270253 / 1000000000000 : ℝ)
  | 3 => (-542911189 / 1000000000000 : ℝ)
  | 4 => (-263148909 / 500000000000 : ℝ)
  | 5 => (-254714233 / 500000000000 : ℝ)
  | 6 => (-492301459 / 1000000000000 : ℝ)
  | 7 => (-118728781 / 250000000000 : ℝ)
  | 8 => (-457267789 / 1000000000000 : ℝ)
  | 9 => (-219678891 / 500000000000 : ℝ)
  | 10 => (-421183433 / 1000000000000 : ℝ)
  | 11 => (-402743071 / 1000000000000 : ℝ)
  | 12 => (-384035029 / 1000000000000 : ℝ)
  | 13 => (-9126441 / 25000000000 : ℝ)
  | 14 => (-172904619 / 500000000000 : ℝ)
  | 15 => (-326288161 / 1000000000000 : ℝ)
  | 16 => (-153246373 / 500000000000 : ℝ)
  | 17 => (-143210667 / 500000000000 : ℝ)
  | 18 => (-133036133 / 500000000000 : ℝ)
  | 19 => (-15340243 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch045Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((900 : ℝ) + (j.val : ℝ)) / 1600)
      (((900 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch045Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch045Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((900 : ℝ) + (j.val : ℝ)) / 1600)
    (((900 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch045Neg45WeightLower j.val) (hpThetaShiftTwoBatch045Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch045Neg45WeightLower, hpThetaShiftTwoBatch045Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch045Neg45_integral_bounds :
    (-272809171 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-128622531 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (900 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch045Lower hpThetaJensenCellsBatch045Upper
    hpThetaShiftTwoBatch045Neg45WeightLower hpThetaShiftTwoBatch045Neg45WeightUpper hpThetaJensenCellsBatch045_bounds hpThetaShiftTwoBatch045Neg45_weight_bounds
  have hl : (-272809171 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch045Lower j * hpThetaShiftTwoBatch045Neg45WeightLower j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftTwoBatch045Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftTwoBatch045Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch045Lower j * hpThetaShiftTwoBatch045Neg45WeightUpper j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftTwoBatch045Neg45WeightUpper j) / 1600) ≤ (-128622531 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftTwoBatch045Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (900 : ℝ) / 1600 = 45 / 80 by norm_num,
    show ((900 : ℝ) + 20) / 1600 = (45 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch045Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1921299491 / 1000000000000 : ℝ)
  | 1 => (-1935008093 / 1000000000000 : ℝ)
  | 2 => (-243591743 / 125000000000 : ℝ)
  | 3 => (-981238239 / 500000000000 : ℝ)
  | 4 => (-1976235121 / 1000000000000 : ℝ)
  | 5 => (-124375581 / 62500000000 : ℝ)
  | 6 => (-100189921 / 50000000000 : ℝ)
  | 7 => (-1008800951 / 500000000000 : ℝ)
  | 8 => (-2031419149 / 1000000000000 : ℝ)
  | 9 => (-2045249559 / 1000000000000 : ℝ)
  | 10 => (-2059092527 / 1000000000000 : ℝ)
  | 11 => (-2072947441 / 1000000000000 : ℝ)
  | 12 => (-1043406841 / 500000000000 : ℝ)
  | 13 => (-2100690629 / 1000000000000 : ℝ)
  | 14 => (-42291553 / 20000000000 : ℝ)
  | 15 => (-2128474113 / 1000000000000 : ℝ)
  | 16 => (-133898711 / 62500000000 : ℝ)
  | 17 => (-1078146397 / 500000000000 : ℝ)
  | 18 => (-135638357 / 62500000000 : ℝ)
  | 19 => (-87365659 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch045Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1907608699 / 1000000000000 : ℝ)
  | 1 => (-192129949 / 100000000000 : ℝ)
  | 2 => (-483752023 / 250000000000 : ℝ)
  | 3 => (-1948733943 / 1000000000000 : ℝ)
  | 4 => (-1962476477 / 1000000000000 : ℝ)
  | 5 => (-24702939 / 12500000000 : ℝ)
  | 6 => (-398001859 / 200000000000 : ℝ)
  | 7 => (-2003798419 / 1000000000000 : ℝ)
  | 8 => (-2017601901 / 1000000000000 : ℝ)
  | 9 => (-507854787 / 250000000000 : ℝ)
  | 10 => (-1022624779 / 500000000000 : ℝ)
  | 11 => (-1029546263 / 500000000000 : ℝ)
  | 12 => (-25911843 / 12500000000 : ℝ)
  | 13 => (-2086813681 / 1000000000000 : ℝ)
  | 14 => (-525172657 / 250000000000 : ℝ)
  | 15 => (-2114577649 / 1000000000000 : ℝ)
  | 16 => (-519647 / 244140625 : ℝ)
  | 17 => (-3427807 / 1600000000 : ℝ)
  | 18 => (-2156292793 / 1000000000000 : ℝ)
  | 19 => (-2170213711 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch045Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((900 : ℝ) + (j.val : ℝ)) / 1600)
      (((900 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch045Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch045Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((900 : ℝ) + (j.val : ℝ)) / 1600)
    (((900 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch045Neg25WeightLower j.val) (hpThetaShiftTwoBatch045Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch045Neg25WeightLower, hpThetaShiftTwoBatch045Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch045Neg25_integral_bounds :
    (-621606471 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (45 / 80 : ℝ) ((45 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-1212892137 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (900 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch045Lower hpThetaJensenCellsBatch045Upper
    hpThetaShiftTwoBatch045Neg25WeightLower hpThetaShiftTwoBatch045Neg25WeightUpper hpThetaJensenCellsBatch045_bounds hpThetaShiftTwoBatch045Neg25_weight_bounds
  have hl : (-621606471 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch045Lower j * hpThetaShiftTwoBatch045Neg25WeightLower j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftTwoBatch045Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftTwoBatch045Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch045Lower j * hpThetaShiftTwoBatch045Neg25WeightUpper j)
        (hpThetaJensenCellsBatch045Upper j * hpThetaShiftTwoBatch045Neg25WeightUpper j) / 1600) ≤ (-1212892137 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch045Lower, hpThetaJensenCellsBatch045Upper,
      hpThetaShiftTwoBatch045Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (900 : ℝ) / 1600 = 45 / 80 by norm_num,
    show ((900 : ℝ) + 20) / 1600 = (45 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch045Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch045Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch045Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch045Neg25_integral_bounds
end HodgeProofHP
