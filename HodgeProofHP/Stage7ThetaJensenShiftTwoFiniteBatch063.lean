/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch063

/-! Exact signed weight and batch integral certificates, batch 63 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch063Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-241593691137 / 250000000000 : ℝ)
  | 1 => (-122069012333 / 125000000000 : ℝ)
  | 2 => (-986820626037 / 1000000000000 : ℝ)
  | 3 => (-498590520627 / 500000000000 : ℝ)
  | 4 => (-503817021681 / 500000000000 : ℝ)
  | 5 => (-254545083973 / 250000000000 : ℝ)
  | 6 => (-514410313443 / 500000000000 : ℝ)
  | 7 => (-519777814457 / 500000000000 : ℝ)
  | 8 => (-1050386059107 / 1000000000000 : ℝ)
  | 9 => (-265328159793 / 250000000000 : ℝ)
  | 10 => (-536168047713 / 500000000000 : ℝ)
  | 11 => (-1083457158811 / 1000000000000 : ℝ)
  | 12 => (-273669141231 / 250000000000 : ℝ)
  | 13 => (-276498763511 / 250000000000 : ℝ)
  | 14 => (-1117413371147 / 1000000000000 : ℝ)
  | 15 => (-564466132971 / 500000000000 : ℝ)
  | 16 => (-114055249289 / 100000000000 : ℝ)
  | 17 => (-288068702807 / 250000000000 : ℝ)
  | 18 => (-582049992499 / 500000000000 : ℝ)
  | 19 => (-1176028783069 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch063Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-956287933539 / 1000000000000 : ℝ)
  | 1 => (-966374764547 / 1000000000000 : ℝ)
  | 2 => (-976552098663 / 1000000000000 : ℝ)
  | 3 => (-246705156509 / 250000000000 : ℝ)
  | 4 => (-997181041253 / 1000000000000 : ℝ)
  | 5 => (-1007634043361 / 1000000000000 : ℝ)
  | 6 => (-1018180335891 / 1000000000000 : ℝ)
  | 7 => (-205764125377 / 200000000000 : ℝ)
  | 8 => (-1039555628913 / 1000000000000 : ℝ)
  | 9 => (-525193029553 / 500000000000 : ℝ)
  | 10 => (-1061312639171 / 1000000000000 : ℝ)
  | 11 => (-42893443817 / 40000000000 : ℝ)
  | 12 => (-108345715881 / 100000000000 : ℝ)
  | 13 => (-1094676564923 / 1000000000000 : ℝ)
  | 14 => (-1105995054043 / 1000000000000 : ℝ)
  | 15 => (-558706685573 / 500000000000 : ℝ)
  | 16 => (-1128932265941 / 1000000000000 : ℝ)
  | 17 => (-1140552492889 / 1000000000000 : ℝ)
  | 18 => (-1152274811227 / 1000000000000 : ℝ)
  | 19 => (-1164099984997 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch063Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1260 : ℝ) + (j.val : ℝ)) / 1600)
      (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch063Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch063Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1260 : ℝ) + (j.val : ℝ)) / 1600)
    (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch063Neg100WeightLower j.val) (hpThetaShiftTwoBatch063Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch063Neg100WeightLower, hpThetaShiftTwoBatch063Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch063Neg100_integral_bounds :
    (-7262604543 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-7011875457 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch063Lower hpThetaJensenCellsBatch063Upper
    hpThetaShiftTwoBatch063Neg100WeightLower hpThetaShiftTwoBatch063Neg100WeightUpper hpThetaJensenCellsBatch063_bounds hpThetaShiftTwoBatch063Neg100_weight_bounds
  have hl : (-7262604543 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch063Lower j * hpThetaShiftTwoBatch063Neg100WeightLower j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftTwoBatch063Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftTwoBatch063Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch063Lower j * hpThetaShiftTwoBatch063Neg100WeightUpper j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftTwoBatch063Neg100WeightUpper j) / 1600) ≤ (-7011875457 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftTwoBatch063Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1260 : ℝ) / 1600 = 63 / 80 by norm_num,
    show ((1260 : ℝ) + 20) / 1600 = (63 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch063Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3694701099 / 50000000000 : ℝ)
  | 1 => (-4699154801 / 62500000000 : ℝ)
  | 2 => (-38247073437 / 500000000000 : ℝ)
  | 3 => (-622537359 / 8000000000 : ℝ)
  | 4 => (-19788921133 / 250000000000 : ℝ)
  | 5 => (-40254915279 / 500000000000 : ℝ)
  | 6 => (-81879748673 / 1000000000000 : ℝ)
  | 7 => (-83265580607 / 1000000000000 : ℝ)
  | 8 => (-21166867277 / 250000000000 : ℝ)
  | 9 => (-86085557947 / 1000000000000 : ℝ)
  | 10 => (-87519991923 / 1000000000000 : ℝ)
  | 11 => (-88970916873 / 1000000000000 : ℝ)
  | 12 => (-9043847967 / 100000000000 : ℝ)
  | 13 => (-91922828237 / 1000000000000 : ℝ)
  | 14 => (-1868482231 / 20000000000 : ℝ)
  | 15 => (-94942479643 / 1000000000000 : ℝ)
  | 16 => (-48239041807 / 500000000000 : ℝ)
  | 17 => (-98031075633 / 1000000000000 : ℝ)
  | 18 => (-49800804473 / 500000000000 : ℝ)
  | 19 => (-25297459471 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch063Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-14523329127 / 200000000000 : ℝ)
  | 1 => (-73894021979 / 1000000000000 : ℝ)
  | 2 => (-15037295363 / 200000000000 : ℝ)
  | 3 => (-76494146873 / 1000000000000 : ℝ)
  | 4 => (-38908584937 / 500000000000 : ℝ)
  | 5 => (-79155684531 / 1000000000000 : ℝ)
  | 6 => (-80509830557 / 1000000000000 : ℝ)
  | 7 => (-1279371073 / 15625000000 : ℝ)
  | 8 => (-41632790303 / 500000000000 : ℝ)
  | 9 => (-84667469107 / 1000000000000 : ℝ)
  | 10 => (-43042778973 / 500000000000 : ℝ)
  | 11 => (-43759995961 / 500000000000 : ℝ)
  | 12 => (-11121364609 / 125000000000 : ℝ)
  | 13 => (-90438479669 / 1000000000000 : ℝ)
  | 14 => (-22980707059 / 250000000000 : ℝ)
  | 15 => (-93424111549 / 1000000000000 : ℝ)
  | 16 => (-47471239821 / 500000000000 : ℝ)
  | 17 => (-96478083613 / 1000000000000 : ℝ)
  | 18 => (-6126942227 / 62500000000 : ℝ)
  | 19 => (-19920321789 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch063Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1260 : ℝ) + (j.val : ℝ)) / 1600)
      (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch063Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch063Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1260 : ℝ) + (j.val : ℝ)) / 1600)
    (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch063Neg65WeightLower j.val) (hpThetaShiftTwoBatch063Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch063Neg65WeightLower, hpThetaShiftTwoBatch063Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch063Neg65_integral_bounds :
    (-589904593 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-565991097 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch063Lower hpThetaJensenCellsBatch063Upper
    hpThetaShiftTwoBatch063Neg65WeightLower hpThetaShiftTwoBatch063Neg65WeightUpper hpThetaJensenCellsBatch063_bounds hpThetaShiftTwoBatch063Neg65_weight_bounds
  have hl : (-589904593 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch063Lower j * hpThetaShiftTwoBatch063Neg65WeightLower j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftTwoBatch063Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftTwoBatch063Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch063Lower j * hpThetaShiftTwoBatch063Neg65WeightUpper j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftTwoBatch063Neg65WeightUpper j) / 1600) ≤ (-565991097 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftTwoBatch063Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1260 : ℝ) / 1600 = 63 / 80 by norm_num,
    show ((1260 : ℝ) + 20) / 1600 = (63 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch063Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4434912797 / 200000000000 : ℝ)
  | 1 => (11099972163 / 500000000000 : ℝ)
  | 2 => (4444733537 / 200000000000 : ℝ)
  | 3 => (11122854173 / 500000000000 : ℝ)
  | 4 => (22266040357 / 1000000000000 : ℝ)
  | 5 => (891385501 / 40000000000 : ℝ)
  | 6 => (22301473417 / 1000000000000 : ℝ)
  | 7 => (278956517 / 12500000000 : ℝ)
  | 8 => (22329754433 / 1000000000000 : ℝ)
  | 9 => (22341145473 / 1000000000000 : ℝ)
  | 10 => (22350667069 / 1000000000000 : ℝ)
  | 11 => (11179145781 / 500000000000 : ℝ)
  | 12 => (22363991041 / 1000000000000 : ℝ)
  | 13 => (11183868673 / 500000000000 : ℝ)
  | 14 => (11184628257 / 500000000000 : ℝ)
  | 15 => (1118348589 / 50000000000 : ℝ)
  | 16 => (1397663667 / 62500000000 : ℝ)
  | 17 => (349315121 / 15625000000 : ℝ)
  | 18 => (2793448661 / 125000000000 : ℝ)
  | 19 => (22336853333 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch063Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (22199944327 / 1000000000000 : ℝ)
  | 1 => (11111833843 / 500000000000 : ℝ)
  | 2 => (22245708347 / 1000000000000 : ℝ)
  | 3 => (11133020179 / 500000000000 : ℝ)
  | 4 => (11142318763 / 500000000000 : ℝ)
  | 5 => (11150736709 / 500000000000 : ℝ)
  | 6 => (22316521361 / 1000000000000 : ℝ)
  | 7 => (11164877217 / 500000000000 : ℝ)
  | 8 => (11170572737 / 500000000000 : ℝ)
  | 9 => (2235066707 / 100000000000 : ℝ)
  | 10 => (22358291563 / 1000000000000 : ℝ)
  | 11 => (11181995521 / 500000000000 : ℝ)
  | 12 => (22367737347 / 1000000000000 : ℝ)
  | 13 => (22369502061 / 1000000000000 : ℝ)
  | 14 => (22369673639 / 1000000000000 : ℝ)
  | 15 => (4473851303 / 200000000000 : ℝ)
  | 16 => (22366971781 / 1000000000000 : ℝ)
  | 17 => (22362618673 / 1000000000000 : ℝ)
  | 18 => (4471233549 / 200000000000 : ℝ)
  | 19 => (22347589289 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch063Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1260 : ℝ) + (j.val : ℝ)) / 1600)
      (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch063Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch063Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1260 : ℝ) + (j.val : ℝ)) / 1600)
    (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch063Neg45WeightLower j.val) (hpThetaShiftTwoBatch063Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch063Neg45WeightLower, hpThetaShiftTwoBatch063Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch063Neg45_integral_bounds :
    (7437781 / 50000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (76284939 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch063Lower hpThetaJensenCellsBatch063Upper
    hpThetaShiftTwoBatch063Neg45WeightLower hpThetaShiftTwoBatch063Neg45WeightUpper hpThetaJensenCellsBatch063_bounds hpThetaShiftTwoBatch063Neg45_weight_bounds
  have hl : (7437781 / 50000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch063Lower j * hpThetaShiftTwoBatch063Neg45WeightLower j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftTwoBatch063Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftTwoBatch063Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch063Lower j * hpThetaShiftTwoBatch063Neg45WeightUpper j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftTwoBatch063Neg45WeightUpper j) / 1600) ≤ (76284939 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftTwoBatch063Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1260 : ℝ) / 1600 = 63 / 80 by norm_num,
    show ((1260 : ℝ) + 20) / 1600 = (63 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch063Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (666370043 / 1000000000000 : ℝ)
  | 1 => (146104173 / 200000000000 : ℝ)
  | 2 => (99404411 / 125000000000 : ℝ)
  | 3 => (430257707 / 500000000000 : ℝ)
  | 4 => (926363339 / 1000000000000 : ℝ)
  | 5 => (992781153 / 1000000000000 : ℝ)
  | 6 => (1059770941 / 1000000000000 : ℝ)
  | 7 => (56366739 / 50000000000 : ℝ)
  | 8 => (59773737 / 50000000000 : ℝ)
  | 9 => (632096443 / 500000000000 : ℝ)
  | 10 => (333372819 / 250000000000 : ℝ)
  | 11 => (1403371959 / 1000000000000 : ℝ)
  | 12 => (1473836979 / 1000000000000 : ℝ)
  | 13 => (1544888371 / 1000000000000 : ℝ)
  | 14 => (323305633 / 200000000000 : ℝ)
  | 15 => (1688758381 / 1000000000000 : ℝ)
  | 16 => (1761581033 / 1000000000000 : ℝ)
  | 17 => (2935997 / 1600000000 : ℝ)
  | 18 => (381802331 / 200000000000 : ℝ)
  | 19 => (1983623613 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch063Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (365260433 / 500000000000 : ℝ)
  | 1 => (795235289 / 1000000000000 : ℝ)
  | 2 => (172103083 / 200000000000 : ℝ)
  | 3 => (46318167 / 50000000000 : ℝ)
  | 4 => (496390577 / 500000000000 : ℝ)
  | 5 => (529885471 / 500000000000 : ℝ)
  | 6 => (1127334781 / 1000000000000 : ℝ)
  | 7 => (1195474741 / 1000000000000 : ℝ)
  | 8 => (1264192887 / 1000000000000 : ℝ)
  | 9 => (1333491277 / 1000000000000 : ℝ)
  | 10 => (35084299 / 25000000000 : ℝ)
  | 11 => (73691849 / 50000000000 : ℝ)
  | 12 => (386222093 / 250000000000 : ℝ)
  | 13 => (808264083 / 500000000000 : ℝ)
  | 14 => (844379191 / 500000000000 : ℝ)
  | 15 => (880790517 / 500000000000 : ℝ)
  | 16 => (917499063 / 500000000000 : ℝ)
  | 17 => (238626457 / 125000000000 : ℝ)
  | 18 => (991811807 / 500000000000 : ℝ)
  | 19 => (2058835979 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch063Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1260 : ℝ) + (j.val : ℝ)) / 1600)
      (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch063Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch063Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1260 : ℝ) + (j.val : ℝ)) / 1600)
    (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch063Neg25WeightLower j.val) (hpThetaShiftTwoBatch063Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch063Neg25WeightLower, hpThetaShiftTwoBatch063Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch063Neg25_integral_bounds :
    (8475473 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (9162257 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch063Lower hpThetaJensenCellsBatch063Upper
    hpThetaShiftTwoBatch063Neg25WeightLower hpThetaShiftTwoBatch063Neg25WeightUpper hpThetaJensenCellsBatch063_bounds hpThetaShiftTwoBatch063Neg25_weight_bounds
  have hl : (8475473 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch063Lower j * hpThetaShiftTwoBatch063Neg25WeightLower j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftTwoBatch063Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftTwoBatch063Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch063Lower j * hpThetaShiftTwoBatch063Neg25WeightUpper j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftTwoBatch063Neg25WeightUpper j) / 1600) ≤ (9162257 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftTwoBatch063Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1260 : ℝ) / 1600 = 63 / 80 by norm_num,
    show ((1260 : ℝ) + 20) / 1600 = (63 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch063Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch063Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch063Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch063Neg25_integral_bounds
end HodgeProofHP
