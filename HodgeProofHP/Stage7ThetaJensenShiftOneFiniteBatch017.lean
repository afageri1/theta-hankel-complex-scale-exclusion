/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch017

/-! Exact signed weight and batch integral certificates, batch 17 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch017Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-7973582317 / 1000000000000 : ℝ)
  | 1 => (-8092678577 / 1000000000000 : ℝ)
  | 2 => (-1642372911 / 200000000000 : ℝ)
  | 3 => (-8331121711 / 1000000000000 : ℝ)
  | 4 => (-845043129 / 100000000000 : ℝ)
  | 5 => (-8569774317 / 1000000000000 : ℝ)
  | 6 => (-4344565801 / 500000000000 : ℝ)
  | 7 => (-8808483737 / 1000000000000 : ℝ)
  | 8 => (-4463905549 / 500000000000 : ℝ)
  | 9 => (-2261773461 / 250000000000 : ℝ)
  | 10 => (-9166311917 / 1000000000000 : ℝ)
  | 11 => (-2321361261 / 250000000000 : ℝ)
  | 12 => (-1880894547 / 200000000000 : ℝ)
  | 13 => (-1904674857 / 200000000000 : ℝ)
  | 14 => (-9642128773 / 1000000000000 : ℝ)
  | 15 => (-1220089383 / 125000000000 : ℝ)
  | 16 => (-9879111807 / 1000000000000 : ℝ)
  | 17 => (-9997297437 / 1000000000000 : ℝ)
  | 18 => (-4939087 / 488281250 : ℝ)
  | 19 => (-10232948031 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch017Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3927297047 / 500000000000 : ℝ)
  | 1 => (-1993395579 / 250000000000 : ℝ)
  | 2 => (-505792411 / 62500000000 : ℝ)
  | 3 => (-4105932277 / 500000000000 : ℝ)
  | 4 => (-833112171 / 100000000000 : ℝ)
  | 5 => (-8450431289 / 1000000000000 : ℝ)
  | 6 => (-2142443579 / 250000000000 : ℝ)
  | 7 => (-8689131601 / 1000000000000 : ℝ)
  | 8 => (-1101060467 / 125000000000 : ℝ)
  | 9 => (-8927811097 / 1000000000000 : ℝ)
  | 10 => (-9047093843 / 1000000000000 : ℝ)
  | 11 => (-2291577979 / 250000000000 : ℝ)
  | 12 => (-9285445043 / 1000000000000 : ℝ)
  | 13 => (-4702236367 / 500000000000 : ℝ)
  | 14 => (-2380843571 / 250000000000 : ℝ)
  | 15 => (-2410532193 / 250000000000 : ℝ)
  | 16 => (-9760715063 / 1000000000000 : ℝ)
  | 17 => (-4939555903 / 500000000000 : ℝ)
  | 18 => (-2499324359 / 250000000000 : ℝ)
  | 19 => (-404610007 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch017Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((340 : ℝ) + (j.val : ℝ)) / 1600)
      (((340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch017Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch017Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((340 : ℝ) + (j.val : ℝ)) / 1600)
    (((340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch017Neg100WeightLower j.val) (hpThetaShiftOneBatch017Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch017Neg100WeightLower, hpThetaShiftOneBatch017Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch017Neg100_integral_bounds :
    (-128982336093 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-62883210437 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch017Lower hpThetaJensenCellsBatch017Upper
    hpThetaShiftOneBatch017Neg100WeightLower hpThetaShiftOneBatch017Neg100WeightUpper hpThetaJensenCellsBatch017_bounds hpThetaShiftOneBatch017Neg100_weight_bounds
  have hl : (-128982336093 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch017Lower j * hpThetaShiftOneBatch017Neg100WeightLower j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftOneBatch017Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftOneBatch017Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch017Lower j * hpThetaShiftOneBatch017Neg100WeightUpper j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftOneBatch017Neg100WeightUpper j) / 1600) ≤ (-62883210437 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftOneBatch017Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (340 : ℝ) / 1600 = 17 / 80 by norm_num,
    show ((340 : ℝ) + 20) / 1600 = (17 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch017Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-806414029 / 500000000000 : ℝ)
  | 1 => (-428870179 / 250000000000 : ℝ)
  | 2 => (-56843129 / 31250000000 : ℝ)
  | 3 => (-38466447 / 20000000000 : ℝ)
  | 4 => (-2028503317 / 1000000000000 : ℝ)
  | 5 => (-33351857 / 15625000000 : ℝ)
  | 6 => (-2241364641 / 1000000000000 : ℝ)
  | 7 => (-2349036273 / 1000000000000 : ℝ)
  | 8 => (-1228764601 / 500000000000 : ℝ)
  | 9 => (-641709691 / 250000000000 : ℝ)
  | 10 => (-669240043 / 250000000000 : ℝ)
  | 11 => (-69697213 / 25000000000 : ℝ)
  | 12 => (-115984751 / 40000000000 : ℝ)
  | 13 => (-1506072893 / 500000000000 : ℝ)
  | 14 => (-3125464273 / 1000000000000 : ℝ)
  | 15 => (-809892209 / 250000000000 : ℝ)
  | 16 => (-3354453949 / 1000000000000 : ℝ)
  | 17 => (-86752849 / 25000000000 : ℝ)
  | 18 => (-3586543093 / 1000000000000 : ℝ)
  | 19 => (-1851867723 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch017Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1511025979 / 1000000000000 : ℝ)
  | 1 => (-1612828057 / 1000000000000 : ℝ)
  | 2 => (-343096143 / 200000000000 : ℝ)
  | 3 => (-1818980127 / 1000000000000 : ℝ)
  | 4 => (-1923322349 / 1000000000000 : ℝ)
  | 5 => (-507125829 / 250000000000 : ℝ)
  | 6 => (-2134518847 / 1000000000000 : ℝ)
  | 7 => (-14008529 / 6250000000 : ℝ)
  | 8 => (-146814767 / 62500000000 : ℝ)
  | 9 => (-2457529201 / 1000000000000 : ℝ)
  | 10 => (-2566838763 / 1000000000000 : ℝ)
  | 11 => (-2676960171 / 1000000000000 : ℝ)
  | 12 => (-2787888519 / 1000000000000 : ℝ)
  | 13 => (-1449809387 / 500000000000 : ℝ)
  | 14 => (-602429157 / 200000000000 : ℝ)
  | 15 => (-195341517 / 62500000000 : ℝ)
  | 16 => (-647913767 / 200000000000 : ℝ)
  | 17 => (-838613487 / 250000000000 : ℝ)
  | 18 => (-3470113959 / 1000000000000 : ℝ)
  | 19 => (-896635773 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch017Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((340 : ℝ) + (j.val : ℝ)) / 1600)
      (((340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch017Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch017Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((340 : ℝ) + (j.val : ℝ)) / 1600)
    (((340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch017Neg65WeightLower j.val) (hpThetaShiftOneBatch017Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch017Neg65WeightLower, hpThetaShiftOneBatch017Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch017Neg65_integral_bounds :
    (-37232675747 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-3524997271 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch017Lower hpThetaJensenCellsBatch017Upper
    hpThetaShiftOneBatch017Neg65WeightLower hpThetaShiftOneBatch017Neg65WeightUpper hpThetaJensenCellsBatch017_bounds hpThetaShiftOneBatch017Neg65_weight_bounds
  have hl : (-37232675747 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch017Lower j * hpThetaShiftOneBatch017Neg65WeightLower j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftOneBatch017Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftOneBatch017Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch017Lower j * hpThetaShiftOneBatch017Neg65WeightUpper j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftOneBatch017Neg65WeightUpper j) / 1600) ≤ (-3524997271 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftOneBatch017Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (340 : ℝ) / 1600 = 17 / 80 by norm_num,
    show ((340 : ℝ) + 20) / 1600 = (17 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch017Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (708215787 / 125000000000 : ℝ)
  | 1 => (561864173 / 100000000000 : ℝ)
  | 2 => (111414103 / 20000000000 : ℝ)
  | 3 => (5521914103 / 1000000000000 : ℝ)
  | 4 => (5472266181 / 1000000000000 : ℝ)
  | 5 => (5421759017 / 1000000000000 : ℝ)
  | 6 => (2685195147 / 500000000000 : ℝ)
  | 7 => (2659078867 / 500000000000 : ℝ)
  | 8 => (1316264777 / 250000000000 : ℝ)
  | 9 => (521109223 / 100000000000 : ℝ)
  | 10 => (5156254963 / 1000000000000 : ℝ)
  | 11 => (5100545213 / 1000000000000 : ℝ)
  | 12 => (5043960933 / 1000000000000 : ℝ)
  | 13 => (1246625031 / 250000000000 : ℝ)
  | 14 => (985632167 / 200000000000 : ℝ)
  | 15 => (4868941159 / 1000000000000 : ℝ)
  | 16 => (4808839241 / 1000000000000 : ℝ)
  | 17 => (4747853271 / 1000000000000 : ℝ)
  | 18 => (4685981489 / 1000000000000 : ℝ)
  | 19 => (924644437 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch017Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5711961343 / 1000000000000 : ℝ)
  | 1 => (5665726297 / 1000000000000 : ℝ)
  | 2 => (5618641731 / 1000000000000 : ℝ)
  | 3 => (5570705151 / 1000000000000 : ℝ)
  | 4 => (690239263 / 125000000000 : ℝ)
  | 5 => (2736133091 / 500000000000 : ℝ)
  | 6 => (2710879509 / 500000000000 : ℝ)
  | 7 => (1074078059 / 200000000000 : ℝ)
  | 8 => (1063631547 / 200000000000 : ℝ)
  | 9 => (5265059109 / 1000000000000 : ℝ)
  | 10 => (5211092231 / 1000000000000 : ℝ)
  | 11 => (1289063741 / 250000000000 : ℝ)
  | 12 => (2550272607 / 500000000000 : ℝ)
  | 13 => (2521980467 / 500000000000 : ℝ)
  | 14 => (39892001 / 8000000000 : ℝ)
  | 15 => (1232040209 / 250000000000 : ℝ)
  | 16 => (121723529 / 25000000000 : ℝ)
  | 17 => (2404419621 / 500000000000 : ℝ)
  | 18 => (593481659 / 125000000000 : ℝ)
  | 19 => (468598149 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch017Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((340 : ℝ) + (j.val : ℝ)) / 1600)
      (((340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch017Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch017Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((340 : ℝ) + (j.val : ℝ)) / 1600)
    (((340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch017Neg40WeightLower j.val) (hpThetaShiftOneBatch017Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch017Neg40WeightLower, hpThetaShiftOneBatch017Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch017Neg40_integral_bounds :
    (36250168937 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (74152481369 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch017Lower hpThetaJensenCellsBatch017Upper
    hpThetaShiftOneBatch017Neg40WeightLower hpThetaShiftOneBatch017Neg40WeightUpper hpThetaJensenCellsBatch017_bounds hpThetaShiftOneBatch017Neg40_weight_bounds
  have hl : (36250168937 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch017Lower j * hpThetaShiftOneBatch017Neg40WeightLower j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftOneBatch017Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftOneBatch017Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch017Lower j * hpThetaShiftOneBatch017Neg40WeightUpper j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftOneBatch017Neg40WeightUpper j) / 1600) ≤ (74152481369 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftOneBatch017Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (340 : ℝ) / 1600 = 17 / 80 by norm_num,
    show ((340 : ℝ) + 20) / 1600 = (17 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch017Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (13283666207 / 1000000000000 : ℝ)
  | 1 => (6656047873 / 500000000000 : ℝ)
  | 2 => (13340083343 / 1000000000000 : ℝ)
  | 3 => (13367625421 / 1000000000000 : ℝ)
  | 4 => (13394718407 / 1000000000000 : ℝ)
  | 5 => (13421358731 / 1000000000000 : ℝ)
  | 6 => (1344754283 / 100000000000 : ℝ)
  | 7 => (13473267143 / 1000000000000 : ℝ)
  | 8 => (3374632029 / 250000000000 : ℝ)
  | 9 => (6761661099 / 500000000000 : ℝ)
  | 10 => (3386911461 / 250000000000 : ℝ)
  | 11 => (13571495513 / 1000000000000 : ℝ)
  | 12 => (13594867671 / 1000000000000 : ℝ)
  | 13 => (3404439697 / 250000000000 : ℝ)
  | 14 => (13640165339 / 1000000000000 : ℝ)
  | 15 => (6831041903 / 500000000000 : ℝ)
  | 16 => (547340427 / 40000000000 : ℝ)
  | 17 => (342611061 / 25000000000 : ℝ)
  | 18 => (6862437799 / 500000000000 : ℝ)
  | 19 => (6872403327 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch017Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (13312095747 / 1000000000000 : ℝ)
  | 1 => (833755209 / 62500000000 : ℝ)
  | 2 => (6683812711 / 500000000000 : ℝ)
  | 3 => (1674339801 / 125000000000 : ℝ)
  | 4 => (3355339683 / 250000000000 : ℝ)
  | 5 => (13447542831 / 1000000000000 : ℝ)
  | 6 => (1684158393 / 125000000000 : ℝ)
  | 7 => (13498528117 / 1000000000000 : ℝ)
  | 8 => (13523322199 / 1000000000000 : ℝ)
  | 9 => (2709529169 / 200000000000 : ℝ)
  | 10 => (6785747757 / 500000000000 : ℝ)
  | 11 => (1699358459 / 125000000000 : ℝ)
  | 12 => (13617758789 / 1000000000000 : ℝ)
  | 13 => (682008267 / 50000000000 : ℝ)
  | 14 => (13662083807 / 1000000000000 : ℝ)
  | 15 => (3420877669 / 250000000000 : ℝ)
  | 16 => (13704442441 / 1000000000000 : ℝ)
  | 17 => (13724875599 / 1000000000000 : ℝ)
  | 18 => (2748961331 / 200000000000 : ℝ)
  | 19 => (13764232119 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch017Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((340 : ℝ) + (j.val : ℝ)) / 1600)
      (((340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch017Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch017Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((340 : ℝ) + (j.val : ℝ)) / 1600)
    (((340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch017Neg20WeightLower j.val) (hpThetaShiftOneBatch017Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch017Neg20WeightLower, hpThetaShiftOneBatch017Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch017Neg20_integral_bounds :
    (47378988341 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (17 / 80 : ℝ) ((17 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (19216137397 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch017Lower hpThetaJensenCellsBatch017Upper
    hpThetaShiftOneBatch017Neg20WeightLower hpThetaShiftOneBatch017Neg20WeightUpper hpThetaJensenCellsBatch017_bounds hpThetaShiftOneBatch017Neg20_weight_bounds
  have hl : (47378988341 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch017Lower j * hpThetaShiftOneBatch017Neg20WeightLower j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftOneBatch017Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftOneBatch017Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch017Lower j * hpThetaShiftOneBatch017Neg20WeightUpper j)
        (hpThetaJensenCellsBatch017Upper j * hpThetaShiftOneBatch017Neg20WeightUpper j) / 1600) ≤ (19216137397 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch017Lower, hpThetaJensenCellsBatch017Upper,
      hpThetaShiftOneBatch017Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (340 : ℝ) / 1600 = 17 / 80 by norm_num,
    show ((340 : ℝ) + 20) / 1600 = (17 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch017Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch017Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch017Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch017Neg20_integral_bounds
end HodgeProofHP
