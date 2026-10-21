/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch069

/-! Exact signed weight and batch integral certificates, batch 69 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch069Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-93485234958331 / 1000000000000 : ℝ)
  | 1 => (-11767480020021 / 125000000000 : ℝ)
  | 2 => (-94798308843111 / 1000000000000 : ℝ)
  | 3 => (-95460659926571 / 1000000000000 : ℝ)
  | 4 => (-48063456202483 / 500000000000 : ℝ)
  | 5 => (-48398542673977 / 500000000000 : ℝ)
  | 6 => (-9747119790067 / 100000000000 : ℝ)
  | 7 => (-6134329330247 / 62500000000 : ℝ)
  | 8 => (-4941565939729 / 50000000000 : ℝ)
  | 9 => (-49758682902753 / 500000000000 : ℝ)
  | 10 => (-25051857441523 / 250000000000 : ℝ)
  | 11 => (-100901530202341 / 1000000000000 : ℝ)
  | 12 => (-20319937343427 / 200000000000 : ℝ)
  | 13 => (-12787739873809 / 125000000000 : ℝ)
  | 14 => (-51504123389849 / 500000000000 : ℝ)
  | 15 => (-414874759679 / 4000000000 : ℝ)
  | 16 => (-104433268323389 / 1000000000000 : ℝ)
  | 17 => (-20537500387 / 195312500 : ℝ)
  | 18 => (-10587491096303 / 100000000000 : ℝ)
  | 19 => (-26650503853957 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch069Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-9283447439297 / 100000000000 : ℝ)
  | 1 => (-9348523495833 / 100000000000 : ℝ)
  | 2 => (-94139840160167 / 1000000000000 : ℝ)
  | 3 => (-9479830884311 / 100000000000 : ℝ)
  | 4 => (-9546065992657 / 100000000000 : ℝ)
  | 5 => (-19225382480993 / 200000000000 : ℝ)
  | 6 => (-96797085347953 / 1000000000000 : ℝ)
  | 7 => (-97471197900669 / 1000000000000 : ℝ)
  | 8 => (-98149269283951 / 1000000000000 : ℝ)
  | 9 => (-98831318794579 / 1000000000000 : ℝ)
  | 10 => (-19903473161101 / 200000000000 : ℝ)
  | 11 => (-100207429766091 / 1000000000000 : ℝ)
  | 12 => (-5045076510117 / 50000000000 : ℝ)
  | 13 => (-50799843358567 / 500000000000 : ℝ)
  | 14 => (-102301918990471 / 1000000000000 : ℝ)
  | 15 => (-103008246779697 / 1000000000000 : ℝ)
  | 16 => (-103718689919749 / 1000000000000 : ℝ)
  | 17 => (-26108317080847 / 250000000000 : ℝ)
  | 18 => (-105152001981439 / 1000000000000 : ℝ)
  | 19 => (-105874910963029 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch069Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1380 : ℝ) + (j.val : ℝ)) / 1600)
      (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch069Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch069Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1380 : ℝ) + (j.val : ℝ)) / 1600)
    (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch069Neg100WeightLower j.val) (hpThetaShiftOneBatch069Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch069Neg100WeightLower, hpThetaShiftOneBatch069Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch069Neg100_integral_bounds :
    (-10090113887 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-38980487297 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch069Lower hpThetaJensenCellsBatch069Upper
    hpThetaShiftOneBatch069Neg100WeightLower hpThetaShiftOneBatch069Neg100WeightUpper hpThetaJensenCellsBatch069_bounds hpThetaShiftOneBatch069Neg100_weight_bounds
  have hl : (-10090113887 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch069Lower j * hpThetaShiftOneBatch069Neg100WeightLower j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftOneBatch069Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftOneBatch069Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch069Lower j * hpThetaShiftOneBatch069Neg100WeightUpper j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftOneBatch069Neg100WeightUpper j) / 1600) ≤ (-38980487297 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftOneBatch069Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1380 : ℝ) / 1600 = 69 / 80 by norm_num,
    show ((1380 : ℝ) + 20) / 1600 = (69 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch069Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-613045240067 / 40000000000 : ℝ)
  | 1 => (-15454082140179 / 1000000000000 : ℝ)
  | 2 => (-15582885683047 / 1000000000000 : ℝ)
  | 3 => (-15712546174831 / 1000000000000 : ℝ)
  | 4 => (-2475479403 / 156250000 : ℝ)
  | 5 => (-7987228139501 / 500000000000 : ℝ)
  | 6 => (-644268603053 / 40000000000 : ℝ)
  | 7 => (-16239849192557 / 1000000000000 : ℝ)
  | 8 => (-16373863268449 / 1000000000000 : ℝ)
  | 9 => (-16508761964179 / 1000000000000 : ℝ)
  | 10 => (-16644549959411 / 1000000000000 : ℝ)
  | 11 => (-16781231953361 / 1000000000000 : ℝ)
  | 12 => (-16918812664853 / 1000000000000 : ℝ)
  | 13 => (-1705729683239 / 100000000000 : ℝ)
  | 14 => (-1719668921421 / 100000000000 : ℝ)
  | 15 => (-8668497294177 / 500000000000 : ℝ)
  | 16 => (-4369554438181 / 250000000000 : ℝ)
  | 17 => (-352407270503 / 20000000000 : ℝ)
  | 18 => (-17763436743451 / 1000000000000 : ℝ)
  | 19 => (-17907442265501 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch069Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3039805548407 / 200000000000 : ℝ)
  | 1 => (-7663065500837 / 500000000000 : ℝ)
  | 2 => (-7727041070089 / 500000000000 : ℝ)
  | 3 => (-7791442841523 / 500000000000 : ℝ)
  | 4 => (-1571254617483 / 100000000000 : ℝ)
  | 5 => (-15843068179199 / 1000000000000 : ℝ)
  | 6 => (-15974456279001 / 1000000000000 : ℝ)
  | 7 => (-4026678769081 / 250000000000 : ℝ)
  | 8 => (-4059962298139 / 250000000000 : ℝ)
  | 9 => (-511683227139 / 31250000000 : ℝ)
  | 10 => (-8254380982089 / 500000000000 : ℝ)
  | 11 => (-1664454995941 / 100000000000 : ℝ)
  | 12 => (-209765399417 / 12500000000 : ℝ)
  | 13 => (-4229703166213 / 250000000000 : ℝ)
  | 14 => (-17057296832389 / 1000000000000 : ℝ)
  | 15 => (-17196689214209 / 1000000000000 : ℝ)
  | 16 => (-17336994588353 / 1000000000000 : ℝ)
  | 17 => (-17478217752723 / 1000000000000 : ℝ)
  | 18 => (-17620363525149 / 1000000000000 : ℝ)
  | 19 => (-355268734869 / 20000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch069Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1380 : ℝ) + (j.val : ℝ)) / 1600)
      (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch069Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch069Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1380 : ℝ) + (j.val : ℝ)) / 1600)
    (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch069Neg65WeightLower j.val) (hpThetaShiftOneBatch069Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch069Neg65WeightLower, hpThetaShiftOneBatch069Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch069Neg65_integral_bounds :
    (-13391188721 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-6458340343 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch069Lower hpThetaJensenCellsBatch069Upper
    hpThetaShiftOneBatch069Neg65WeightLower hpThetaShiftOneBatch069Neg65WeightUpper hpThetaJensenCellsBatch069_bounds hpThetaShiftOneBatch069Neg65_weight_bounds
  have hl : (-13391188721 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch069Lower j * hpThetaShiftOneBatch069Neg65WeightLower j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftOneBatch069Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftOneBatch069Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch069Lower j * hpThetaShiftOneBatch069Neg65WeightUpper j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftOneBatch069Neg65WeightUpper j) / 1600) ≤ (-6458340343 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftOneBatch069Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1380 : ℝ) / 1600 = 69 / 80 by norm_num,
    show ((1380 : ℝ) + 20) / 1600 = (69 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch069Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-373183276131 / 1000000000000 : ℝ)
  | 1 => (-96224872871 / 250000000000 : ℝ)
  | 2 => (-99183858297 / 250000000000 : ℝ)
  | 3 => (-204345950509 / 500000000000 : ℝ)
  | 4 => (-84153939719 / 200000000000 : ℝ)
  | 5 => (-432969633401 / 1000000000000 : ℝ)
  | 6 => (-445292516791 / 1000000000000 : ℝ)
  | 7 => (-228869582003 / 500000000000 : ℝ)
  | 8 => (-470310394187 / 1000000000000 : ℝ)
  | 9 => (-483007030391 / 1000000000000 : ℝ)
  | 10 => (-495829899599 / 1000000000000 : ℝ)
  | 11 => (-254389916367 / 500000000000 : ℝ)
  | 12 => (-130464416169 / 250000000000 : ℝ)
  | 13 => (-53506423427 / 100000000000 : ℝ)
  | 14 => (-109680076869 / 200000000000 : ℝ)
  | 15 => (-561866961723 / 1000000000000 : ℝ)
  | 16 => (-14386620431 / 25000000000 : ℝ)
  | 17 => (-2356779223 / 4000000000 : ℝ)
  | 18 => (-603057786149 / 1000000000000 : ℝ)
  | 19 => (-617054621379 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch069Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-72317198237 / 200000000000 : ℝ)
  | 1 => (-37318327613 / 100000000000 : ℝ)
  | 2 => (-384899491483 / 1000000000000 : ℝ)
  | 3 => (-396735433187 / 1000000000000 : ℝ)
  | 4 => (-408691901017 / 1000000000000 : ℝ)
  | 5 => (-210384849297 / 500000000000 : ℝ)
  | 6 => (-2164848167 / 5000000000 : ℝ)
  | 7 => (-44529251679 / 100000000000 : ℝ)
  | 8 => (-91547832801 / 200000000000 : ℝ)
  | 9 => (-235155197093 / 500000000000 : ℝ)
  | 10 => (-48300703039 / 100000000000 : ℝ)
  | 11 => (-247914949799 / 500000000000 : ℝ)
  | 12 => (-508779832733 / 1000000000000 : ℝ)
  | 13 => (-20874306587 / 40000000000 : ℝ)
  | 14 => (-535064234269 / 1000000000000 : ℝ)
  | 15 => (-68550048043 / 125000000000 : ℝ)
  | 16 => (-280933480861 / 500000000000 : ℝ)
  | 17 => (-575464817239 / 1000000000000 : ℝ)
  | 18 => (-589194805749 / 1000000000000 : ℝ)
  | 19 => (-150764446537 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch069Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1380 : ℝ) + (j.val : ℝ)) / 1600)
      (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch069Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch069Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1380 : ℝ) + (j.val : ℝ)) / 1600)
    (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch069Neg40WeightLower j.val) (hpThetaShiftOneBatch069Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch069Neg40WeightLower, hpThetaShiftOneBatch069Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch069Neg40_integral_bounds :
    (-392120611 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-185660117 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch069Lower hpThetaJensenCellsBatch069Upper
    hpThetaShiftOneBatch069Neg40WeightLower hpThetaShiftOneBatch069Neg40WeightUpper hpThetaJensenCellsBatch069_bounds hpThetaShiftOneBatch069Neg40_weight_bounds
  have hl : (-392120611 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch069Lower j * hpThetaShiftOneBatch069Neg40WeightLower j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftOneBatch069Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftOneBatch069Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch069Lower j * hpThetaShiftOneBatch069Neg40WeightUpper j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftOneBatch069Neg40WeightUpper j) / 1600) ≤ (-185660117 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftOneBatch069Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1380 : ℝ) / 1600 = 69 / 80 by norm_num,
    show ((1380 : ℝ) + 20) / 1600 = (69 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch069Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (263399435599 / 1000000000000 : ℝ)
  | 1 => (265365592353 / 1000000000000 : ℝ)
  | 2 => (267336648849 / 1000000000000 : ℝ)
  | 3 => (269312580917 / 1000000000000 : ℝ)
  | 4 => (135646682049 / 500000000000 : ℝ)
  | 5 => (68319743411 / 250000000000 : ℝ)
  | 6 => (68817346129 / 250000000000 : ℝ)
  | 7 => (34658071423 / 125000000000 : ℝ)
  | 8 => (139632254311 / 500000000000 : ℝ)
  | 9 => (281269170313 / 1000000000000 : ℝ)
  | 10 => (885245407 / 3125000000 : ℝ)
  | 11 => (285292561891 / 1000000000000 : ℝ)
  | 12 => (287311238453 / 1000000000000 : ℝ)
  | 13 => (144667266407 / 500000000000 : ℝ)
  | 14 => (291362417559 / 1000000000000 : ℝ)
  | 15 => (293394864971 / 1000000000000 : ℝ)
  | 16 => (295431847027 / 1000000000000 : ℝ)
  | 17 => (297473335399 / 1000000000000 : ℝ)
  | 18 => (5990386029 / 20000000000 : ℝ)
  | 19 => (75392429059 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch069Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (132682796177 / 500000000000 : ℝ)
  | 1 => (5346732977 / 20000000000 : ℝ)
  | 2 => (134656290459 / 500000000000 : ℝ)
  | 3 => (271293364099 / 1000000000000 : ℝ)
  | 4 => (54655794729 / 200000000000 : ℝ)
  | 5 => (275269384517 / 1000000000000 : ℝ)
  | 6 => (55452914277 / 200000000000 : ℝ)
  | 7 => (279264508623 / 1000000000000 : ℝ)
  | 8 => (140634585157 / 500000000000 : ℝ)
  | 9 => (283278530241 / 1000000000000 : ℝ)
  | 10 => (71323140473 / 250000000000 : ℝ)
  | 11 => (143655619227 / 500000000000 : ℝ)
  | 12 => (57866906563 / 200000000000 : ℝ)
  | 13 => (7284060439 / 25000000000 : ℝ)
  | 14 => (73348716243 / 250000000000 : ℝ)
  | 15 => (73857961757 / 250000000000 : ℝ)
  | 16 => (1487366677 / 5000000000 : ℝ)
  | 17 => (299519301451 / 1000000000000 : ℝ)
  | 18 => (301569716237 / 1000000000000 : ℝ)
  | 19 => (151812275251 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch069Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1380 : ℝ) + (j.val : ℝ)) / 1600)
      (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch069Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch069Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1380 : ℝ) + (j.val : ℝ)) / 1600)
    (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch069Neg20WeightLower j.val) (hpThetaShiftOneBatch069Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch069Neg20WeightLower, hpThetaShiftOneBatch069Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch069Neg20_integral_bounds :
    (221779229 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (114838557 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch069Lower hpThetaJensenCellsBatch069Upper
    hpThetaShiftOneBatch069Neg20WeightLower hpThetaShiftOneBatch069Neg20WeightUpper hpThetaJensenCellsBatch069_bounds hpThetaShiftOneBatch069Neg20_weight_bounds
  have hl : (221779229 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch069Lower j * hpThetaShiftOneBatch069Neg20WeightLower j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftOneBatch069Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftOneBatch069Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch069Lower j * hpThetaShiftOneBatch069Neg20WeightUpper j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftOneBatch069Neg20WeightUpper j) / 1600) ≤ (114838557 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftOneBatch069Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1380 : ℝ) / 1600 = 69 / 80 by norm_num,
    show ((1380 : ℝ) + 20) / 1600 = (69 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch069Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch069Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch069Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch069Neg20_integral_bounds
end HodgeProofHP
