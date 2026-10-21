/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch070

/-! Exact signed weight and batch integral certificates, batch 70 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch070Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-21466667113257 / 200000000000 : ℝ)
  | 1 => (-108068891719873 / 1000000000000 : ℝ)
  | 2 => (-108808704261327 / 1000000000000 : ℝ)
  | 3 => (-27388198413721 / 250000000000 : ℝ)
  | 4 => (-6893823777783 / 62500000000 : ℝ)
  | 5 => (-111053885254231 / 1000000000000 : ℝ)
  | 6 => (-111810928788197 / 1000000000000 : ℝ)
  | 7 => (-112572331831101 / 1000000000000 : ℝ)
  | 8 => (-113338115248341 / 1000000000000 : ℝ)
  | 9 => (-28527074996569 / 250000000000 : ℝ)
  | 10 => (-14360363384059 / 125000000000 : ℝ)
  | 11 => (-2313239152319 / 20000000000 : ℝ)
  | 12 => (-116445472807433 / 1000000000000 : ℝ)
  | 13 => (-29308368479897 / 250000000000 : ℝ)
  | 14 => (-59012991153639 / 500000000000 : ℝ)
  | 15 => (-118823019407807 / 1000000000000 : ℝ)
  | 16 => (-119624606741171 / 1000000000000 : ℝ)
  | 17 => (-120430765910303 / 1000000000000 : ℝ)
  | 18 => (-121241518601327 / 1000000000000 : ℝ)
  | 19 => (-61028443291903 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch070Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-106602015415827 / 1000000000000 : ℝ)
  | 1 => (-26833333891571 / 250000000000 : ℝ)
  | 2 => (-1688576433123 / 15625000000 : ℝ)
  | 3 => (-54404352130663 / 500000000000 : ℝ)
  | 4 => (-109552793654883 / 1000000000000 : ℝ)
  | 5 => (-110301180444527 / 1000000000000 : ℝ)
  | 6 => (-11105388525423 / 100000000000 : ℝ)
  | 7 => (-27952732197049 / 250000000000 : ℝ)
  | 8 => (-1125723318311 / 10000000000 : ℝ)
  | 9 => (-5666905762417 / 50000000000 : ℝ)
  | 10 => (-4564331999451 / 40000000000 : ℝ)
  | 11 => (-114882907072471 / 1000000000000 : ℝ)
  | 12 => (-115661957615949 / 1000000000000 : ℝ)
  | 13 => (-14555684100929 / 125000000000 : ℝ)
  | 14 => (-117233473919587 / 1000000000000 : ℝ)
  | 15 => (-118025982307277 / 1000000000000 : ℝ)
  | 16 => (-59411509703903 / 500000000000 : ℝ)
  | 17 => (-11962460674117 / 100000000000 : ℝ)
  | 18 => (-60215382955151 / 500000000000 : ℝ)
  | 19 => (-60620759300663 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch070Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1400 : ℝ) + (j.val : ℝ)) / 1600)
      (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch070Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch070Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1400 : ℝ) + (j.val : ℝ)) / 1600)
    (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch070Neg100WeightLower j.val) (hpThetaShiftOneBatch070Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch070Neg100WeightLower, hpThetaShiftOneBatch070Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch070Neg100_integral_bounds :
    (-31240260961 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-30159559173 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch070Lower hpThetaJensenCellsBatch070Upper
    hpThetaShiftOneBatch070Neg100WeightLower hpThetaShiftOneBatch070Neg100WeightUpper hpThetaJensenCellsBatch070_bounds hpThetaShiftOneBatch070Neg100_weight_bounds
  have hl : (-31240260961 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch070Lower j * hpThetaShiftOneBatch070Neg100WeightLower j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftOneBatch070Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftOneBatch070Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch070Lower j * hpThetaShiftOneBatch070Neg100WeightUpper j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftOneBatch070Neg100WeightUpper j) / 1600) ≤ (-30159559173 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftOneBatch070Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1400 : ℝ) / 1600 = 70 / 80 by norm_num,
    show ((1400 : ℝ) + 20) / 1600 = (70 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch070Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1805238496929 / 100000000000 : ℝ)
  | 1 => (-1819826975299 / 100000000000 : ℝ)
  | 2 => (-2293137691877 / 125000000000 : ℝ)
  | 3 => (-18492885254093 / 1000000000000 : ℝ)
  | 4 => (-466040646733 / 25000000000 : ℝ)
  | 5 => (-18791328360231 / 1000000000000 : ℝ)
  | 6 => (-18941997726863 / 1000000000000 : ℝ)
  | 7 => (-19093638989821 / 1000000000000 : ℝ)
  | 8 => (-19246257190339 / 1000000000000 : ℝ)
  | 9 => (-4849964347587 / 250000000000 : ℝ)
  | 10 => (-9777222336271 / 500000000000 : ℝ)
  | 11 => (-9855012070219 / 500000000000 : ℝ)
  | 12 => (-397332018369 / 20000000000 : ℝ)
  | 13 => (-2503022518993 / 125000000000 : ℝ)
  | 14 => (-1261422937957 / 62500000000 : ℝ)
  | 15 => (-5085591668009 / 250000000000 : ℝ)
  | 16 => (-20502984354751 / 1000000000000 : ℝ)
  | 17 => (-10332312642657 / 500000000000 : ℝ)
  | 18 => (-5206823678717 / 250000000000 : ℝ)
  | 19 => (-2623874739489 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch070Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-35814884531 / 2000000000 : ℝ)
  | 1 => (-18052384969289 / 1000000000000 : ℝ)
  | 2 => (-18198269752989 / 1000000000000 : ℝ)
  | 3 => (-3669020307003 / 200000000000 : ℝ)
  | 4 => (-4623221313523 / 250000000000 : ℝ)
  | 5 => (-18641625869319 / 1000000000000 : ℝ)
  | 6 => (-1879132836023 / 100000000000 : ℝ)
  | 7 => (-9470998863431 / 500000000000 : ℝ)
  | 8 => (-954681949491 / 50000000000 : ℝ)
  | 9 => (-9623128595169 / 500000000000 : ℝ)
  | 10 => (-19399857390347 / 1000000000000 : ℝ)
  | 11 => (-19554444672541 / 1000000000000 : ℝ)
  | 12 => (-19710024140437 / 1000000000000 : ℝ)
  | 13 => (-19866600918449 / 1000000000000 : ℝ)
  | 14 => (-20024180151943 / 1000000000000 : ℝ)
  | 15 => (-20182767007311 / 1000000000000 : ℝ)
  | 16 => (-4068473334407 / 200000000000 : ℝ)
  | 17 => (-82011937419 / 4000000000 : ℝ)
  | 18 => (-20664625285313 / 1000000000000 : ℝ)
  | 19 => (-20827294714867 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch070Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1400 : ℝ) + (j.val : ℝ)) / 1600)
      (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch070Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch070Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1400 : ℝ) + (j.val : ℝ)) / 1600)
    (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch070Neg65WeightLower j.val) (hpThetaShiftOneBatch070Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch070Neg65WeightLower, hpThetaShiftOneBatch070Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch070Neg65_integral_bounds :
    (-1327824739 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-1024305941 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch070Lower hpThetaJensenCellsBatch070Upper
    hpThetaShiftOneBatch070Neg65WeightLower hpThetaShiftOneBatch070Neg65WeightUpper hpThetaJensenCellsBatch070_bounds hpThetaShiftOneBatch070Neg65_weight_bounds
  have hl : (-1327824739 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch070Lower j * hpThetaShiftOneBatch070Neg65WeightLower j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftOneBatch070Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftOneBatch070Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch070Lower j * hpThetaShiftOneBatch070Neg65WeightUpper j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftOneBatch070Neg65WeightUpper j) / 1600) ≤ (-1024305941 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftOneBatch070Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1400 : ℝ) / 1600 = 70 / 80 by norm_num,
    show ((1400 : ℝ) + 20) / 1600 = (70 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch070Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-631186178451 / 1000000000000 : ℝ)
  | 1 => (-645453328453 / 1000000000000 : ℝ)
  | 2 => (-131971389313 / 200000000000 : ℝ)
  | 3 => (-168599478019 / 250000000000 : ℝ)
  | 4 => (-689077108393 / 1000000000000 : ℝ)
  | 5 => (-35194771153 / 50000000000 : ℝ)
  | 6 => (-718853747769 / 1000000000000 : ℝ)
  | 7 => (-5871623827 / 8000000000 : ℝ)
  | 8 => (-749194014911 / 1000000000000 : ℝ)
  | 9 => (-382288880801 / 500000000000 : ℝ)
  | 10 => (-195026281719 / 250000000000 : ℝ)
  | 11 => (-795777023383 / 1000000000000 : ℝ)
  | 12 => (-101449296001 / 125000000000 : ℝ)
  | 13 => (-827558081883 / 1000000000000 : ℝ)
  | 14 => (-843669090403 / 1000000000000 : ℝ)
  | 15 => (-429964161621 / 500000000000 : ℝ)
  | 16 => (-219084178591 / 250000000000 : ℝ)
  | 17 => (-892895202041 / 1000000000000 : ℝ)
  | 18 => (-28425147777 / 31250000000 : ℝ)
  | 19 => (-926466241761 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch070Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-308527310689 / 500000000000 : ℝ)
  | 1 => (-12623723569 / 20000000000 : ℝ)
  | 2 => (-161363332113 / 250000000000 : ℝ)
  | 3 => (-164964236641 / 250000000000 : ℝ)
  | 4 => (-26975916483 / 40000000000 : ℝ)
  | 5 => (-86134638549 / 125000000000 : ℝ)
  | 6 => (-703895423059 / 1000000000000 : ℝ)
  | 7 => (-89856718471 / 125000000000 : ℝ)
  | 8 => (-366976489187 / 500000000000 : ℝ)
  | 9 => (-74919401491 / 100000000000 : ℝ)
  | 10 => (-764577761601 / 1000000000000 : ℝ)
  | 11 => (-1248168203 / 1600000000 : ℝ)
  | 12 => (-397888511691 / 500000000000 : ℝ)
  | 13 => (-811594368007 / 1000000000000 : ℝ)
  | 14 => (-413779040941 / 500000000000 : ℝ)
  | 15 => (-421834545201 / 500000000000 : ℝ)
  | 16 => (-859928323241 / 1000000000000 : ℝ)
  | 17 => (-876336714363 / 1000000000000 : ℝ)
  | 18 => (-22322380051 / 25000000000 : ℝ)
  | 19 => (-909604728863 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch070Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1400 : ℝ) + (j.val : ℝ)) / 1600)
      (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch070Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch070Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1400 : ℝ) + (j.val : ℝ)) / 1600)
    (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch070Neg40WeightLower j.val) (hpThetaShiftOneBatch070Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch070Neg40WeightLower, hpThetaShiftOneBatch070Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch070Neg40_integral_bounds :
    (-209385863 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-398840461 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch070Lower hpThetaJensenCellsBatch070Upper
    hpThetaShiftOneBatch070Neg40WeightLower hpThetaShiftOneBatch070Neg40WeightUpper hpThetaJensenCellsBatch070_bounds hpThetaShiftOneBatch070Neg40_weight_bounds
  have hl : (-209385863 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch070Lower j * hpThetaShiftOneBatch070Neg40WeightLower j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftOneBatch070Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftOneBatch070Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch070Lower j * hpThetaShiftOneBatch070Neg40WeightUpper j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftOneBatch070Neg40WeightUpper j) / 1600) ≤ (-398840461 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftOneBatch070Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1400 : ℝ) / 1600 = 70 / 80 by norm_num,
    show ((1400 : ℝ) + 20) / 1600 = (70 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch070Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (303624550501 / 1000000000000 : ℝ)
  | 1 => (305683774677 / 1000000000000 : ℝ)
  | 2 => (61549471777 / 200000000000 : ℝ)
  | 3 => (9681727279 / 31250000000 : ℝ)
  | 4 => (62377497259 / 200000000000 : ℝ)
  | 5 => (313963968157 / 1000000000000 : ℝ)
  | 6 => (63208937473 / 200000000000 : ℝ)
  | 7 => (6362592249 / 20000000000 : ℝ)
  | 8 => (320218711623 / 1000000000000 : ℝ)
  | 9 => (322311952767 / 1000000000000 : ℝ)
  | 10 => (64881860689 / 200000000000 : ℝ)
  | 11 => (326510730889 / 1000000000000 : ℝ)
  | 12 => (328616202007 / 1000000000000 : ℝ)
  | 13 => (165362841687 / 500000000000 : ℝ)
  | 14 => (166419570619 / 500000000000 : ℝ)
  | 15 => (334956541511 / 1000000000000 : ℝ)
  | 16 => (337077849773 / 1000000000000 : ℝ)
  | 17 => (339203031269 / 1000000000000 : ℝ)
  | 18 => (68266410181 / 200000000000 : ℝ)
  | 19 => (343464873251 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch070Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (152841887339 / 500000000000 : ℝ)
  | 1 => (153873679443 / 500000000000 : ℝ)
  | 2 => (309815272929 / 1000000000000 : ℝ)
  | 3 => (38985935787 / 125000000000 : ℝ)
  | 4 => (156981984079 / 500000000000 : ℝ)
  | 5 => (158022343683 / 500000000000 : ℝ)
  | 6 => (318129612451 / 1000000000000 : ℝ)
  | 7 => (40027338953 / 125000000000 : ℝ)
  | 8 => (2518062131 / 7812500000 : ℝ)
  | 9 => (162204651723 / 500000000000 : ℝ)
  | 10 => (32651073089 / 100000000000 : ℝ)
  | 11 => (41077025251 / 125000000000 : ℝ)
  | 12 => (2645805467 / 8000000000 : ℝ)
  | 13 => (332839141239 / 1000000000000 : ℝ)
  | 14 => (41869567689 / 125000000000 : ℝ)
  | 15 => (168538924887 / 500000000000 : ℝ)
  | 16 => (33920303127 / 100000000000 : ℝ)
  | 17 => (170666025453 / 500000000000 : ℝ)
  | 18 => (85866218313 / 250000000000 : ℝ)
  | 19 => (43200182817 / 125000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch070Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1400 : ℝ) + (j.val : ℝ)) / 1600)
      (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch070Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch070Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1400 : ℝ) + (j.val : ℝ)) / 1600)
    (((1400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch070Neg20WeightLower j.val) (hpThetaShiftOneBatch070Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch070Neg20WeightLower, hpThetaShiftOneBatch070Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch070Neg20_integral_bounds :
    (8573487 / 50000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (70 / 80 : ℝ) ((70 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (35512683 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch070Lower hpThetaJensenCellsBatch070Upper
    hpThetaShiftOneBatch070Neg20WeightLower hpThetaShiftOneBatch070Neg20WeightUpper hpThetaJensenCellsBatch070_bounds hpThetaShiftOneBatch070Neg20_weight_bounds
  have hl : (8573487 / 50000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch070Lower j * hpThetaShiftOneBatch070Neg20WeightLower j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftOneBatch070Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftOneBatch070Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch070Lower j * hpThetaShiftOneBatch070Neg20WeightUpper j)
        (hpThetaJensenCellsBatch070Upper j * hpThetaShiftOneBatch070Neg20WeightUpper j) / 1600) ≤ (35512683 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch070Lower, hpThetaJensenCellsBatch070Upper,
      hpThetaShiftOneBatch070Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1400 : ℝ) / 1600 = 70 / 80 by norm_num,
    show ((1400 : ℝ) + 20) / 1600 = (70 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch070Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch070Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch070Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch070Neg20_integral_bounds
end HodgeProofHP
