/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch072

/-! Exact signed weight and batch integral certificates, batch 72 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch072Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-140285200471627 / 1000000000000 : ℝ)
  | 1 => (-28241556929079 / 200000000000 : ℝ)
  | 2 => (-142135508423111 / 1000000000000 : ℝ)
  | 3 => (-143068395653333 / 1000000000000 : ℝ)
  | 4 => (-144006470274489 / 1000000000000 : ℝ)
  | 5 => (-18118719539393 / 125000000000 : ℝ)
  | 6 => (-145898277894263 / 1000000000000 : ℝ)
  | 7 => (-3671301480537 / 25000000000 : ℝ)
  | 8 => (-147811124597361 / 1000000000000 : ℝ)
  | 9 => (-148775498413673 / 1000000000000 : ℝ)
  | 10 => (-149745205153651 / 1000000000000 : ℝ)
  | 11 => (-150720269392263 / 1000000000000 : ℝ)
  | 12 => (-75850357898243 / 500000000000 : ℝ)
  | 13 => (-152686569125569 / 1000000000000 : ℝ)
  | 14 => (-76838927115651 / 500000000000 : ℝ)
  | 15 => (-154674596058293 / 1000000000000 : ℝ)
  | 16 => (-155676819644233 / 1000000000000 : ℝ)
  | 17 => (-15668455012017 / 100000000000 : ℝ)
  | 18 => (-7884890635539 / 50000000000 : ℝ)
  | 19 => (-1983957909183 / 12500000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch072Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-139367732142857 / 1000000000000 : ℝ)
  | 1 => (-70142600235813 / 500000000000 : ℝ)
  | 2 => (-70603892322697 / 500000000000 : ℝ)
  | 3 => (-14213550842311 / 100000000000 : ℝ)
  | 4 => (-35767098913333 / 250000000000 : ℝ)
  | 5 => (-18000808784311 / 125000000000 : ℝ)
  | 6 => (-144949756315143 / 1000000000000 : ℝ)
  | 7 => (-72949138947131 / 500000000000 : ℝ)
  | 8 => (-146852059221479 / 1000000000000 : ℝ)
  | 9 => (-1847639057467 / 12500000000 : ℝ)
  | 10 => (-18596937301709 / 125000000000 : ℝ)
  | 11 => (-2994904103073 / 20000000000 : ℝ)
  | 12 => (-75360134696131 / 500000000000 : ℝ)
  | 13 => (-30340143159297 / 200000000000 : ℝ)
  | 14 => (-2385727642587 / 15625000000 : ℝ)
  | 15 => (-153677854231301 / 1000000000000 : ℝ)
  | 16 => (-38668649014573 / 250000000000 : ℝ)
  | 17 => (-19459602455529 / 125000000000 : ℝ)
  | 18 => (-156684550120169 / 1000000000000 : ℝ)
  | 19 => (-157697812710779 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch072Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1440 : ℝ) + (j.val : ℝ)) / 1600)
      (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch072Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch072Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1440 : ℝ) + (j.val : ℝ)) / 1600)
    (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch072Neg100WeightLower j.val) (hpThetaShiftOneBatch072Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch072Neg100WeightLower, hpThetaShiftOneBatch072Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch072Neg100_integral_bounds :
    (-4482059681 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-1729248943 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch072Lower hpThetaJensenCellsBatch072Upper
    hpThetaShiftOneBatch072Neg100WeightLower hpThetaShiftOneBatch072Neg100WeightUpper hpThetaJensenCellsBatch072_bounds hpThetaShiftOneBatch072Neg100_weight_bounds
  have hl : (-4482059681 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch072Lower j * hpThetaShiftOneBatch072Neg100WeightLower j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftOneBatch072Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftOneBatch072Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch072Lower j * hpThetaShiftOneBatch072Neg100WeightUpper j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftOneBatch072Neg100WeightUpper j) / 1600) ≤ (-1729248943 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftOneBatch072Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1440 : ℝ) / 1600 = 72 / 80 by norm_num,
    show ((1440 : ℝ) + 20) / 1600 = (72 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch072Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-12338567207043 / 500000000000 : ℝ)
  | 1 => (-12432479299987 / 500000000000 : ℝ)
  | 2 => (-1252697193673 / 50000000000 : ℝ)
  | 3 => (-504881920797 / 20000000000 : ℝ)
  | 4 => (-6358855231879 / 250000000000 : ℝ)
  | 5 => (-12813962193981 / 500000000000 : ℝ)
  | 6 => (-3227701536987 / 125000000000 : ℝ)
  | 7 => (-13008245274651 / 500000000000 : ℝ)
  | 8 => (-3276570633689 / 125000000000 : ℝ)
  | 9 => (-26409841801271 / 1000000000000 : ℝ)
  | 10 => (-5321665342563 / 200000000000 : ℝ)
  | 11 => (-13404012897969 / 500000000000 : ℝ)
  | 12 => (-27008945066067 / 1000000000000 : ℝ)
  | 13 => (-2721109056233 / 100000000000 : ℝ)
  | 14 => (-6853617086907 / 250000000000 : ℝ)
  | 15 => (-3452385563589 / 125000000000 : ℝ)
  | 16 => (-27824945156249 / 1000000000000 : ℝ)
  | 17 => (-28032056424897 / 1000000000000 : ℝ)
  | 18 => (-14120212236689 / 500000000000 : ℝ)
  | 19 => (-7112513871137 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch072Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-12245232766741 / 500000000000 : ℝ)
  | 1 => (-4935426882817 / 200000000000 : ℝ)
  | 2 => (-24864958599973 / 1000000000000 : ℝ)
  | 3 => (-25053943873459 / 1000000000000 : ℝ)
  | 4 => (-25244096039849 / 1000000000000 : ℝ)
  | 5 => (-5087084185503 / 200000000000 : ℝ)
  | 6 => (-25627924387961 / 1000000000000 : ℝ)
  | 7 => (-5164322459179 / 200000000000 : ℝ)
  | 8 => (-26016490549301 / 1000000000000 : ℝ)
  | 9 => (-26212565069511 / 1000000000000 : ℝ)
  | 10 => (-2640984180127 / 100000000000 : ℝ)
  | 11 => (-13304163356407 / 500000000000 : ℝ)
  | 12 => (-26808025795937 / 1000000000000 : ℝ)
  | 13 => (-13504472533033 / 500000000000 : ℝ)
  | 14 => (-27211090562329 / 1000000000000 : ℝ)
  | 15 => (-27414468347627 / 1000000000000 : ℝ)
  | 16 => (-27619084508711 / 1000000000000 : ℝ)
  | 17 => (-3478118144531 / 125000000000 : ℝ)
  | 18 => (-438000881639 / 15625000000 : ℝ)
  | 19 => (-28240424473377 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch072Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1440 : ℝ) + (j.val : ℝ)) / 1600)
      (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch072Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch072Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1440 : ℝ) + (j.val : ℝ)) / 1600)
    (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch072Neg65WeightLower j.val) (hpThetaShiftOneBatch072Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch072Neg65WeightLower, hpThetaShiftOneBatch072Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch072Neg65_integral_bounds :
    (-6364829071 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-6133017777 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch072Lower hpThetaJensenCellsBatch072Upper
    hpThetaShiftOneBatch072Neg65WeightLower hpThetaShiftOneBatch072Neg65WeightUpper hpThetaJensenCellsBatch072_bounds hpThetaShiftOneBatch072Neg65_weight_bounds
  have hl : (-6364829071 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch072Lower j * hpThetaShiftOneBatch072Neg65WeightLower j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftOneBatch072Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftOneBatch072Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch072Lower j * hpThetaShiftOneBatch072Neg65WeightUpper j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftOneBatch072Neg65WeightUpper j) / 1600) ≤ (-6133017777 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftOneBatch072Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1440 : ℝ) / 1600 = 72 / 80 by norm_num,
    show ((1440 : ℝ) + 20) / 1600 = (72 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch072Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-263478130419 / 200000000000 : ℝ)
  | 1 => (-1337844392239 / 1000000000000 : ℝ)
  | 2 => (-1358473128311 / 1000000000000 : ℝ)
  | 3 => (-1379277915739 / 1000000000000 : ℝ)
  | 4 => (-700129907331 / 500000000000 : ℝ)
  | 5 => (-284283977989 / 200000000000 : ℝ)
  | 6 => (-1442759211193 / 1000000000000 : ℝ)
  | 7 => (-146427885277 / 100000000000 : ℝ)
  | 8 => (-1485979893809 / 1000000000000 : ℝ)
  | 9 => (-753931709117 / 500000000000 : ℝ)
  | 10 => (-152993051477 / 100000000000 : ℝ)
  | 11 => (-1552182276963 / 1000000000000 : ℝ)
  | 12 => (-196827475399 / 125000000000 : ℝ)
  | 13 => (-1597244196687 / 1000000000000 : ℝ)
  | 14 => (-810028282773 / 500000000000 : ℝ)
  | 15 => (-1643058022747 / 1000000000000 : ℝ)
  | 16 => (-1666249686167 / 1000000000000 : ℝ)
  | 17 => (-1689632678597 / 1000000000000 : ℝ)
  | 18 => (-1713208127757 / 1000000000000 : ℝ)
  | 19 => (-1736977166313 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch072Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-648555428571 / 500000000000 : ℝ)
  | 1 => (-658695326047 / 500000000000 : ℝ)
  | 2 => (-668922196119 / 500000000000 : ℝ)
  | 3 => (-135847312831 / 100000000000 : ℝ)
  | 4 => (-689638957869 / 500000000000 : ℝ)
  | 5 => (-1400259814661 / 1000000000000 : ℝ)
  | 6 => (-177677486243 / 125000000000 : ℝ)
  | 7 => (-180344901399 / 125000000000 : ℝ)
  | 8 => (-1464278852769 / 1000000000000 : ℝ)
  | 9 => (-92873743363 / 62500000000 : ℝ)
  | 10 => (-1507863418233 / 1000000000000 : ℝ)
  | 11 => (-1529930514769 / 1000000000000 : ℝ)
  | 12 => (-776091138481 / 500000000000 : ℝ)
  | 13 => (-1574619803191 / 1000000000000 : ℝ)
  | 14 => (-798622098343 / 500000000000 : ℝ)
  | 15 => (-324011313109 / 200000000000 : ℝ)
  | 16 => (-821529011373 / 500000000000 : ℝ)
  | 17 => (-833124843083 / 500000000000 : ℝ)
  | 18 => (-422408169649 / 250000000000 : ℝ)
  | 19 => (-428302031939 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch072Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1440 : ℝ) + (j.val : ℝ)) / 1600)
      (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch072Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch072Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1440 : ℝ) + (j.val : ℝ)) / 1600)
    (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch072Neg40WeightLower j.val) (hpThetaShiftOneBatch072Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch072Neg40WeightLower, hpThetaShiftOneBatch072Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch072Neg40_integral_bounds :
    (-90834863 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-86904827 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch072Lower hpThetaJensenCellsBatch072Upper
    hpThetaShiftOneBatch072Neg40WeightLower hpThetaShiftOneBatch072Neg40WeightUpper hpThetaJensenCellsBatch072_bounds hpThetaShiftOneBatch072Neg40_weight_bounds
  have hl : (-90834863 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch072Lower j * hpThetaShiftOneBatch072Neg40WeightLower j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftOneBatch072Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftOneBatch072Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch072Lower j * hpThetaShiftOneBatch072Neg40WeightUpper j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftOneBatch072Neg40WeightUpper j) / 1600) ≤ (-86904827 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftOneBatch072Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1440 : ℝ) / 1600 = 72 / 80 by norm_num,
    show ((1440 : ℝ) + 20) / 1600 = (72 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch072Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (389066142857 / 1000000000000 : ℝ)
  | 1 => (97818239109 / 250000000000 : ℝ)
  | 2 => (3147861287 / 8000000000 : ℝ)
  | 3 => (98923803039 / 250000000000 : ℝ)
  | 4 => (198955282943 / 500000000000 : ℝ)
  | 5 => (100032169323 / 250000000000 : ℝ)
  | 6 => (20117475061 / 50000000000 : ℝ)
  | 7 => (202286496067 / 500000000000 : ℝ)
  | 8 => (406799104113 / 1000000000000 : ℝ)
  | 9 => (409027790851 / 1000000000000 : ℝ)
  | 10 => (51407375707 / 125000000000 : ℝ)
  | 11 => (206746350723 / 500000000000 : ℝ)
  | 12 => (415728830747 / 1000000000000 : ℝ)
  | 13 => (13061479553 / 31250000000 : ℝ)
  | 14 => (210104099017 / 500000000000 : ℝ)
  | 15 => (211225669553 / 500000000000 : ℝ)
  | 16 => (424696719861 / 1000000000000 : ℝ)
  | 17 => (8538885817 / 20000000000 : ℝ)
  | 18 => (429194002221 / 1000000000000 : ℝ)
  | 19 => (215722901861 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch072Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (391272956437 / 1000000000000 : ℝ)
  | 1 => (98370665219 / 250000000000 : ℝ)
  | 2 => (395695212157 / 1000000000000 : ℝ)
  | 3 => (397910565887 / 1000000000000 : ℝ)
  | 4 => (400128677293 / 1000000000000 : ℝ)
  | 5 => (402349501221 / 1000000000000 : ℝ)
  | 6 => (80914598427 / 200000000000 : ℝ)
  | 7 => (203399552057 / 500000000000 : ℝ)
  | 8 => (102256947713 / 250000000000 : ℝ)
  | 9 => (411259005657 / 1000000000000 : ℝ)
  | 10 => (413492701447 / 1000000000000 : ℝ)
  | 11 => (103932207687 / 250000000000 : ℝ)
  | 12 => (417967345697 / 1000000000000 : ℝ)
  | 13 => (84041639607 / 200000000000 : ℝ)
  | 14 => (422451339107 / 1000000000000 : ℝ)
  | 15 => (212348359931 / 500000000000 : ℝ)
  | 16 => (426944290851 / 1000000000000 : ℝ)
  | 17 => (214597001111 / 500000000000 : ℝ)
  | 18 => (431445803723 / 1000000000000 : ℝ)
  | 19 => (433699644697 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch072Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1440 : ℝ) + (j.val : ℝ)) / 1600)
      (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch072Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch072Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1440 : ℝ) + (j.val : ℝ)) / 1600)
    (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch072Neg20WeightLower j.val) (hpThetaShiftOneBatch072Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch072Neg20WeightLower, hpThetaShiftOneBatch072Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch072Neg20_integral_bounds :
    (95677977 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (24772559 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch072Lower hpThetaJensenCellsBatch072Upper
    hpThetaShiftOneBatch072Neg20WeightLower hpThetaShiftOneBatch072Neg20WeightUpper hpThetaJensenCellsBatch072_bounds hpThetaShiftOneBatch072Neg20_weight_bounds
  have hl : (95677977 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch072Lower j * hpThetaShiftOneBatch072Neg20WeightLower j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftOneBatch072Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftOneBatch072Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch072Lower j * hpThetaShiftOneBatch072Neg20WeightUpper j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftOneBatch072Neg20WeightUpper j) / 1600) ≤ (24772559 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftOneBatch072Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1440 : ℝ) / 1600 = 72 / 80 by norm_num,
    show ((1440 : ℝ) + 20) / 1600 = (72 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch072Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch072Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch072Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch072Neg20_integral_bounds
end HodgeProofHP
