/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch021

/-! Exact signed weight and batch integral certificates, batch 21 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch021Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-7963720087 / 500000000000 : ℝ)
  | 1 => (-3195603073 / 200000000000 : ℝ)
  | 2 => (-16026557959 / 1000000000000 : ℝ)
  | 3 => (-16073034469 / 1000000000000 : ℝ)
  | 4 => (-3223482257 / 200000000000 : ℝ)
  | 5 => (-16159654677 / 1000000000000 : ℝ)
  | 6 => (-3239946159 / 200000000000 : ℝ)
  | 7 => (-4059401419 / 250000000000 : ℝ)
  | 8 => (-3254649049 / 200000000000 : ℝ)
  | 9 => (-3261323063 / 200000000000 : ℝ)
  | 10 => (-8168840797 / 500000000000 : ℝ)
  | 11 => (-4091602421 / 250000000000 : ℝ)
  | 12 => (-16392765087 / 1000000000000 : ℝ)
  | 13 => (-3283342641 / 200000000000 : ℝ)
  | 14 => (-3287643869 / 200000000000 : ℝ)
  | 15 => (-16457248721 / 1000000000000 : ℝ)
  | 16 => (-16473766457 / 1000000000000 : ℝ)
  | 17 => (-16487737591 / 1000000000000 : ℝ)
  | 18 => (-659965083 / 40000000000 : ℝ)
  | 19 => (-2063487473 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch021Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-15874865747 / 1000000000000 : ℝ)
  | 1 => (-15927440173 / 1000000000000 : ℝ)
  | 2 => (-3994503841 / 250000000000 : ℝ)
  | 3 => (-8013278979 / 500000000000 : ℝ)
  | 4 => (-4018258617 / 250000000000 : ℝ)
  | 5 => (-4029352821 / 250000000000 : ℝ)
  | 6 => (-4039913669 / 250000000000 : ℝ)
  | 7 => (-8099865397 / 500000000000 : ℝ)
  | 8 => (-649504227 / 40000000000 : ℝ)
  | 9 => (-4068311311 / 250000000000 : ℝ)
  | 10 => (-8153307657 / 500000000000 : ℝ)
  | 11 => (-16337681593 / 1000000000000 : ℝ)
  | 12 => (-16366409683 / 1000000000000 : ℝ)
  | 13 => (-8196382543 / 500000000000 : ℝ)
  | 14 => (-4104178301 / 250000000000 : ℝ)
  | 15 => (-1027388709 / 62500000000 : ℝ)
  | 16 => (-205715609 / 12500000000 : ℝ)
  | 17 => (-2059220807 / 125000000000 : ℝ)
  | 18 => (-1648773759 / 100000000000 : ℝ)
  | 19 => (-8249563537 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch021Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((420 : ℝ) + (j.val : ℝ)) / 1600)
      (((420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch021Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch021Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((420 : ℝ) + (j.val : ℝ)) / 1600)
    (((420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch021Neg100WeightLower j.val) (hpThetaShiftOneBatch021Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch021Neg100WeightLower, hpThetaShiftOneBatch021Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch021Neg100_integral_bounds :
    (-22592954493 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-35624342301 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch021Lower hpThetaJensenCellsBatch021Upper
    hpThetaShiftOneBatch021Neg100WeightLower hpThetaShiftOneBatch021Neg100WeightUpper hpThetaJensenCellsBatch021_bounds hpThetaShiftOneBatch021Neg100_weight_bounds
  have hl : (-22592954493 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch021Lower j * hpThetaShiftOneBatch021Neg100WeightLower j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftOneBatch021Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftOneBatch021Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch021Lower j * hpThetaShiftOneBatch021Neg100WeightUpper j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftOneBatch021Neg100WeightUpper j) / 1600) ≤ (-35624342301 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftOneBatch021Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (420 : ℝ) / 1600 = 21 / 80 by norm_num,
    show ((420 : ℝ) + 20) / 1600 = (21 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch021Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-11978096171 / 1000000000000 : ℝ)
  | 1 => (-12125579921 / 1000000000000 : ℝ)
  | 2 => (-490927429 / 40000000000 : ℝ)
  | 3 => (-2484179793 / 200000000000 : ℝ)
  | 4 => (-12568704879 / 1000000000000 : ℝ)
  | 5 => (-12716588567 / 1000000000000 : ℝ)
  | 6 => (-2572906997 / 200000000000 : ℝ)
  | 7 => (-260250579 / 20000000000 : ℝ)
  | 8 => (-102816837 / 7812500000 : ℝ)
  | 9 => (-3327149519 / 250000000000 : ℝ)
  | 10 => (-3364160541 / 250000000000 : ℝ)
  | 11 => (-13604671651 / 1000000000000 : ℝ)
  | 12 => (-13752670647 / 1000000000000 : ℝ)
  | 13 => (-3475155781 / 250000000000 : ℝ)
  | 14 => (-14048512909 / 1000000000000 : ℝ)
  | 15 => (-14196323693 / 1000000000000 : ℝ)
  | 16 => (-7172019511 / 500000000000 : ℝ)
  | 17 => (-14491642307 / 1000000000000 : ℝ)
  | 18 => (-14639116813 / 1000000000000 : ℝ)
  | 19 => (-1478644567 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch021Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1478843619 / 125000000000 : ℝ)
  | 1 => (-1197809617 / 100000000000 : ℝ)
  | 2 => (-151569749 / 12500000000 : ℝ)
  | 3 => (-3068296431 / 250000000000 : ℝ)
  | 4 => (-3105224741 / 250000000000 : ℝ)
  | 5 => (-6284352439 / 500000000000 : ℝ)
  | 6 => (-6358294283 / 500000000000 : ℝ)
  | 7 => (-1608066873 / 125000000000 : ℝ)
  | 8 => (-13012528949 / 1000000000000 : ℝ)
  | 9 => (-2632111027 / 200000000000 : ℝ)
  | 10 => (-532343923 / 40000000000 : ℝ)
  | 11 => (-13456642163 / 1000000000000 : ℝ)
  | 12 => (-272093433 / 20000000000 : ℝ)
  | 13 => (-6876335323 / 500000000000 : ℝ)
  | 14 => (-13900623123 / 1000000000000 : ℝ)
  | 15 => (-3512128227 / 250000000000 : ℝ)
  | 16 => (-3549080923 / 250000000000 : ℝ)
  | 17 => (-14344039021 / 1000000000000 : ℝ)
  | 18 => (-7245821153 / 500000000000 : ℝ)
  | 19 => (-3659779203 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch021Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((420 : ℝ) + (j.val : ℝ)) / 1600)
      (((420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch021Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch021Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((420 : ℝ) + (j.val : ℝ)) / 1600)
    (((420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch021Neg65WeightLower j.val) (hpThetaShiftOneBatch021Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch021Neg65WeightLower, hpThetaShiftOneBatch021Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch021Neg65_integral_bounds :
    (-148385068671 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-72449678593 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch021Lower hpThetaJensenCellsBatch021Upper
    hpThetaShiftOneBatch021Neg65WeightLower hpThetaShiftOneBatch021Neg65WeightUpper hpThetaJensenCellsBatch021_bounds hpThetaShiftOneBatch021Neg65_weight_bounds
  have hl : (-148385068671 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch021Lower j * hpThetaShiftOneBatch021Neg65WeightLower j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftOneBatch021Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftOneBatch021Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch021Lower j * hpThetaShiftOneBatch021Neg65WeightUpper j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftOneBatch021Neg65WeightUpper j) / 1600) ≤ (-72449678593 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftOneBatch021Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (420 : ℝ) / 1600 = 21 / 80 by norm_num,
    show ((420 : ℝ) + 20) / 1600 = (21 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch021Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-917523237 / 1000000000000 : ℝ)
  | 1 => (-32387141 / 31250000000 : ℝ)
  | 2 => (-1156136141 / 1000000000000 : ℝ)
  | 3 => (-1276764033 / 1000000000000 : ℝ)
  | 4 => (-55930801 / 40000000000 : ℝ)
  | 5 => (-760325943 / 500000000000 : ℝ)
  | 6 => (-1643907313 / 1000000000000 : ℝ)
  | 7 => (-110502121 / 62500000000 : ℝ)
  | 8 => (-1893029313 / 1000000000000 : ℝ)
  | 9 => (-2018890931 / 1000000000000 : ℝ)
  | 10 => (-1072808103 / 500000000000 : ℝ)
  | 11 => (-568300621 / 250000000000 : ℝ)
  | 12 => (-7505147 / 3125000000 : ℝ)
  | 13 => (-101237883 / 40000000000 : ℝ)
  | 14 => (-2661099721 / 1000000000000 : ℝ)
  | 15 => (-558420407 / 200000000000 : ℝ)
  | 16 => (-2923951003 / 1000000000000 : ℝ)
  | 17 => (-3056643539 / 1000000000000 : ℝ)
  | 18 => (-3190176483 / 1000000000000 : ℝ)
  | 19 => (-1662273301 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch021Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-799542341 / 1000000000000 : ℝ)
  | 1 => (-229380809 / 250000000000 : ℝ)
  | 2 => (-1036388511 / 1000000000000 : ℝ)
  | 3 => (-57806807 / 50000000000 : ℝ)
  | 4 => (-9974719 / 7812500000 : ℝ)
  | 5 => (-174783753 / 125000000000 : ℝ)
  | 6 => (-304130377 / 200000000000 : ℝ)
  | 7 => (-102744207 / 62500000000 : ℝ)
  | 8 => (-353606787 / 200000000000 : ℝ)
  | 9 => (-29578583 / 15625000000 : ℝ)
  | 10 => (-201889093 / 100000000000 : ℝ)
  | 11 => (-429123241 / 200000000000 : ℝ)
  | 12 => (-2273202483 / 1000000000000 : ℝ)
  | 13 => (-2401647039 / 1000000000000 : ℝ)
  | 14 => (-1265473537 / 500000000000 : ℝ)
  | 15 => (-66527493 / 25000000000 : ℝ)
  | 16 => (-1396051017 / 500000000000 : ℝ)
  | 17 => (-1461975501 / 500000000000 : ℝ)
  | 18 => (-1528321769 / 500000000000 : ℝ)
  | 19 => (-1595088241 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch021Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((420 : ℝ) + (j.val : ℝ)) / 1600)
      (((420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch021Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch021Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((420 : ℝ) + (j.val : ℝ)) / 1600)
    (((420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch021Neg40WeightLower j.val) (hpThetaShiftOneBatch021Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch021Neg40WeightLower, hpThetaShiftOneBatch021Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch021Neg40_integral_bounds :
    (-23114964139 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-2144112909 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch021Lower hpThetaJensenCellsBatch021Upper
    hpThetaShiftOneBatch021Neg40WeightLower hpThetaShiftOneBatch021Neg40WeightUpper hpThetaJensenCellsBatch021_bounds hpThetaShiftOneBatch021Neg40_weight_bounds
  have hl : (-23114964139 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch021Lower j * hpThetaShiftOneBatch021Neg40WeightLower j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftOneBatch021Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftOneBatch021Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch021Lower j * hpThetaShiftOneBatch021Neg40WeightUpper j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftOneBatch021Neg40WeightUpper j) / 1600) ≤ (-2144112909 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftOneBatch021Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (420 : ℝ) / 1600 = 21 / 80 by norm_num,
    show ((420 : ℝ) + 20) / 1600 = (21 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch021Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (346485989 / 25000000000 : ℝ)
  | 1 => (6920520517 / 500000000000 : ℝ)
  | 2 => (55287739 / 4000000000 : ℝ)
  | 3 => (2760423573 / 200000000000 : ℝ)
  | 4 => (3445396887 / 250000000000 : ℝ)
  | 5 => (6880170493 / 500000000000 : ℝ)
  | 6 => (13738375377 / 1000000000000 : ℝ)
  | 7 => (2743137587 / 200000000000 : ℝ)
  | 8 => (13692275889 / 1000000000000 : ℝ)
  | 9 => (13668136483 / 1000000000000 : ℝ)
  | 10 => (13643266973 / 1000000000000 : ℝ)
  | 11 => (6808832317 / 500000000000 : ℝ)
  | 12 => (6795663377 / 500000000000 : ℝ)
  | 13 => (2712850127 / 200000000000 : ℝ)
  | 14 => (6768216799 / 500000000000 : ℝ)
  | 15 => (844242061 / 62500000000 : ℝ)
  | 16 => (336964153 / 25000000000 : ℝ)
  | 17 => (6724255197 / 500000000000 : ℝ)
  | 18 => (6708851591 / 500000000000 : ℝ)
  | 19 => (13386141879 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch021Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2775426637 / 200000000000 : ℝ)
  | 1 => (13859439561 / 1000000000000 : ℝ)
  | 2 => (2768208207 / 200000000000 : ℝ)
  | 3 => (13821934751 / 1000000000000 : ℝ)
  | 4 => (6901058933 / 500000000000 : ℝ)
  | 5 => (13781587549 / 1000000000000 : ℝ)
  | 6 => (13760340987 / 1000000000000 : ℝ)
  | 7 => (6869187689 / 500000000000 : ℝ)
  | 8 => (26788453 / 1953125000 : ℝ)
  | 9 => (1369227589 / 100000000000 : ℝ)
  | 10 => (3417034121 / 250000000000 : ℝ)
  | 11 => (6821633487 / 500000000000 : ℝ)
  | 12 => (2723532927 / 200000000000 : ℝ)
  | 13 => (2718265351 / 200000000000 : ℝ)
  | 14 => (3391062659 / 250000000000 : ℝ)
  | 15 => (13536433599 / 1000000000000 : ℝ)
  | 16 => (13507872977 / 1000000000000 : ℝ)
  | 17 => (13478566121 / 1000000000000 : ℝ)
  | 18 => (2689702079 / 200000000000 : ℝ)
  | 19 => (13417703183 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch021Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((420 : ℝ) + (j.val : ℝ)) / 1600)
      (((420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch021Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch021Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((420 : ℝ) + (j.val : ℝ)) / 1600)
    (((420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch021Neg20WeightLower j.val) (hpThetaShiftOneBatch021Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch021Neg20WeightLower, hpThetaShiftOneBatch021Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch021Neg20_integral_bounds :
    (37399516181 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (21 / 80 : ℝ) ((21 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (151774035189 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch021Lower hpThetaJensenCellsBatch021Upper
    hpThetaShiftOneBatch021Neg20WeightLower hpThetaShiftOneBatch021Neg20WeightUpper hpThetaJensenCellsBatch021_bounds hpThetaShiftOneBatch021Neg20_weight_bounds
  have hl : (37399516181 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch021Lower j * hpThetaShiftOneBatch021Neg20WeightLower j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftOneBatch021Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftOneBatch021Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch021Lower j * hpThetaShiftOneBatch021Neg20WeightUpper j)
        (hpThetaJensenCellsBatch021Upper j * hpThetaShiftOneBatch021Neg20WeightUpper j) / 1600) ≤ (151774035189 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch021Lower, hpThetaJensenCellsBatch021Upper,
      hpThetaShiftOneBatch021Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (420 : ℝ) / 1600 = 21 / 80 by norm_num,
    show ((420 : ℝ) + 20) / 1600 = (21 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch021Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch021Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch021Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch021Neg20_integral_bounds
end HodgeProofHP
