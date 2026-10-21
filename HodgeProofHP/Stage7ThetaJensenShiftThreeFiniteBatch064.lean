/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch064

/-! Exact signed weight and batch integral certificates, batch 64 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch064Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4972351723 / 200000000000 : ℝ)
  | 1 => (-6295040937 / 250000000000 : ℝ)
  | 2 => (-25502090299 / 1000000000000 : ℝ)
  | 3 => (-5165514417 / 200000000000 : ℝ)
  | 4 => (-26156643201 / 1000000000000 : ℝ)
  | 5 => (-26489338029 / 1000000000000 : ℝ)
  | 6 => (-838302851 / 31250000000 : ℝ)
  | 7 => (-13582868883 / 500000000000 : ℝ)
  | 8 => (-3438689109 / 125000000000 : ℝ)
  | 9 => (-27857052087 / 1000000000000 : ℝ)
  | 10 => (-28208391239 / 1000000000000 : ℝ)
  | 11 => (-7140891613 / 250000000000 : ℝ)
  | 12 => (-28922614151 / 1000000000000 : ℝ)
  | 13 => (-29285571057 / 1000000000000 : ℝ)
  | 14 => (-14826237099 / 500000000000 : ℝ)
  | 15 => (-15011680451 / 500000000000 : ℝ)
  | 16 => (-15199134403 / 500000000000 : ℝ)
  | 17 => (-30777235857 / 1000000000000 : ℝ)
  | 18 => (-31160300311 / 1000000000000 : ℝ)
  | 19 => (-31547500737 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch064Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-12273420683 / 500000000000 : ℝ)
  | 1 => (-12430879307 / 500000000000 : ℝ)
  | 2 => (-25180163747 / 1000000000000 : ℝ)
  | 3 => (-12751045149 / 500000000000 : ℝ)
  | 4 => (-6456893021 / 250000000000 : ℝ)
  | 5 => (-8173951 / 312500000 : ℝ)
  | 6 => (-6622334507 / 250000000000 : ℝ)
  | 7 => (-26825691231 / 1000000000000 : ℝ)
  | 8 => (-5433147553 / 200000000000 : ℝ)
  | 9 => (-27509512871 / 1000000000000 : ℝ)
  | 10 => (-13928526043 / 500000000000 : ℝ)
  | 11 => (-14104195619 / 500000000000 : ℝ)
  | 12 => (-28563566451 / 1000000000000 : ℝ)
  | 13 => (-578452283 / 20000000000 : ℝ)
  | 14 => (-1830348191 / 62500000000 : ℝ)
  | 15 => (-29652474197 / 1000000000000 : ℝ)
  | 16 => (-30023360901 / 1000000000000 : ℝ)
  | 17 => (-6079653761 / 200000000000 : ℝ)
  | 18 => (-1923577241 / 62500000000 : ℝ)
  | 19 => (-3116030031 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch064Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1280 : ℝ) + (j.val : ℝ)) / 1600)
      (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch064Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch064Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1280 : ℝ) + (j.val : ℝ)) / 1600)
    (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch064Neg100WeightLower j.val) (hpThetaShiftThreeBatch064Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch064Neg100WeightLower, hpThetaShiftThreeBatch064Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch064Neg100_integral_bounds :
    (-68581627 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-33018127 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch064Lower hpThetaJensenCellsBatch064Upper
    hpThetaShiftThreeBatch064Neg100WeightLower hpThetaShiftThreeBatch064Neg100WeightUpper hpThetaJensenCellsBatch064_bounds hpThetaShiftThreeBatch064Neg100_weight_bounds
  have hl : (-68581627 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch064Lower j * hpThetaShiftThreeBatch064Neg100WeightLower j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftThreeBatch064Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftThreeBatch064Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch064Lower j * hpThetaShiftThreeBatch064Neg100WeightUpper j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftThreeBatch064Neg100WeightUpper j) / 1600) ≤ (-33018127 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftThreeBatch064Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1280 : ℝ) / 1600 = 64 / 80 by norm_num,
    show ((1280 : ℝ) + 20) / 1600 = (64 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch064Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-64581537 / 31250000000 : ℝ)
  | 1 => (-2112821627 / 1000000000000 : ℝ)
  | 2 => (-539928377 / 250000000000 : ℝ)
  | 3 => (-2207292623 / 1000000000000 : ℝ)
  | 4 => (-2255566841 / 1000000000000 : ℝ)
  | 5 => (-576136027 / 250000000000 : ℝ)
  | 6 => (-58855811 / 25000000000 : ℝ)
  | 7 => (-240463993 / 100000000000 : ℝ)
  | 8 => (-613943687 / 250000000000 : ℝ)
  | 9 => (-2507645139 / 1000000000000 : ℝ)
  | 10 => (-80008107 / 31250000000 : ℝ)
  | 11 => (-2613626003 / 1000000000000 : ℝ)
  | 12 => (-2667753353 / 1000000000000 : ℝ)
  | 13 => (-2722650031 / 1000000000000 : ℝ)
  | 14 => (-277832467 / 100000000000 : ℝ)
  | 15 => (-2834785987 / 1000000000000 : ℝ)
  | 16 => (-2892042777 / 1000000000000 : ℝ)
  | 17 => (-737525979 / 250000000000 : ℝ)
  | 18 => (-3008978363 / 1000000000000 : ℝ)
  | 19 => (-3068675159 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch064Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-404213691 / 200000000000 : ℝ)
  | 1 => (-2066609183 / 1000000000000 : ℝ)
  | 2 => (-1056410813 / 500000000000 : ℝ)
  | 3 => (-2159713507 / 1000000000000 : ℝ)
  | 4 => (-1103646311 / 500000000000 : ℝ)
  | 5 => (-56389171 / 25000000000 : ℝ)
  | 6 => (-2304544107 / 1000000000000 : ℝ)
  | 7 => (-2354232439 / 1000000000000 : ℝ)
  | 8 => (-2404639929 / 1000000000000 : ℝ)
  | 9 => (-2455774747 / 1000000000000 : ℝ)
  | 10 => (-1253822569 / 500000000000 : ℝ)
  | 11 => (-2560259423 / 1000000000000 : ℝ)
  | 12 => (-1306813001 / 500000000000 : ℝ)
  | 13 => (-333469169 / 125000000000 : ℝ)
  | 14 => (-272265003 / 100000000000 : ℝ)
  | 15 => (-2778324669 / 1000000000000 : ℝ)
  | 16 => (-1417392993 / 500000000000 : ℝ)
  | 17 => (-361505347 / 125000000000 : ℝ)
  | 18 => (-590020783 / 200000000000 : ℝ)
  | 19 => (-1504489181 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch064Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1280 : ℝ) + (j.val : ℝ)) / 1600)
      (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch064Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch064Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1280 : ℝ) + (j.val : ℝ)) / 1600)
    (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch064Neg70WeightLower j.val) (hpThetaShiftThreeBatch064Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch064Neg70WeightLower, hpThetaShiftThreeBatch064Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch064Neg70_integral_bounds :
    (-12374291 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-11816299 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch064Lower hpThetaJensenCellsBatch064Upper
    hpThetaShiftThreeBatch064Neg70WeightLower hpThetaShiftThreeBatch064Neg70WeightUpper hpThetaJensenCellsBatch064_bounds hpThetaShiftThreeBatch064Neg70_weight_bounds
  have hl : (-12374291 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch064Lower j * hpThetaShiftThreeBatch064Neg70WeightLower j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftThreeBatch064Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftThreeBatch064Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch064Lower j * hpThetaShiftThreeBatch064Neg70WeightUpper j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftThreeBatch064Neg70WeightUpper j) / 1600) ≤ (-11816299 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftThreeBatch064Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1280 : ℝ) / 1600 = 64 / 80 by norm_num,
    show ((1280 : ℝ) + 20) / 1600 = (64 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch064Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (215219089 / 250000000000 : ℝ)
  | 1 => (867135921 / 1000000000000 : ℝ)
  | 2 => (109175087 / 125000000000 : ℝ)
  | 3 => (27489691 / 31250000000 : ℝ)
  | 4 => (885943593 / 1000000000000 : ℝ)
  | 5 => (111527569 / 125000000000 : ℝ)
  | 6 => (898500391 / 1000000000000 : ℝ)
  | 7 => (180956501 / 200000000000 : ℝ)
  | 8 => (227766569 / 250000000000 : ℝ)
  | 9 => (917351079 / 1000000000000 : ℝ)
  | 10 => (923636277 / 1000000000000 : ℝ)
  | 11 => (929921223 / 1000000000000 : ℝ)
  | 12 => (46810263 / 50000000000 : ℝ)
  | 13 => (942487721 / 1000000000000 : ℝ)
  | 14 => (118595991 / 125000000000 : ℝ)
  | 15 => (119380649 / 125000000000 : ℝ)
  | 16 => (192263763 / 200000000000 : ℝ)
  | 17 => (193517617 / 200000000000 : ℝ)
  | 18 => (486926141 / 500000000000 : ℝ)
  | 19 => (39204427 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch064Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (433567961 / 500000000000 : ℝ)
  | 1 => (873400697 / 1000000000000 : ℝ)
  | 2 => (879670113 / 1000000000000 : ℝ)
  | 3 => (442971797 / 500000000000 : ℝ)
  | 4 => (892220553 / 1000000000000 : ℝ)
  | 5 => (112312549 / 125000000000 : ℝ)
  | 6 => (452391253 / 500000000000 : ℝ)
  | 7 => (911066277 / 1000000000000 : ℝ)
  | 8 => (22933777 / 25000000000 : ℝ)
  | 9 => (461818139 / 500000000000 : ℝ)
  | 10 => (116240153 / 125000000000 : ℝ)
  | 11 => (936205261 / 1000000000000 : ℝ)
  | 12 => (471243861 / 500000000000 : ℝ)
  | 13 => (948767929 / 1000000000000 : ℝ)
  | 14 => (955045193 / 1000000000000 : ℝ)
  | 15 => (30041213 / 31250000000 : ℝ)
  | 16 => (483794043 / 500000000000 : ℝ)
  | 17 => (973852283 / 1000000000000 : ℝ)
  | 18 => (245027669 / 250000000000 : ℝ)
  | 19 => (24659063 / 25000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch064Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1280 : ℝ) + (j.val : ℝ)) / 1600)
      (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch064Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch064Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1280 : ℝ) + (j.val : ℝ)) / 1600)
    (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch064Neg45WeightLower j.val) (hpThetaShiftThreeBatch064Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch064Neg45WeightLower, hpThetaShiftThreeBatch064Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch064Neg45_integral_bounds :
    (2197823 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (141843 / 31250000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch064Lower hpThetaJensenCellsBatch064Upper
    hpThetaShiftThreeBatch064Neg45WeightLower hpThetaShiftThreeBatch064Neg45WeightUpper hpThetaJensenCellsBatch064_bounds hpThetaShiftThreeBatch064Neg45_weight_bounds
  have hl : (2197823 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch064Lower j * hpThetaShiftThreeBatch064Neg45WeightLower j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftThreeBatch064Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftThreeBatch064Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch064Lower j * hpThetaShiftThreeBatch064Neg45WeightUpper j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftThreeBatch064Neg45WeightUpper j) / 1600) ≤ (141843 / 31250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftThreeBatch064Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1280 : ℝ) / 1600 = 64 / 80 by norm_num,
    show ((1280 : ℝ) + 20) / 1600 = (64 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch064Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-52327927 / 200000000000 : ℝ)
  | 1 => (-130659729 / 500000000000 : ℝ)
  | 2 => (-260979403 / 1000000000000 : ℝ)
  | 3 => (-130309637 / 500000000000 : ℝ)
  | 4 => (-130119437 / 500000000000 : ℝ)
  | 5 => (-64959501 / 250000000000 : ℝ)
  | 6 => (-51883293 / 200000000000 : ℝ)
  | 7 => (-258974057 / 1000000000000 : ℝ)
  | 8 => (-258510579 / 1000000000000 : ℝ)
  | 9 => (-258025829 / 1000000000000 : ℝ)
  | 10 => (-257519603 / 1000000000000 : ℝ)
  | 11 => (-256991699 / 1000000000000 : ℝ)
  | 12 => (-25644191 / 100000000000 : ℝ)
  | 13 => (-15991877 / 62500000000 : ℝ)
  | 14 => (-255275857 / 1000000000000 : ℝ)
  | 15 => (-254659177 / 1000000000000 : ℝ)
  | 16 => (-31752473 / 125000000000 : ℝ)
  | 17 => (-253357469 / 1000000000000 : ℝ)
  | 18 => (-252672019 / 1000000000000 : ℝ)
  | 19 => (-31495403 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch064Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-261319457 / 1000000000000 : ℝ)
  | 1 => (-130489701 / 500000000000 : ℝ)
  | 2 => (-260619273 / 1000000000000 : ℝ)
  | 3 => (-260238873 / 1000000000000 : ℝ)
  | 4 => (-259838003 / 1000000000000 : ℝ)
  | 5 => (-16213529 / 62500000000 : ℝ)
  | 6 => (-32371757 / 125000000000 : ℝ)
  | 7 => (-129255289 / 500000000000 : ℝ)
  | 8 => (-64506457 / 250000000000 : ℝ)
  | 9 => (-128759801 / 500000000000 : ℝ)
  | 10 => (-128495849 / 500000000000 : ℝ)
  | 11 => (-256441909 / 1000000000000 : ℝ)
  | 12 => (-255870031 / 1000000000000 : ℝ)
  | 13 => (-15954741 / 62500000000 : ℝ)
  | 14 => (-31832397 / 125000000000 : ℝ)
  | 15 => (-254019783 / 1000000000000 : ℝ)
  | 16 => (-63339367 / 250000000000 : ℝ)
  | 17 => (-126336009 / 500000000000 : ℝ)
  | 18 => (-251963223 / 1000000000000 : ℝ)
  | 19 => (-251230871 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch064Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1280 : ℝ) + (j.val : ℝ)) / 1600)
      (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch064Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch064Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1280 : ℝ) + (j.val : ℝ)) / 1600)
    (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch064Neg25WeightLower j.val) (hpThetaShiftThreeBatch064Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch064Neg25WeightLower, hpThetaShiftThreeBatch064Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch064Neg25_integral_bounds :
    (-1266877 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-1232837 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch064Lower hpThetaJensenCellsBatch064Upper
    hpThetaShiftThreeBatch064Neg25WeightLower hpThetaShiftThreeBatch064Neg25WeightUpper hpThetaJensenCellsBatch064_bounds hpThetaShiftThreeBatch064Neg25_weight_bounds
  have hl : (-1266877 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch064Lower j * hpThetaShiftThreeBatch064Neg25WeightLower j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftThreeBatch064Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftThreeBatch064Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch064Lower j * hpThetaShiftThreeBatch064Neg25WeightUpper j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftThreeBatch064Neg25WeightUpper j) / 1600) ≤ (-1232837 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftThreeBatch064Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1280 : ℝ) / 1600 = 64 / 80 by norm_num,
    show ((1280 : ℝ) + 20) / 1600 = (64 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch064Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch064Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch064Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch064Neg25_integral_bounds
end HodgeProofHP
