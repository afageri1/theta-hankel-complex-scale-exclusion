/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch067

/-! Exact signed weight and batch integral certificates, batch 67 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch067Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-12876279081 / 250000000000 : ℝ)
  | 1 => (-52105351001 / 1000000000000 : ℝ)
  | 2 => (-6588963741 / 125000000000 : ℝ)
  | 3 => (-6665530981 / 125000000000 : ℝ)
  | 4 => (-5394301993 / 100000000000 : ℝ)
  | 5 => (-54568081771 / 1000000000000 : ℝ)
  | 6 => (-55199489403 / 1000000000000 : ℝ)
  | 7 => (-55837299293 / 1000000000000 : ℝ)
  | 8 => (-11296313669 / 200000000000 : ℝ)
  | 9 => (-14283088477 / 250000000000 : ℝ)
  | 10 => (-57789713773 / 1000000000000 : ℝ)
  | 11 => (-29226853089 / 500000000000 : ℝ)
  | 12 => (-59124389813 / 1000000000000 : ℝ)
  | 13 => (-59801823821 / 1000000000000 : ℝ)
  | 14 => (-30243033901 / 500000000000 : ℝ)
  | 15 => (-7647147727 / 125000000000 : ℝ)
  | 16 => (-61875226383 / 1000000000000 : ℝ)
  | 17 => (-15645065623 / 250000000000 : ℝ)
  | 18 => (-63292351599 / 1000000000000 : ℝ)
  | 19 => (-64011555633 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch067Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-50910951581 / 1000000000000 : ℝ)
  | 1 => (-51505116323 / 1000000000000 : ℝ)
  | 2 => (-52105351 / 1000000000 : ℝ)
  | 3 => (-52711709927 / 1000000000000 : ℝ)
  | 4 => (-53324247847 / 1000000000000 : ℝ)
  | 5 => (-53943019929 / 1000000000000 : ℝ)
  | 6 => (-5456808177 / 100000000000 : ℝ)
  | 7 => (-27599744701 / 500000000000 : ℝ)
  | 8 => (-13959324823 / 250000000000 : ℝ)
  | 9 => (-7060196043 / 125000000000 : ℝ)
  | 10 => (-57132353907 / 1000000000000 : ℝ)
  | 11 => (-14447428443 / 250000000000 : ℝ)
  | 12 => (-58453706177 / 1000000000000 : ℝ)
  | 13 => (-14781097453 / 250000000000 : ℝ)
  | 14 => (-2990091191 / 50000000000 : ℝ)
  | 15 => (-60486067801 / 1000000000000 : ℝ)
  | 16 => (-12235436363 / 200000000000 : ℝ)
  | 17 => (-30937613191 / 500000000000 : ℝ)
  | 18 => (-62580262491 / 1000000000000 : ℝ)
  | 19 => (-31646175799 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch067Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1340 : ℝ) + (j.val : ℝ)) / 1600)
      (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch067Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch067Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1340 : ℝ) + (j.val : ℝ)) / 1600)
    (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch067Neg100WeightLower j.val) (hpThetaShiftThreeBatch067Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch067Neg100WeightLower, hpThetaShiftThreeBatch067Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch067Neg100_integral_bounds :
    (-24608247 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-94739301 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch067Lower hpThetaJensenCellsBatch067Upper
    hpThetaShiftThreeBatch067Neg100WeightLower hpThetaShiftThreeBatch067Neg100WeightUpper hpThetaJensenCellsBatch067_bounds hpThetaShiftThreeBatch067Neg100_weight_bounds
  have hl : (-24608247 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch067Lower j * hpThetaShiftThreeBatch067Neg100WeightLower j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftThreeBatch067Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftThreeBatch067Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch067Lower j * hpThetaShiftThreeBatch067Neg100WeightUpper j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftThreeBatch067Neg100WeightUpper j) / 1600) ≤ (-94739301 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftThreeBatch067Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1340 : ℝ) / 1600 = 67 / 80 by norm_num,
    show ((1340 : ℝ) + 20) / 1600 = (67 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch067Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3173921283 / 500000000000 : ℝ)
  | 1 => (-6451431709 / 1000000000000 : ℝ)
  | 2 => (-3278159727 / 500000000000 : ℝ)
  | 3 => (-416407447 / 62500000000 : ℝ)
  | 4 => (-677004427 / 100000000000 : ℝ)
  | 5 => (-6878908389 / 1000000000000 : ℝ)
  | 6 => (-6989125207 / 1000000000000 : ℝ)
  | 7 => (-3550354271 / 500000000000 : ℝ)
  | 8 => (-7213672327 / 1000000000000 : ℝ)
  | 9 => (-3664015309 / 500000000000 : ℝ)
  | 10 => (-1860949397 / 250000000000 : ℝ)
  | 11 => (-7560987533 / 1000000000000 : ℝ)
  | 12 => (-7679614871 / 1000000000000 : ℝ)
  | 13 => (-3899847071 / 500000000000 : ℝ)
  | 14 => (-792124001 / 100000000000 : ℝ)
  | 15 => (-31422919 / 3906250000 : ℝ)
  | 16 => (-4084395409 / 500000000000 : ℝ)
  | 17 => (-518426607 / 62500000000 : ℝ)
  | 18 => (-1684477423 / 200000000000 : ℝ)
  | 19 => (-8551490323 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch067Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1561384697 / 250000000000 : ℝ)
  | 1 => (-1269568513 / 200000000000 : ℝ)
  | 2 => (-1612857927 / 250000000000 : ℝ)
  | 3 => (-6556319453 / 1000000000000 : ℝ)
  | 4 => (-6662519151 / 1000000000000 : ℝ)
  | 5 => (-6770044269 / 1000000000000 : ℝ)
  | 6 => (-1719727097 / 250000000000 : ℝ)
  | 7 => (-3494562603 / 500000000000 : ℝ)
  | 8 => (-7100708541 / 1000000000000 : ℝ)
  | 9 => (-3606836163 / 500000000000 : ℝ)
  | 10 => (-7328030617 / 1000000000000 : ℝ)
  | 11 => (-7443797587 / 1000000000000 : ℝ)
  | 12 => (-1890246883 / 250000000000 : ℝ)
  | 13 => (-767961487 / 100000000000 : ℝ)
  | 14 => (-7799694141 / 1000000000000 : ℝ)
  | 15 => (-7921240009 / 1000000000000 : ℝ)
  | 16 => (-8044267263 / 1000000000000 : ℝ)
  | 17 => (-8168790817 / 1000000000000 : ℝ)
  | 18 => (-8294825711 / 1000000000000 : ℝ)
  | 19 => (-4211193557 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch067Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1340 : ℝ) + (j.val : ℝ)) / 1600)
      (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch067Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch067Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1340 : ℝ) + (j.val : ℝ)) / 1600)
    (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch067Neg70WeightLower j.val) (hpThetaShiftThreeBatch067Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch067Neg70WeightLower, hpThetaShiftThreeBatch067Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch067Neg70_integral_bounds :
    (-6317913 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-12109879 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch067Lower hpThetaJensenCellsBatch067Upper
    hpThetaShiftThreeBatch067Neg70WeightLower hpThetaShiftThreeBatch067Neg70WeightUpper hpThetaJensenCellsBatch067_bounds hpThetaShiftThreeBatch067Neg70_weight_bounds
  have hl : (-6317913 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch067Lower j * hpThetaShiftThreeBatch067Neg70WeightLower j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftThreeBatch067Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftThreeBatch067Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch067Lower j * hpThetaShiftThreeBatch067Neg70WeightUpper j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftThreeBatch067Neg70WeightUpper j) / 1600) ≤ (-12109879 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftThreeBatch067Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1340 : ℝ) / 1600 = 67 / 80 by norm_num,
    show ((1340 : ℝ) + 20) / 1600 = (67 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch067Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1221029859 / 1000000000000 : ℝ)
  | 1 => (245243903 / 200000000000 : ℝ)
  | 2 => (1231359739 / 1000000000000 : ℝ)
  | 3 => (123644919 / 100000000000 : ℝ)
  | 4 => (1241486511 / 1000000000000 : ℝ)
  | 5 => (1246470329 / 1000000000000 : ℝ)
  | 6 => (312849813 / 250000000000 : ℝ)
  | 7 => (306707 / 244140625 : ℝ)
  | 8 => (1261086763 / 1000000000000 : ℝ)
  | 9 => (1265842481 / 1000000000000 : ℝ)
  | 10 => (254107513 / 200000000000 : ℝ)
  | 11 => (159396317 / 125000000000 : ℝ)
  | 12 => (159967487 / 125000000000 : ℝ)
  | 13 => (1284244129 / 1000000000000 : ℝ)
  | 14 => (12886817 / 10000000000 : ℝ)
  | 15 => (1293051057 / 1000000000000 : ℝ)
  | 16 => (1297350627 / 1000000000000 : ℝ)
  | 17 => (1301578821 / 1000000000000 : ℝ)
  | 18 => (326433507 / 250000000000 : ℝ)
  | 19 => (654907309 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch067Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (306554879 / 250000000000 : ℝ)
  | 1 => (61567987 / 50000000000 : ℝ)
  | 2 => (1236449191 / 1000000000000 : ℝ)
  | 3 => (77592907 / 62500000000 : ℝ)
  | 4 => (124647033 / 100000000000 : ℝ)
  | 5 => (1251399253 / 1000000000000 : ℝ)
  | 6 => (1256271873 / 1000000000000 : ℝ)
  | 7 => (315271691 / 250000000000 : ℝ)
  | 8 => (632921241 / 500000000000 : ℝ)
  | 9 => (635268783 / 500000000000 : ℝ)
  | 10 => (1275170537 / 1000000000000 : ℝ)
  | 11 => (1279739897 / 1000000000000 : ℝ)
  | 12 => (128424413 / 100000000000 : ℝ)
  | 13 => (1288681701 / 1000000000000 : ℝ)
  | 14 => (646525529 / 500000000000 : ℝ)
  | 15 => (324337657 / 250000000000 : ℝ)
  | 16 => (650789411 / 500000000000 : ℝ)
  | 17 => (1305734029 / 1000000000000 : ℝ)
  | 18 => (1309814619 / 1000000000000 : ℝ)
  | 19 => (262763789 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch067Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1340 : ℝ) + (j.val : ℝ)) / 1600)
      (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch067Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch067Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1340 : ℝ) + (j.val : ℝ)) / 1600)
    (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch067Neg45WeightLower j.val) (hpThetaShiftThreeBatch067Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch067Neg45WeightLower, hpThetaShiftThreeBatch067Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch067Neg45_integral_bounds :
    (1059641 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (2184873 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch067Lower hpThetaJensenCellsBatch067Upper
    hpThetaShiftThreeBatch067Neg45WeightLower hpThetaShiftThreeBatch067Neg45WeightUpper hpThetaJensenCellsBatch067_bounds hpThetaShiftThreeBatch067Neg45_weight_bounds
  have hl : (1059641 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch067Lower j * hpThetaShiftThreeBatch067Neg45WeightLower j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftThreeBatch067Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftThreeBatch067Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch067Lower j * hpThetaShiftThreeBatch067Neg45WeightUpper j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftThreeBatch067Neg45WeightUpper j) / 1600) ≤ (2184873 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftThreeBatch067Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1340 : ℝ) / 1600 = 67 / 80 by norm_num,
    show ((1340 : ℝ) + 20) / 1600 = (67 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch067Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-20006381 / 100000000000 : ℝ)
  | 1 => (-198171093 / 1000000000000 : ℝ)
  | 2 => (-196245057 / 1000000000000 : ℝ)
  | 3 => (-194285453 / 1000000000000 : ℝ)
  | 4 => (-192292027 / 1000000000000 : ℝ)
  | 5 => (-95132263 / 500000000000 : ℝ)
  | 6 => (-94101349 / 500000000000 : ℝ)
  | 7 => (-93053143 / 500000000000 : ℝ)
  | 8 => (-183975037 / 1000000000000 : ℝ)
  | 9 => (-45452173 / 250000000000 : ℝ)
  | 10 => (-44901749 / 250000000000 : ℝ)
  | 11 => (-17736969 / 100000000000 : ℝ)
  | 12 => (-43774129 / 250000000000 : ℝ)
  | 13 => (-172787213 / 1000000000000 : ℝ)
  | 14 => (-170441523 / 1000000000000 : ℝ)
  | 15 => (-168059183 / 1000000000000 : ℝ)
  | 16 => (-165639933 / 1000000000000 : ℝ)
  | 17 => (-163183509 / 1000000000000 : ℝ)
  | 18 => (-10043103 / 62500000000 : ℝ)
  | 19 => (-79079043 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch067Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-49542773 / 250000000000 : ℝ)
  | 1 => (-3066329 / 15625000000 : ℝ)
  | 2 => (-48571363 / 250000000000 : ℝ)
  | 3 => (-96146013 / 500000000000 : ℝ)
  | 4 => (-7610581 / 40000000000 : ℝ)
  | 5 => (-188202697 / 1000000000000 : ℝ)
  | 6 => (-37221257 / 200000000000 : ℝ)
  | 7 => (-45993759 / 250000000000 : ℝ)
  | 8 => (-181808691 / 1000000000000 : ℝ)
  | 9 => (-35921399 / 200000000000 : ℝ)
  | 10 => (-177369689 / 1000000000000 : ℝ)
  | 11 => (-35019303 / 200000000000 : ℝ)
  | 12 => (-43196803 / 250000000000 : ℝ)
  | 13 => (-85220761 / 500000000000 : ℝ)
  | 14 => (-84029591 / 500000000000 : ℝ)
  | 15 => (-41409983 / 250000000000 : ℝ)
  | 16 => (-40795877 / 250000000000 : ℝ)
  | 17 => (-160689647 / 1000000000000 : ℝ)
  | 18 => (-31631617 / 200000000000 : ℝ)
  | 19 => (-155588557 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch067Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1340 : ℝ) + (j.val : ℝ)) / 1600)
      (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch067Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch067Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1340 : ℝ) + (j.val : ℝ)) / 1600)
    (((1340 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch067Neg25WeightLower j.val) (hpThetaShiftThreeBatch067Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch067Neg25WeightLower, hpThetaShiftThreeBatch067Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch067Neg25_integral_bounds :
    (-9763 / 31250000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (67 / 80 : ℝ) ((67 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-300471 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1340 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch067Lower hpThetaJensenCellsBatch067Upper
    hpThetaShiftThreeBatch067Neg25WeightLower hpThetaShiftThreeBatch067Neg25WeightUpper hpThetaJensenCellsBatch067_bounds hpThetaShiftThreeBatch067Neg25_weight_bounds
  have hl : (-9763 / 31250000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch067Lower j * hpThetaShiftThreeBatch067Neg25WeightLower j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftThreeBatch067Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftThreeBatch067Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch067Lower j * hpThetaShiftThreeBatch067Neg25WeightUpper j)
        (hpThetaJensenCellsBatch067Upper j * hpThetaShiftThreeBatch067Neg25WeightUpper j) / 1600) ≤ (-300471 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch067Lower, hpThetaJensenCellsBatch067Upper,
      hpThetaShiftThreeBatch067Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1340 : ℝ) / 1600 = 67 / 80 by norm_num,
    show ((1340 : ℝ) + 20) / 1600 = (67 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch067Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch067Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch067Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch067Neg25_integral_bounds
end HodgeProofHP
