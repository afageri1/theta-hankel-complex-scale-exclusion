/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch064

/-! Exact signed weight and batch integral certificates, batch 64 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch064Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1188061979167 / 1000000000000 : ℝ)
  | 1 => (-1200200351893 / 1000000000000 : ℝ)
  | 2 => (-242488936951 / 200000000000 : ℝ)
  | 3 => (-1224795766193 / 1000000000000 : ℝ)
  | 4 => (-1546567987 / 1250000000 : ℝ)
  | 5 => (-624910676677 / 500000000000 : ℝ)
  | 6 => (-31562436521 / 25000000000 : ℝ)
  | 7 => (-1275283520477 / 1000000000000 : ℝ)
  | 8 => (-1288180345747 / 1000000000000 : ℝ)
  | 9 => (-81324297201 / 62500000000 : ℝ)
  | 10 => (-262861914513 / 200000000000 : ℝ)
  | 11 => (-663771813307 / 500000000000 : ℝ)
  | 12 => (-167611468919 / 125000000000 : ℝ)
  | 13 => (-33858869649 / 25000000000 : ℝ)
  | 14 => (-1367933574839 / 1000000000000 : ℝ)
  | 15 => (-1381628967637 / 1000000000000 : ℝ)
  | 16 => (-1395441819279 / 1000000000000 : ℝ)
  | 17 => (-140937298999 / 100000000000 : ℝ)
  | 18 => (-355855836331 / 250000000000 : ℝ)
  | 19 => (-1437593756193 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch064Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-294007195767 / 250000000000 : ℝ)
  | 1 => (-594030989583 / 500000000000 : ℝ)
  | 2 => (-300050087973 / 250000000000 : ℝ)
  | 3 => (-606222342377 / 500000000000 : ℝ)
  | 4 => (-76549735387 / 62500000000 : ℝ)
  | 5 => (-1237254389599 / 1000000000000 : ℝ)
  | 6 => (-1249821353353 / 1000000000000 : ℝ)
  | 7 => (-1262497460839 / 1000000000000 : ℝ)
  | 8 => (-318820880119 / 250000000000 : ℝ)
  | 9 => (-644090172873 / 500000000000 : ℝ)
  | 10 => (-260237751043 / 200000000000 : ℝ)
  | 11 => (-328577393141 / 250000000000 : ℝ)
  | 12 => (-1327543626613 / 1000000000000 : ℝ)
  | 13 => (-1340891751351 / 1000000000000 : ℝ)
  | 14 => (-1354354785959 / 1000000000000 : ℝ)
  | 15 => (-683966787419 / 500000000000 : ℝ)
  | 16 => (-345407241909 / 250000000000 : ℝ)
  | 17 => (-697720909639 / 500000000000 : ℝ)
  | 18 => (-1409372989989 / 1000000000000 : ℝ)
  | 19 => (-1423423345323 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch064Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1280 : ℝ) + (j.val : ℝ)) / 1600)
      (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch064Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch064Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1280 : ℝ) + (j.val : ℝ)) / 1600)
    (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch064Neg100WeightLower j.val) (hpThetaShiftTwoBatch064Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch064Neg100WeightLower, hpThetaShiftTwoBatch064Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch064Neg100_integral_bounds :
    (-128048177 / 20000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-3090127297 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch064Lower hpThetaJensenCellsBatch064Upper
    hpThetaShiftTwoBatch064Neg100WeightLower hpThetaShiftTwoBatch064Neg100WeightUpper hpThetaJensenCellsBatch064_bounds hpThetaShiftTwoBatch064Neg100_weight_bounds
  have hl : (-128048177 / 20000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch064Lower j * hpThetaShiftTwoBatch064Neg100WeightLower j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftTwoBatch064Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftTwoBatch064Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch064Lower j * hpThetaShiftTwoBatch064Neg100WeightUpper j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftTwoBatch064Neg100WeightUpper j) / 1600) ≤ (-3090127297 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftTwoBatch064Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1280 : ℝ) / 1600 = 64 / 80 by norm_num,
    show ((1280 : ℝ) + 20) / 1600 = (64 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch064Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-51397958933 / 500000000000 : ℝ)
  | 1 => (-52210002703 / 500000000000 : ℝ)
  | 2 => (-2651556453 / 25000000000 : ℝ)
  | 3 => (-53861417367 / 500000000000 : ℝ)
  | 4 => (-27350473771 / 250000000000 : ℝ)
  | 5 => (-111099600131 / 1000000000000 : ℝ)
  | 6 => (-112816111959 / 1000000000000 : ℝ)
  | 7 => (-114551593789 / 1000000000000 : ℝ)
  | 8 => (-116306209977 / 1000000000000 : ℝ)
  | 9 => (-29520031507 / 250000000000 : ℝ)
  | 10 => (-119873508599 / 1000000000000 : ℝ)
  | 11 => (-60843262753 / 500000000000 : ℝ)
  | 12 => (-123519345729 / 1000000000000 : ℝ)
  | 13 => (-62686069711 / 500000000000 : ℝ)
  | 14 => (-63622538957 / 500000000000 : ℝ)
  | 15 => (-129138333723 / 1000000000000 : ℝ)
  | 16 => (-26210416111 / 200000000000 : ℝ)
  | 17 => (-132986493317 / 1000000000000 : ℝ)
  | 18 => (-3373543703 / 25000000000 : ℝ)
  | 19 => (-68459011143 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch064Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-101189837883 / 1000000000000 : ℝ)
  | 1 => (-20559183573 / 200000000000 : ℝ)
  | 2 => (-20884001081 / 200000000000 : ℝ)
  | 3 => (-106062258119 / 1000000000000 : ℝ)
  | 4 => (-107722834733 / 1000000000000 : ℝ)
  | 5 => (-109401895083 / 1000000000000 : ℝ)
  | 6 => (-11109960013 / 100000000000 : ℝ)
  | 7 => (-56408055979 / 500000000000 : ℝ)
  | 8 => (-28637898447 / 250000000000 : ℝ)
  | 9 => (-14538276247 / 125000000000 : ℝ)
  | 10 => (-118080126027 / 1000000000000 : ℝ)
  | 11 => (-59936754299 / 500000000000 : ℝ)
  | 12 => (-24337305101 / 200000000000 : ℝ)
  | 13 => (-1929989777 / 15625000000 : ℝ)
  | 14 => (-125372139421 / 1000000000000 : ℝ)
  | 15 => (-127245077913 / 1000000000000 : ℝ)
  | 16 => (-64569166861 / 500000000000 : ℝ)
  | 17 => (-65526040277 / 500000000000 : ℝ)
  | 18 => (-33246623329 / 250000000000 : ℝ)
  | 19 => (-134941748119 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch064Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1280 : ℝ) + (j.val : ℝ)) / 1600)
      (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch064Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch064Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1280 : ℝ) + (j.val : ℝ)) / 1600)
    (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch064Neg65WeightLower j.val) (hpThetaShiftTwoBatch064Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch064Neg65WeightLower, hpThetaShiftTwoBatch064Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch064Neg65_integral_bounds :
    (-290798357 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-279285089 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch064Lower hpThetaJensenCellsBatch064Upper
    hpThetaShiftTwoBatch064Neg65WeightLower hpThetaShiftTwoBatch064Neg65WeightUpper hpThetaJensenCellsBatch064_bounds hpThetaShiftTwoBatch064Neg65_weight_bounds
  have hl : (-290798357 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch064Lower j * hpThetaShiftTwoBatch064Neg65WeightLower j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftTwoBatch064Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftTwoBatch064Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch064Lower j * hpThetaShiftTwoBatch064Neg65WeightUpper j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftTwoBatch064Neg65WeightUpper j) / 1600) ≤ (-279285089 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftTwoBatch064Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1280 : ℝ) / 1600 = 64 / 80 by norm_num,
    show ((1280 : ℝ) + 20) / 1600 = (64 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch064Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (22323929641 / 1000000000000 : ℝ)
  | 1 => (22308787709 / 1000000000000 : ℝ)
  | 2 => (22291396763 / 1000000000000 : ℝ)
  | 3 => (69599143 / 3125000000 : ℝ)
  | 4 => (4449948677 / 200000000000 : ℝ)
  | 5 => (347272157 / 15625000000 : ℝ)
  | 6 => (22198717883 / 1000000000000 : ℝ)
  | 7 => (5542402687 / 250000000000 : ℝ)
  | 8 => (1106903211 / 50000000000 : ℝ)
  | 9 => (5526011399 / 250000000000 : ℝ)
  | 10 => (2206752189 / 100000000000 : ℝ)
  | 11 => (2202845983 / 100000000000 : ℝ)
  | 12 => (21986825859 / 1000000000000 : ℝ)
  | 13 => (21942586131 / 1000000000000 : ℝ)
  | 14 => (21895706509 / 1000000000000 : ℝ)
  | 15 => (21846152567 / 1000000000000 : ℝ)
  | 16 => (10896944791 / 500000000000 : ℝ)
  | 17 => (4347776507 / 200000000000 : ℝ)
  | 18 => (21681096113 / 1000000000000 : ℝ)
  | 19 => (21620494699 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch064Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (11168426667 / 500000000000 : ℝ)
  | 1 => (11161964821 / 500000000000 : ℝ)
  | 2 => (2230878771 / 100000000000 : ℝ)
  | 3 => (5572849191 / 250000000000 : ℝ)
  | 4 => (22271725761 / 1000000000000 : ℝ)
  | 5 => (11124871693 / 500000000000 : ℝ)
  | 6 => (22225418049 / 1000000000000 : ℝ)
  | 7 => (5549679471 / 250000000000 : ℝ)
  | 8 => (22169610749 / 1000000000000 : ℝ)
  | 9 => (22138064221 / 1000000000000 : ℝ)
  | 10 => (22104045597 / 1000000000000 : ℝ)
  | 11 => (22067521891 / 1000000000000 : ℝ)
  | 12 => (22028459831 / 1000000000000 : ℝ)
  | 13 => (1099341293 / 50000000000 : ℝ)
  | 14 => (5485646533 / 250000000000 : ℝ)
  | 15 => (2189570651 / 100000000000 : ℝ)
  | 16 => (2730769071 / 125000000000 : ℝ)
  | 17 => (21793889583 / 1000000000000 : ℝ)
  | 18 => (2717360317 / 125000000000 : ℝ)
  | 19 => (10840548057 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch064Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1280 : ℝ) + (j.val : ℝ)) / 1600)
      (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch064Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch064Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1280 : ℝ) + (j.val : ℝ)) / 1600)
    (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch064Neg45WeightLower j.val) (hpThetaShiftTwoBatch064Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch064Neg45WeightLower, hpThetaShiftTwoBatch064Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch064Neg45_integral_bounds :
    (105766151 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (54320583 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch064Lower hpThetaJensenCellsBatch064Upper
    hpThetaShiftTwoBatch064Neg45WeightLower hpThetaShiftTwoBatch064Neg45WeightUpper hpThetaJensenCellsBatch064_bounds hpThetaShiftTwoBatch064Neg45_weight_bounds
  have hl : (105766151 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch064Lower j * hpThetaShiftTwoBatch064Neg45WeightLower j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftTwoBatch064Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftTwoBatch064Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch064Lower j * hpThetaShiftTwoBatch064Neg45WeightUpper j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftTwoBatch064Neg45WeightUpper j) / 1600) ≤ (54320583 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftTwoBatch064Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1280 : ℝ) / 1600 = 64 / 80 by norm_num,
    show ((1280 : ℝ) + 20) / 1600 = (64 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch064Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1029417989 / 500000000000 : ℝ)
  | 1 => (533662681 / 250000000000 : ℝ)
  | 2 => (2211069813 / 1000000000000 : ℝ)
  | 3 => (1144047601 / 500000000000 : ℝ)
  | 4 => (1182864417 / 500000000000 : ℝ)
  | 5 => (2443972649 / 1000000000000 : ℝ)
  | 6 => (630707143 / 250000000000 : ℝ)
  | 7 => (2602298521 / 1000000000000 : ℝ)
  | 8 => (2682384407 / 1000000000000 : ℝ)
  | 9 => (1381544063 / 500000000000 : ℝ)
  | 10 => (2844411567 / 1000000000000 : ℝ)
  | 11 => (2926356611 / 1000000000000 : ℝ)
  | 12 => (3008925123 / 1000000000000 : ℝ)
  | 13 => (773029741 / 250000000000 : ℝ)
  | 14 => (3175939979 / 1000000000000 : ℝ)
  | 15 => (1630195003 / 500000000000 : ℝ)
  | 16 => (3345470869 / 1000000000000 : ℝ)
  | 17 => (686236877 / 200000000000 : ℝ)
  | 18 => (703506471 / 200000000000 : ℝ)
  | 19 => (901129143 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch064Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (85386029 / 40000000000 : ℝ)
  | 1 => (1105534907 / 500000000000 : ℝ)
  | 2 => (2288095203 / 1000000000000 : ℝ)
  | 3 => (473145767 / 200000000000 : ℝ)
  | 4 => (48879453 / 20000000000 : ℝ)
  | 5 => (2522828573 / 1000000000000 : ℝ)
  | 6 => (1301149261 / 500000000000 : ℝ)
  | 7 => (335298051 / 125000000000 : ℝ)
  | 8 => (2763088127 / 1000000000000 : ℝ)
  | 9 => (177775723 / 62500000000 : ℝ)
  | 10 => (731589153 / 250000000000 : ℝ)
  | 11 => (752231281 / 250000000000 : ℝ)
  | 12 => (618423793 / 200000000000 : ℝ)
  | 13 => (158796999 / 50000000000 : ℝ)
  | 14 => (3260390007 / 1000000000000 : ℝ)
  | 15 => (334547087 / 100000000000 : ℝ)
  | 16 => (1715592193 / 500000000000 : ℝ)
  | 17 => (879383089 / 250000000000 : ℝ)
  | 18 => (3604516573 / 1000000000000 : ℝ)
  | 19 => (57689669 / 15625000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch064Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1280 : ℝ) + (j.val : ℝ)) / 1600)
      (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch064Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch064Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1280 : ℝ) + (j.val : ℝ)) / 1600)
    (((1280 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch064Neg25WeightLower j.val) (hpThetaShiftTwoBatch064Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch064Neg25WeightLower, hpThetaShiftTwoBatch064Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch064Neg25_integral_bounds :
    (6636081 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (64 / 80 : ℝ) ((64 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (700591 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1280 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch064Lower hpThetaJensenCellsBatch064Upper
    hpThetaShiftTwoBatch064Neg25WeightLower hpThetaShiftTwoBatch064Neg25WeightUpper hpThetaJensenCellsBatch064_bounds hpThetaShiftTwoBatch064Neg25_weight_bounds
  have hl : (6636081 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch064Lower j * hpThetaShiftTwoBatch064Neg25WeightLower j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftTwoBatch064Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftTwoBatch064Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch064Lower j * hpThetaShiftTwoBatch064Neg25WeightUpper j)
        (hpThetaJensenCellsBatch064Upper j * hpThetaShiftTwoBatch064Neg25WeightUpper j) / 1600) ≤ (700591 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch064Lower, hpThetaJensenCellsBatch064Upper,
      hpThetaShiftTwoBatch064Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1280 : ℝ) / 1600 = 64 / 80 by norm_num,
    show ((1280 : ℝ) + 20) / 1600 = (64 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch064Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch064Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch064Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch064Neg25_integral_bounds
end HodgeProofHP
