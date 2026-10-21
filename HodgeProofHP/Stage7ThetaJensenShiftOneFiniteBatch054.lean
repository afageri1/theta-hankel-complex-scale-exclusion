/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch054

/-! Exact signed weight and batch integral certificates, batch 54 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch054Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3522768355673 / 500000000000 : ℝ)
  | 1 => (-178100077383 / 25000000000 : ℝ)
  | 2 => (-1800788825749 / 250000000000 : ℝ)
  | 3 => (-3641499043461 / 500000000000 : ℝ)
  | 4 => (-7363536225479 / 1000000000000 : ℝ)
  | 5 => (-3722387261491 / 500000000000 : ℝ)
  | 6 => (-752671780979 / 100000000000 : ℝ)
  | 7 => (-475585683901 / 62500000000 : ℝ)
  | 8 => (-7692738803627 / 1000000000000 : ℝ)
  | 9 => (-7776826302559 / 1000000000000 : ℝ)
  | 10 => (-314465534993 / 40000000000 : ℝ)
  | 11 => (-7947179982619 / 1000000000000 : ℝ)
  | 12 => (-8033456114831 / 1000000000000 : ℝ)
  | 13 => (-507529486697 / 62500000000 : ℝ)
  | 14 => (-1641646408437 / 200000000000 : ℝ)
  | 15 => (-2074185487389 / 250000000000 : ℝ)
  | 16 => (-1048250825753 / 125000000000 : ℝ)
  | 17 => (-8476031135591 / 1000000000000 : ℝ)
  | 18 => (-8566820689613 / 1000000000000 : ℝ)
  | 19 => (-135287194483 / 15625000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch054Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1741937856061 / 250000000000 : ℝ)
  | 1 => (-1409107342269 / 200000000000 : ℝ)
  | 2 => (-7124003095319 / 1000000000000 : ℝ)
  | 3 => (-1440631060599 / 200000000000 : ℝ)
  | 4 => (-7282998086921 / 1000000000000 : ℝ)
  | 5 => (-3681768112739 / 500000000000 : ℝ)
  | 6 => (-7444774522981 / 1000000000000 : ℝ)
  | 7 => (-7526717809789 / 1000000000000 : ℝ)
  | 8 => (-1521874188483 / 200000000000 : ℝ)
  | 9 => (-3846369401813 / 500000000000 : ℝ)
  | 10 => (-3888413151279 / 500000000000 : ℝ)
  | 11 => (-982704796853 / 125000000000 : ℝ)
  | 12 => (-3973589991309 / 500000000000 : ℝ)
  | 13 => (-803345611483 / 100000000000 : ℝ)
  | 14 => (-8120471787151 / 1000000000000 : ℝ)
  | 15 => (-1026029005273 / 125000000000 : ℝ)
  | 16 => (-1659348389911 / 200000000000 : ℝ)
  | 17 => (-8386006606023 / 1000000000000 : ℝ)
  | 18 => (-847603113559 / 100000000000 : ℝ)
  | 19 => (-2141705172403 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch054Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1080 : ℝ) + (j.val : ℝ)) / 1600)
      (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch054Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch054Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1080 : ℝ) + (j.val : ℝ)) / 1600)
    (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch054Neg100WeightLower j.val) (hpThetaShiftOneBatch054Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch054Neg100WeightLower, hpThetaShiftOneBatch054Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch054Neg100_integral_bounds :
    (-688426530383 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-20839503441 / 31250000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1080 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch054Lower hpThetaJensenCellsBatch054Upper
    hpThetaShiftOneBatch054Neg100WeightLower hpThetaShiftOneBatch054Neg100WeightUpper hpThetaJensenCellsBatch054_bounds hpThetaShiftOneBatch054Neg100_weight_bounds
  have hl : (-688426530383 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch054Lower j * hpThetaShiftOneBatch054Neg100WeightLower j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftOneBatch054Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftOneBatch054Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch054Lower j * hpThetaShiftOneBatch054Neg100WeightUpper j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftOneBatch054Neg100WeightUpper j) / 1600) ≤ (-20839503441 / 31250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftOneBatch054Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1080 : ℝ) / 1600 = 54 / 80 by norm_num,
    show ((1080 : ℝ) + 20) / 1600 = (54 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch054Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-41705643533 / 200000000000 : ℝ)
  | 1 => (-217454690857 / 1000000000000 : ℝ)
  | 2 => (-56624684581 / 250000000000 : ℝ)
  | 3 => (-9426454681 / 40000000000 : ℝ)
  | 4 => (-122471795057 / 500000000000 : ℝ)
  | 5 => (-63586606743 / 250000000000 : ℝ)
  | 6 => (-263870903231 / 1000000000000 : ℝ)
  | 7 => (-54703610161 / 200000000000 : ℝ)
  | 8 => (-70822226979 / 250000000000 : ℝ)
  | 9 => (-293184519121 / 1000000000000 : ℝ)
  | 10 => (-18950370959 / 62500000000 : ℝ)
  | 11 => (-156677106949 / 500000000000 : ℝ)
  | 12 => (-323630418521 / 1000000000000 : ℝ)
  | 13 => (-334035619397 / 1000000000000 : ℝ)
  | 14 => (-344570893189 / 1000000000000 : ℝ)
  | 15 => (-44404665383 / 125000000000 : ℝ)
  | 16 => (-183017999363 / 500000000000 : ℝ)
  | 17 => (-376968016441 / 1000000000000 : ℝ)
  | 18 => (-194017239533 / 500000000000 : ℝ)
  | 19 => (-199618248041 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch054Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-199718317959 / 1000000000000 : ℝ)
  | 1 => (-3258253401 / 15625000000 : ℝ)
  | 2 => (-27181836357 / 125000000000 : ℝ)
  | 3 => (-226498738323 / 1000000000000 : ℝ)
  | 4 => (-14728835439 / 62500000000 : ℝ)
  | 5 => (-244943590113 / 1000000000000 : ℝ)
  | 6 => (-254346426971 / 1000000000000 : ℝ)
  | 7 => (-26387090323 / 100000000000 : ℝ)
  | 8 => (-68379512701 / 250000000000 : ℝ)
  | 9 => (-56657781583 / 200000000000 : ℝ)
  | 10 => (-3664806489 / 12500000000 : ℝ)
  | 11 => (-303205935343 / 1000000000000 : ℝ)
  | 12 => (-313354213897 / 1000000000000 : ℝ)
  | 13 => (-8090760463 / 25000000000 : ℝ)
  | 14 => (-83508904849 / 250000000000 : ℝ)
  | 15 => (-86142723297 / 250000000000 : ℝ)
  | 16 => (-355237323063 / 1000000000000 : ℝ)
  | 17 => (-14641439949 / 40000000000 : ℝ)
  | 18 => (-9424200411 / 25000000000 : ℝ)
  | 19 => (-77606895813 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch054Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1080 : ℝ) + (j.val : ℝ)) / 1600)
      (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch054Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch054Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1080 : ℝ) + (j.val : ℝ)) / 1600)
    (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch054Neg65WeightLower j.val) (hpThetaShiftOneBatch054Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch054Neg65WeightLower, hpThetaShiftOneBatch054Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch054Neg65_integral_bounds :
    (-13075965043 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-6187749563 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1080 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch054Lower hpThetaJensenCellsBatch054Upper
    hpThetaShiftOneBatch054Neg65WeightLower hpThetaShiftOneBatch054Neg65WeightUpper hpThetaJensenCellsBatch054_bounds hpThetaShiftOneBatch054Neg65_weight_bounds
  have hl : (-13075965043 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch054Lower j * hpThetaShiftOneBatch054Neg65WeightLower j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftOneBatch054Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftOneBatch054Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch054Lower j * hpThetaShiftOneBatch054Neg65WeightUpper j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftOneBatch054Neg65WeightUpper j) / 1600) ≤ (-6187749563 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftOneBatch054Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1080 : ℝ) / 1600 = 54 / 80 by norm_num,
    show ((1080 : ℝ) + 20) / 1600 = (54 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch054Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (73386888833 / 250000000000 : ℝ)
  | 1 => (147568733887 / 500000000000 : ℝ)
  | 2 => (296724784613 / 1000000000000 : ℝ)
  | 3 => (298309387209 / 1000000000000 : ℝ)
  | 4 => (299891155849 / 1000000000000 : ℝ)
  | 5 => (15073498487 / 50000000000 : ℝ)
  | 6 => (303045707001 / 1000000000000 : ℝ)
  | 7 => (38077280583 / 125000000000 : ℝ)
  | 8 => (306187458661 / 1000000000000 : ℝ)
  | 9 => (307753223821 / 1000000000000 : ℝ)
  | 10 => (309315413867 / 1000000000000 : ℝ)
  | 11 => (77718475351 / 250000000000 : ℝ)
  | 12 => (1952678487 / 6250000000 : ℝ)
  | 13 => (156989626887 / 500000000000 : ℝ)
  | 14 => (63105171639 / 200000000000 : ℝ)
  | 15 => (158534119637 / 500000000000 : ℝ)
  | 16 => (79651565989 / 250000000000 : ℝ)
  | 17 => (8003494951 / 25000000000 : ℝ)
  | 18 => (64333741233 / 200000000000 : ℝ)
  | 19 => (323192851811 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch054Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (11805498711 / 40000000000 : ℝ)
  | 1 => (148362392307 / 500000000000 : ℝ)
  | 2 => (29830938721 / 100000000000 : ℝ)
  | 3 => (5997823117 / 20000000000 : ℝ)
  | 4 => (301469969741 / 1000000000000 : ℝ)
  | 5 => (151522853501 / 500000000000 : ℝ)
  | 6 => (60923648933 / 200000000000 : ℝ)
  | 7 => (153093729331 / 500000000000 : ℝ)
  | 8 => (153876611911 / 500000000000 : ℝ)
  | 9 => (77328853467 / 250000000000 : ℝ)
  | 10 => (62174780281 / 200000000000 : ℝ)
  | 11 => (312428557921 / 1000000000000 : ℝ)
  | 12 => (12559170151 / 40000000000 : ℝ)
  | 13 => (78881464549 / 250000000000 : ℝ)
  | 14 => (12682729571 / 40000000000 : ℝ)
  | 15 => (318606263957 / 1000000000000 : ℝ)
  | 16 => (320139798041 / 1000000000000 : ℝ)
  | 17 => (160834353083 / 500000000000 : ℝ)
  | 18 => (80798212953 / 250000000000 : ℝ)
  | 19 => (324712097291 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch054Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1080 : ℝ) + (j.val : ℝ)) / 1600)
      (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch054Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch054Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1080 : ℝ) + (j.val : ℝ)) / 1600)
    (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch054Neg40WeightLower j.val) (hpThetaShiftOneBatch054Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch054Neg40WeightLower, hpThetaShiftOneBatch054Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch054Neg40_integral_bounds :
    (26618016131 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (27319425617 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1080 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch054Lower hpThetaJensenCellsBatch054Upper
    hpThetaShiftOneBatch054Neg40WeightLower hpThetaShiftOneBatch054Neg40WeightUpper hpThetaJensenCellsBatch054_bounds hpThetaShiftOneBatch054Neg40_weight_bounds
  have hl : (26618016131 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch054Lower j * hpThetaShiftOneBatch054Neg40WeightLower j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftOneBatch054Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftOneBatch054Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch054Lower j * hpThetaShiftOneBatch054Neg40WeightUpper j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftOneBatch054Neg40WeightUpper j) / 1600) ≤ (27319425617 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftOneBatch054Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1080 : ℝ) / 1600 = 54 / 80 by norm_num,
    show ((1080 : ℝ) + 20) / 1600 = (54 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch054Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8690405477 / 125000000000 : ℝ)
  | 1 => (-8651124933 / 125000000000 : ℝ)
  | 2 => (-13778110559 / 200000000000 : ℝ)
  | 3 => (-68567888253 / 1000000000000 : ℝ)
  | 4 => (-68240990303 / 1000000000000 : ℝ)
  | 5 => (-33954921717 / 500000000000 : ℝ)
  | 6 => (-67574432157 / 1000000000000 : ℝ)
  | 7 => (-4202171313 / 62500000000 : ℝ)
  | 8 => (-16722688637 / 250000000000 : ℝ)
  | 9 => (-66542457361 / 1000000000000 : ℝ)
  | 10 => (-66189834057 / 1000000000000 : ℝ)
  | 11 => (-65832869273 / 1000000000000 : ℝ)
  | 12 => (-6547154767 / 100000000000 : ℝ)
  | 13 => (-32552926969 / 500000000000 : ℝ)
  | 14 => (-32367886397 / 500000000000 : ℝ)
  | 15 => (-3218064449 / 50000000000 : ℝ)
  | 16 => (-63982387271 / 1000000000000 : ℝ)
  | 17 => (-31799526233 / 500000000000 : ℝ)
  | 18 => (-31605634699 / 500000000000 : ℝ)
  | 19 => (-2512760917 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch054Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-69208999463 / 1000000000000 : ℝ)
  | 1 => (-34445276397 / 500000000000 : ℝ)
  | 2 => (-17141972063 / 250000000000 : ℝ)
  | 3 => (-34120495151 / 500000000000 : ℝ)
  | 4 => (-67909843433 / 1000000000000 : ℝ)
  | 5 => (-16893608039 / 250000000000 : ℝ)
  | 6 => (-67234741007 / 1000000000000 : ℝ)
  | 7 => (-66890754547 / 1000000000000 : ℝ)
  | 8 => (-831780717 / 12500000000 : ℝ)
  | 9 => (-8273729257 / 125000000000 : ℝ)
  | 10 => (-8229108659 / 125000000000 : ℝ)
  | 11 => (-65471547669 / 1000000000000 : ℝ)
  | 12 => (-65105853937 / 1000000000000 : ℝ)
  | 13 => (-64735772793 / 1000000000000 : ℝ)
  | 14 => (-64361288979 / 1000000000000 : ℝ)
  | 15 => (-6398238727 / 100000000000 : ℝ)
  | 16 => (-12719810493 / 200000000000 : ℝ)
  | 17 => (-63211269397 / 1000000000000 : ℝ)
  | 18 => (-15704755731 / 250000000000 : ℝ)
  | 19 => (-62422297939 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch054Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1080 : ℝ) + (j.val : ℝ)) / 1600)
      (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch054Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch054Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1080 : ℝ) + (j.val : ℝ)) / 1600)
    (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch054Neg20WeightLower j.val) (hpThetaShiftOneBatch054Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch054Neg20WeightLower, hpThetaShiftOneBatch054Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch054Neg20_integral_bounds :
    (-1466639647 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-5714390883 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1080 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch054Lower hpThetaJensenCellsBatch054Upper
    hpThetaShiftOneBatch054Neg20WeightLower hpThetaShiftOneBatch054Neg20WeightUpper hpThetaJensenCellsBatch054_bounds hpThetaShiftOneBatch054Neg20_weight_bounds
  have hl : (-1466639647 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch054Lower j * hpThetaShiftOneBatch054Neg20WeightLower j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftOneBatch054Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftOneBatch054Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch054Lower j * hpThetaShiftOneBatch054Neg20WeightUpper j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftOneBatch054Neg20WeightUpper j) / 1600) ≤ (-5714390883 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftOneBatch054Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1080 : ℝ) / 1600 = 54 / 80 by norm_num,
    show ((1080 : ℝ) + 20) / 1600 = (54 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch054Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch054Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch054Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch054Neg20_integral_bounds
end HodgeProofHP
