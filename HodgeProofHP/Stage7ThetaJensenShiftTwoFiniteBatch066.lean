/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch066

/-! Exact signed weight and batch integral certificates, batch 66 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch066Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-220563250493 / 125000000000 : ℝ)
  | 1 => (-890774587193 / 500000000000 : ℝ)
  | 2 => (-449683493681 / 250000000000 : ℝ)
  | 3 => (-1816061412979 / 1000000000000 : ℝ)
  | 4 => (-366706500651 / 200000000000 : ℝ)
  | 5 => (-1851148265767 / 1000000000000 : ℝ)
  | 6 => (-467227431719 / 250000000000 : ℝ)
  | 7 => (-471704479779 / 250000000000 : ℝ)
  | 8 => (-76194955249 / 40000000000 : ℝ)
  | 9 => (-1923078658181 / 1000000000000 : ℝ)
  | 10 => (-242679162653 / 125000000000 : ℝ)
  | 11 => (-1959938867899 / 1000000000000 : ℝ)
  | 12 => (-989298211039 / 500000000000 : ℝ)
  | 13 => (-399481406799 / 200000000000 : ℝ)
  | 14 => (-1008185890139 / 500000000000 : ℝ)
  | 15 => (-2035491743983 / 1000000000000 : ℝ)
  | 16 => (-2054768014621 / 1000000000000 : ℝ)
  | 17 => (-16204700689 / 7812500000 : ℝ)
  | 18 => (-1046896933611 / 500000000000 : ℝ)
  | 19 => (-528386415197 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch066Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1747603461427 / 1000000000000 : ℝ)
  | 1 => (-1764506003943 / 1000000000000 : ℝ)
  | 2 => (-356309834877 / 200000000000 : ℝ)
  | 3 => (-1798733974723 / 1000000000000 : ℝ)
  | 4 => (-908030706489 / 500000000000 : ℝ)
  | 5 => (-916766251627 / 500000000000 : ℝ)
  | 6 => (-925574132883 / 500000000000 : ℝ)
  | 7 => (-2990255563 / 1600000000 : ℝ)
  | 8 => (-377363583823 / 200000000000 : ℝ)
  | 9 => (-238109235153 / 125000000000 : ℝ)
  | 10 => (-96153932909 / 50000000000 : ℝ)
  | 11 => (-1941433301223 / 1000000000000 : ℝ)
  | 12 => (-979969433949 / 500000000000 : ℝ)
  | 13 => (-1978596422077 / 1000000000000 : ℝ)
  | 14 => (-998703516997 / 500000000000 : ℝ)
  | 15 => (-2016371780277 / 1000000000000 : ℝ)
  | 16 => (-1017745871991 / 500000000000 : ℝ)
  | 17 => (-102738400731 / 50000000000 : ℝ)
  | 18 => (-2074201688191 / 1000000000000 : ℝ)
  | 19 => (-2093793867221 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch066Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1320 : ℝ) + (j.val : ℝ)) / 1600)
      (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch066Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch066Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1320 : ℝ) + (j.val : ℝ)) / 1600)
    (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch066Neg100WeightLower j.val) (hpThetaShiftTwoBatch066Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch066Neg100WeightLower, hpThetaShiftTwoBatch066Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch066Neg100_integral_bounds :
    (-4748075351 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-2290592963 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch066Lower hpThetaJensenCellsBatch066Upper
    hpThetaShiftTwoBatch066Neg100WeightLower hpThetaShiftTwoBatch066Neg100WeightUpper hpThetaJensenCellsBatch066_bounds hpThetaShiftTwoBatch066Neg100_weight_bounds
  have hl : (-4748075351 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch066Lower j * hpThetaShiftTwoBatch066Neg100WeightLower j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftTwoBatch066Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftTwoBatch066Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch066Lower j * hpThetaShiftTwoBatch066Neg100WeightUpper j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftTwoBatch066Neg100WeightUpper j) / 1600) ≤ (-2290592963 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftTwoBatch066Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1320 : ℝ) / 1600 = 66 / 80 by norm_num,
    show ((1320 : ℝ) + 20) / 1600 = (66 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch066Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-183602527659 / 1000000000000 : ℝ)
  | 1 => (-7443545173 / 40000000000 : ℝ)
  | 2 => (-188600179021 / 1000000000000 : ℝ)
  | 3 => (-38227477047 / 200000000000 : ℝ)
  | 4 => (-96850228921 / 500000000000 : ℝ)
  | 5 => (-98144804059 / 500000000000 : ℝ)
  | 6 => (-99452524369 / 500000000000 : ℝ)
  | 7 => (-1574585889 / 7812500000 : ℝ)
  | 8 => (-51053914697 / 250000000000 : ℝ)
  | 9 => (-206911260659 / 1000000000000 : ℝ)
  | 10 => (-13102126111 / 62500000000 : ℝ)
  | 11 => (-53096037487 / 250000000000 : ℝ)
  | 12 => (-215161878437 / 1000000000000 : ℝ)
  | 13 => (-5449185649 / 25000000000 : ℝ)
  | 14 => (-110400508351 / 500000000000 : ℝ)
  | 15 => (-223662876319 / 1000000000000 : ℝ)
  | 16 => (-226553231949 / 1000000000000 : ℝ)
  | 17 => (-114736156109 / 500000000000 : ℝ)
  | 18 => (-929681389 / 4000000000 : ℝ)
  | 19 => (-117698784337 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch066Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-90570833457 / 500000000000 : ℝ)
  | 1 => (-91801263829 / 500000000000 : ℝ)
  | 2 => (-46522157331 / 250000000000 : ℝ)
  | 3 => (-9430008951 / 50000000000 : ℝ)
  | 4 => (-95568692617 / 500000000000 : ℝ)
  | 5 => (-193700457841 / 1000000000000 : ℝ)
  | 6 => (-196289608117 / 1000000000000 : ℝ)
  | 7 => (-198905048737 / 1000000000000 : ℝ)
  | 8 => (-201546993791 / 1000000000000 : ℝ)
  | 9 => (-204215658787 / 1000000000000 : ℝ)
  | 10 => (-103455630329 / 500000000000 : ℝ)
  | 11 => (-8385360711 / 40000000000 : ℝ)
  | 12 => (-212384149947 / 1000000000000 : ℝ)
  | 13 => (-53790469609 / 250000000000 : ℝ)
  | 14 => (-217967425959 / 1000000000000 : ℝ)
  | 15 => (-220801016701 / 1000000000000 : ℝ)
  | 16 => (-111831438159 / 500000000000 : ℝ)
  | 17 => (-56638307987 / 250000000000 : ℝ)
  | 18 => (-229472312217 / 1000000000000 : ℝ)
  | 19 => (-232420347249 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch066Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1320 : ℝ) + (j.val : ℝ)) / 1600)
      (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch066Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch066Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1320 : ℝ) + (j.val : ℝ)) / 1600)
    (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch066Neg65WeightLower j.val) (hpThetaShiftTwoBatch066Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch066Neg65WeightLower, hpThetaShiftTwoBatch066Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch066Neg65_integral_bounds :
    (-15973463 / 31250000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-9828247 / 20000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch066Lower hpThetaJensenCellsBatch066Upper
    hpThetaShiftTwoBatch066Neg65WeightLower hpThetaShiftTwoBatch066Neg65WeightUpper hpThetaJensenCellsBatch066_bounds hpThetaShiftTwoBatch066Neg65_weight_bounds
  have hl : (-15973463 / 31250000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch066Lower j * hpThetaShiftTwoBatch066Neg65WeightLower j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftTwoBatch066Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftTwoBatch066Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch066Lower j * hpThetaShiftTwoBatch066Neg65WeightUpper j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftTwoBatch066Neg65WeightUpper j) / 1600) ≤ (-9828247 / 20000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftTwoBatch066Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1320 : ℝ) / 1600 = 66 / 80 by norm_num,
    show ((1320 : ℝ) + 20) / 1600 = (66 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch066Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (9815622333 / 500000000000 : ℝ)
  | 1 => (3899814501 / 200000000000 : ℝ)
  | 2 => (3872635823 / 200000000000 : ℝ)
  | 3 => (19223521109 / 1000000000000 : ℝ)
  | 4 => (19080054749 / 1000000000000 : ℝ)
  | 5 => (18932735947 / 1000000000000 : ℝ)
  | 6 => (18781520259 / 1000000000000 : ℝ)
  | 7 => (18626362889 / 1000000000000 : ℝ)
  | 8 => (18467218681 / 1000000000000 : ℝ)
  | 9 => (9152021059 / 500000000000 : ℝ)
  | 10 => (18136787323 / 1000000000000 : ℝ)
  | 11 => (8982704027 / 500000000000 : ℝ)
  | 12 => (17789857701 / 1000000000000 : ℝ)
  | 13 => (17610089287 / 1000000000000 : ℝ)
  | 14 => (2178256933 / 125000000000 : ℝ)
  | 15 => (17237708509 / 1000000000000 : ℝ)
  | 16 => (8522500163 / 500000000000 : ℝ)
  | 17 => (16847882441 / 1000000000000 : ℝ)
  | 18 => (16646305997 / 1000000000000 : ℝ)
  | 19 => (51375693 / 3125000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch066Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (19759738641 / 1000000000000 : ℝ)
  | 1 => (19631244667 / 1000000000000 : ℝ)
  | 2 => (9749536253 / 500000000000 : ℝ)
  | 3 => (4840794779 / 250000000000 : ℝ)
  | 4 => (1922352111 / 100000000000 : ℝ)
  | 5 => (76320219 / 4000000000 : ℝ)
  | 6 => (4733183987 / 250000000000 : ℝ)
  | 7 => (939076013 / 50000000000 : ℝ)
  | 8 => (1862636289 / 100000000000 : ℝ)
  | 9 => (9233609341 / 500000000000 : ℝ)
  | 10 => (18304042119 / 1000000000000 : ℝ)
  | 11 => (4534196831 / 250000000000 : ℝ)
  | 12 => (3593081611 / 200000000000 : ℝ)
  | 13 => (8894928851 / 500000000000 : ℝ)
  | 14 => (2201261161 / 125000000000 : ℝ)
  | 15 => (3485211093 / 200000000000 : ℝ)
  | 16 => (1723770851 / 100000000000 : ℝ)
  | 17 => (17045000327 / 1000000000000 : ℝ)
  | 18 => (8423941221 / 500000000000 : ℝ)
  | 19 => (8323152999 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch066Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1320 : ℝ) + (j.val : ℝ)) / 1600)
      (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch066Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch066Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1320 : ℝ) + (j.val : ℝ)) / 1600)
    (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch066Neg45WeightLower j.val) (hpThetaShiftTwoBatch066Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch066Neg45WeightLower, hpThetaShiftTwoBatch066Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch066Neg45_integral_bounds :
    (43874993 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (45445923 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch066Lower hpThetaJensenCellsBatch066Upper
    hpThetaShiftTwoBatch066Neg45WeightLower hpThetaShiftTwoBatch066Neg45WeightUpper hpThetaJensenCellsBatch066_bounds hpThetaShiftTwoBatch066Neg45_weight_bounds
  have hl : (43874993 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch066Lower j * hpThetaShiftTwoBatch066Neg45WeightLower j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftTwoBatch066Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftTwoBatch066Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch066Lower j * hpThetaShiftTwoBatch066Neg45WeightUpper j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftTwoBatch066Neg45WeightUpper j) / 1600) ≤ (45445923 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftTwoBatch066Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1320 : ℝ) / 1600 = 66 / 80 by norm_num,
    show ((1320 : ℝ) + 20) / 1600 = (66 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch066Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (5581199859 / 1000000000000 : ℝ)
  | 1 => (1420652329 / 250000000000 : ℝ)
  | 2 => (2892346323 / 500000000000 : ℝ)
  | 3 => (5887451309 / 1000000000000 : ℝ)
  | 4 => (23963547 / 4000000000 : ℝ)
  | 5 => (6095000399 / 1000000000000 : ℝ)
  | 6 => (3099896833 / 500000000000 : ℝ)
  | 7 => (6305267947 / 1000000000000 : ℝ)
  | 8 => (6411424619 / 1000000000000 : ℝ)
  | 9 => (6518265043 / 1000000000000 : ℝ)
  | 10 => (6625790563 / 1000000000000 : ℝ)
  | 11 => (6734002503 / 1000000000000 : ℝ)
  | 12 => (6842902171 / 1000000000000 : ℝ)
  | 13 => (869061357 / 125000000000 : ℝ)
  | 14 => (706276983 / 100000000000 : ℝ)
  | 15 => (1434748069 / 200000000000 : ℝ)
  | 16 => (1457080727 / 200000000000 : ℝ)
  | 17 => (3698880457 / 500000000000 : ℝ)
  | 18 => (7510813377 / 1000000000000 : ℝ)
  | 19 => (3812281101 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch066Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (5682609317 / 1000000000000 : ℝ)
  | 1 => (5784692647 / 1000000000000 : ℝ)
  | 2 => (588745131 / 100000000000 : ℝ)
  | 3 => (5990886751 / 1000000000000 : ℝ)
  | 4 => (15237501 / 2500000000 : ℝ)
  | 5 => (6199793667 / 1000000000000 : ℝ)
  | 6 => (1576316987 / 250000000000 : ℝ)
  | 7 => (320571231 / 50000000000 : ℝ)
  | 8 => (1629566261 / 250000000000 : ℝ)
  | 9 => (1656447641 / 250000000000 : ℝ)
  | 10 => (841750313 / 125000000000 : ℝ)
  | 11 => (1710725543 / 250000000000 : ℝ)
  | 12 => (6952490857 / 1000000000000 : ℝ)
  | 13 => (7062769831 / 1000000000000 : ℝ)
  | 14 => (3586870173 / 500000000000 : ℝ)
  | 15 => (1821350909 / 250000000000 : ℝ)
  | 16 => (1479552183 / 200000000000 : ℝ)
  | 17 => (3755406689 / 500000000000 : ℝ)
  | 18 => (7624562203 / 1000000000000 : ℝ)
  | 19 => (241844017 / 31250000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch066Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1320 : ℝ) + (j.val : ℝ)) / 1600)
      (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch066Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch066Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1320 : ℝ) + (j.val : ℝ)) / 1600)
    (((1320 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch066Neg25WeightLower j.val) (hpThetaShiftTwoBatch066Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch066Neg25WeightLower, hpThetaShiftTwoBatch066Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch066Neg25_integral_bounds :
    (626941 / 40000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (66 / 80 : ℝ) ((66 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (16356117 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1320 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch066Lower hpThetaJensenCellsBatch066Upper
    hpThetaShiftTwoBatch066Neg25WeightLower hpThetaShiftTwoBatch066Neg25WeightUpper hpThetaJensenCellsBatch066_bounds hpThetaShiftTwoBatch066Neg25_weight_bounds
  have hl : (626941 / 40000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch066Lower j * hpThetaShiftTwoBatch066Neg25WeightLower j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftTwoBatch066Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftTwoBatch066Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch066Lower j * hpThetaShiftTwoBatch066Neg25WeightUpper j)
        (hpThetaJensenCellsBatch066Upper j * hpThetaShiftTwoBatch066Neg25WeightUpper j) / 1600) ≤ (16356117 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch066Lower, hpThetaJensenCellsBatch066Upper,
      hpThetaShiftTwoBatch066Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1320 : ℝ) / 1600 = 66 / 80 by norm_num,
    show ((1320 : ℝ) + 20) / 1600 = (66 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch066Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch066Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch066Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch066Neg25_integral_bounds
end HodgeProofHP
