/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch073

/-! Exact signed weight and batch integral certificates, batch 73 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch073Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-19967629450563 / 125000000000 : ℝ)
  | 1 => (-160771046827571 / 1000000000000 : ℝ)
  | 2 => (-161806692005767 / 1000000000000 : ℝ)
  | 3 => (-162847996836013 / 1000000000000 : ℝ)
  | 4 => (-20486873388813 / 125000000000 : ℝ)
  | 5 => (-41236922179247 / 250000000000 : ℝ)
  | 6 => (-33201225527807 / 200000000000 : ℝ)
  | 7 => (-167070329956323 / 1000000000000 : ℝ)
  | 8 => (-168140321844911 / 1000000000000 : ℝ)
  | 9 => (-169216129577517 / 1000000000000 : ℝ)
  | 10 => (-85148889761901 / 500000000000 : ℝ)
  | 11 => (-42846324537661 / 250000000000 : ℝ)
  | 12 => (-172478712022423 / 1000000000000 : ℝ)
  | 13 => (-1735780478013 / 10000000000 : ℝ)
  | 14 => (-34936666449499 / 200000000000 : ℝ)
  | 15 => (-87897296109789 / 500000000000 : ℝ)
  | 16 => (-176911854674743 / 1000000000000 : ℝ)
  | 17 => (-22254393333637 / 125000000000 : ℝ)
  | 18 => (-179164495357937 / 1000000000000 : ℝ)
  | 19 => (-90149963998023 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch073Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-158716632734639 / 1000000000000 : ℝ)
  | 1 => (-159741035604503 / 1000000000000 : ℝ)
  | 2 => (-16077104682757 / 100000000000 : ℝ)
  | 3 => (-80903346002883 / 500000000000 : ℝ)
  | 4 => (-40711999209003 / 250000000000 : ℝ)
  | 5 => (-163894987110503 / 1000000000000 : ℝ)
  | 6 => (-164947688716987 / 1000000000000 : ℝ)
  | 7 => (-83003063819517 / 500000000000 : ℝ)
  | 8 => (-83535164978161 / 500000000000 : ℝ)
  | 9 => (-16814032184491 / 100000000000 : ℝ)
  | 10 => (-42304032394379 / 250000000000 : ℝ)
  | 11 => (-170297779523801 / 1000000000000 : ℝ)
  | 12 => (-171385298150643 / 1000000000000 : ℝ)
  | 13 => (-86239356011211 / 500000000000 : ℝ)
  | 14 => (-173578047801299 / 1000000000000 : ℝ)
  | 15 => (-87341666123747 / 500000000000 : ℝ)
  | 16 => (-175794592219577 / 1000000000000 : ℝ)
  | 17 => (-88455927337371 / 500000000000 : ℝ)
  | 18 => (-35607029333819 / 200000000000 : ℝ)
  | 19 => (-11197780959871 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch073Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1460 : ℝ) + (j.val : ℝ)) / 1600)
      (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch073Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch073Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1460 : ℝ) + (j.val : ℝ)) / 1600)
    (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch073Neg100WeightLower j.val) (hpThetaShiftOneBatch073Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch073Neg100WeightLower, hpThetaShiftOneBatch073Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch073Neg100_integral_bounds :
    (-1661016501 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-25621496441 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch073Lower hpThetaJensenCellsBatch073Upper
    hpThetaShiftOneBatch073Neg100WeightLower hpThetaShiftOneBatch073Neg100WeightUpper hpThetaJensenCellsBatch073_bounds hpThetaShiftOneBatch073Neg100_weight_bounds
  have hl : (-1661016501 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch073Lower j * hpThetaShiftOneBatch073Neg100WeightLower j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftOneBatch073Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftOneBatch073Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch073Lower j * hpThetaShiftOneBatch073Neg100WeightUpper j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftOneBatch073Neg100WeightUpper j) / 1600) ≤ (-25621496441 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftOneBatch073Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1460 : ℝ) / 1600 = 73 / 80 by norm_num,
    show ((1460 : ℝ) + 20) / 1600 = (73 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch073Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-14330477832737 / 500000000000 : ℝ)
  | 1 => (-14436565623751 / 500000000000 : ℝ)
  | 2 => (-14543294243167 / 500000000000 : ℝ)
  | 3 => (-29301333662099 / 1000000000000 : ℝ)
  | 4 => (-29517373079427 / 1000000000000 : ℝ)
  | 5 => (-14867356533761 / 500000000000 : ℝ)
  | 6 => (-29953359980239 / 1000000000000 : ℝ)
  | 7 => (-30173320196151 / 1000000000000 : ℝ)
  | 8 => (-30394600118631 / 1000000000000 : ℝ)
  | 9 => (-30617206175919 / 1000000000000 : ℝ)
  | 10 => (-15420572410601 / 500000000000 : ℝ)
  | 11 => (-6213284506537 / 200000000000 : ℝ)
  | 12 => (-7823261453417 / 250000000000 : ℝ)
  | 13 => (-15760510596309 / 500000000000 : ℝ)
  | 14 => (-31750355223247 / 1000000000000 : ℝ)
  | 15 => (-15990527242293 / 500000000000 : ℝ)
  | 16 => (-32213125581057 / 1000000000000 : ℝ)
  | 17 => (-8111643785639 / 250000000000 : ℝ)
  | 18 => (-16340704912261 / 500000000000 : ℝ)
  | 19 => (-16458818154007 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch073Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-28450055484547 / 1000000000000 : ℝ)
  | 1 => (-28660955665473 / 1000000000000 : ℝ)
  | 2 => (-28873131247501 / 1000000000000 : ℝ)
  | 3 => (-29086588486333 / 1000000000000 : ℝ)
  | 4 => (-14650666831049 / 500000000000 : ℝ)
  | 5 => (-14758686539713 / 500000000000 : ℝ)
  | 6 => (-29734713067521 / 1000000000000 : ℝ)
  | 7 => (-14976679990119 / 500000000000 : ℝ)
  | 8 => (-603466403923 / 20000000000 : ℝ)
  | 9 => (-3039460011863 / 100000000000 : ℝ)
  | 10 => (-15308603087959 / 500000000000 : ℝ)
  | 11 => (-30841144821201 / 1000000000000 : ℝ)
  | 12 => (-7766605633171 / 250000000000 : ℝ)
  | 13 => (-31293045813667 / 1000000000000 : ℝ)
  | 14 => (-31521021192617 / 1000000000000 : ℝ)
  | 15 => (-15875177611623 / 500000000000 : ℝ)
  | 16 => (-6396210896917 / 200000000000 : ℝ)
  | 17 => (-125832521801 / 3906250000 : ℝ)
  | 18 => (-6489315028511 / 200000000000 : ℝ)
  | 19 => (-32681409824521 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch073Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1460 : ℝ) + (j.val : ℝ)) / 1600)
      (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch073Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch073Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1460 : ℝ) + (j.val : ℝ)) / 1600)
    (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch073Neg65WeightLower j.val) (hpThetaShiftOneBatch073Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch073Neg65WeightLower, hpThetaShiftOneBatch073Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch073Neg65_integral_bounds :
    (-192333293 / 40000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-4631325979 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch073Lower hpThetaJensenCellsBatch073Upper
    hpThetaShiftOneBatch073Neg65WeightLower hpThetaShiftOneBatch073Neg65WeightUpper hpThetaJensenCellsBatch073_bounds hpThetaShiftOneBatch073Neg65_weight_bounds
  have hl : (-192333293 / 40000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch073Lower j * hpThetaShiftOneBatch073Neg65WeightLower j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftOneBatch073Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftOneBatch073Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch073Lower j * hpThetaShiftOneBatch073Neg65WeightUpper j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftOneBatch073Neg65WeightUpper j) / 1600) ≤ (-4631325979 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftOneBatch073Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1460 : ℝ) / 1600 = 73 / 80 by norm_num,
    show ((1460 : ℝ) + 20) / 1600 = (73 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch073Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1760940931893 / 1000000000000 : ℝ)
  | 1 => (-892550283551 / 500000000000 : ℝ)
  | 2 => (-90472860977 / 50000000000 : ℝ)
  | 3 => (-1834012041817 / 1000000000000 : ℝ)
  | 4 => (-1858766191567 / 1000000000000 : ℝ)
  | 5 => (-470930207867 / 250000000000 : ℝ)
  | 6 => (-381775425851 / 200000000000 : ℝ)
  | 7 => (-96711812887 / 50000000000 : ℝ)
  | 8 => (-1959799394823 / 1000000000000 : ℝ)
  | 9 => (-992783861757 / 500000000000 : ℝ)
  | 10 => (-251442803993 / 125000000000 : ℝ)
  | 11 => (-1018862356693 / 500000000000 : ℝ)
  | 12 => (-516028941567 / 250000000000 : ℝ)
  | 13 => (-2090716794193 / 1000000000000 : ℝ)
  | 14 => (-2117529005951 / 1000000000000 : ℝ)
  | 15 => (-1072276807769 / 500000000000 : ℝ)
  | 16 => (-86871673687 / 40000000000 : ℝ)
  | 17 => (-27490561379 / 12500000000 : ℝ)
  | 18 => (-2226914049687 / 1000000000000 : ℝ)
  | 19 => (-2254800495263 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch073Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-217122145789 / 125000000000 : ℝ)
  | 1 => (-440235232973 / 250000000000 : ℝ)
  | 2 => (-1785100567101 / 1000000000000 : ℝ)
  | 3 => (-1809457219539 / 1000000000000 : ℝ)
  | 4 => (-229251505227 / 125000000000 : ℝ)
  | 5 => (-929383095783 / 500000000000 : ℝ)
  | 6 => (-1883720831467 / 1000000000000 : ℝ)
  | 7 => (-954438564627 / 500000000000 : ℝ)
  | 8 => (-1934236257739 / 1000000000000 : ℝ)
  | 9 => (-979899697411 / 500000000000 : ℝ)
  | 10 => (-1985567723513 / 1000000000000 : ℝ)
  | 11 => (-2011542431943 / 1000000000000 : ℝ)
  | 12 => (-407544942677 / 200000000000 : ℝ)
  | 13 => (-2064115766267 / 1000000000000 : ℝ)
  | 14 => (-130669799637 / 62500000000 : ℝ)
  | 15 => (-42350580119 / 20000000000 : ℝ)
  | 16 => (-2144553615537 / 1000000000000 : ℝ)
  | 17 => (-1085895921087 / 500000000000 : ℝ)
  | 18 => (-2199244910319 / 1000000000000 : ℝ)
  | 19 => (-1113457024843 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch073Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1460 : ℝ) + (j.val : ℝ)) / 1600)
      (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch073Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch073Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1460 : ℝ) + (j.val : ℝ)) / 1600)
    (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch073Neg40WeightLower j.val) (hpThetaShiftOneBatch073Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch073Neg40WeightLower, hpThetaShiftOneBatch073Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch073Neg40_integral_bounds :
    (-38967983 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-298539303 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch073Lower hpThetaJensenCellsBatch073Upper
    hpThetaShiftOneBatch073Neg40WeightLower hpThetaShiftOneBatch073Neg40WeightUpper hpThetaJensenCellsBatch073_bounds hpThetaShiftOneBatch073Neg40_weight_bounds
  have hl : (-38967983 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch073Lower j * hpThetaShiftOneBatch073Neg40WeightLower j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftOneBatch073Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftOneBatch073Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch073Lower j * hpThetaShiftOneBatch073Neg40WeightUpper j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftOneBatch073Neg40WeightUpper j) / 1600) ≤ (-298539303 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftOneBatch073Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1460 : ℝ) / 1600 = 73 / 80 by norm_num,
    show ((1460 : ℝ) + 20) / 1600 = (73 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch073Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (54212455587 / 125000000000 : ℝ)
  | 1 => (435955474081 / 1000000000000 : ℝ)
  | 2 => (438213240407 / 1000000000000 : ℝ)
  | 3 => (88094578359 / 200000000000 : ℝ)
  | 4 => (221367187979 / 500000000000 : ℝ)
  | 5 => (108642002 / 244140625 : ℝ)
  | 6 => (447262631383 / 1000000000000 : ℝ)
  | 7 => (28095581 / 62500000 : ℝ)
  | 8 => (451797580093 / 1000000000000 : ℝ)
  | 9 => (227033714647 / 500000000000 : ℝ)
  | 10 => (91267757763 / 200000000000 : ℝ)
  | 11 => (91722320689 / 200000000000 : ℝ)
  | 12 => (230442908773 / 500000000000 : ℝ)
  | 13 => (231580687529 / 500000000000 : ℝ)
  | 14 => (465438219489 / 1000000000000 : ℝ)
  | 15 => (233858146961 / 500000000000 : ℝ)
  | 16 => (469995541003 / 1000000000000 : ℝ)
  | 17 => (9445518059 / 20000000000 : ℝ)
  | 18 => (59319665193 / 125000000000 : ℝ)
  | 19 => (29802483633 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch073Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (217977737041 / 500000000000 : ℝ)
  | 1 => (54776655051 / 125000000000 : ℝ)
  | 2 => (110118222949 / 250000000000 : ℝ)
  | 3 => (442734375959 / 1000000000000 : ℝ)
  | 4 => (444997640193 / 1000000000000 : ℝ)
  | 5 => (55907828923 / 125000000000 : ℝ)
  | 6 => (449529296001 / 1000000000000 : ℝ)
  | 7 => (225898790047 / 500000000000 : ℝ)
  | 8 => (90813485859 / 200000000000 : ℝ)
  | 9 => (28521174301 / 62500000000 : ℝ)
  | 10 => (229305801723 / 500000000000 : ℝ)
  | 11 => (460885817547 / 1000000000000 : ℝ)
  | 12 => (463161375059 / 1000000000000 : ℝ)
  | 13 => (46543821949 / 100000000000 : ℝ)
  | 14 => (467716293923 / 1000000000000 : ℝ)
  | 15 => (117498885251 / 250000000000 : ℝ)
  | 16 => (472275902951 / 1000000000000 : ℝ)
  | 17 => (94911464309 / 200000000000 : ℝ)
  | 18 => (476839738129 / 1000000000000 : ℝ)
  | 19 => (47912309361 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch073Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1460 : ℝ) + (j.val : ℝ)) / 1600)
      (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch073Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch073Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1460 : ℝ) + (j.val : ℝ)) / 1600)
    (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch073Neg20WeightLower j.val) (hpThetaShiftOneBatch073Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch073Neg20WeightLower, hpThetaShiftOneBatch073Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch073Neg20_integral_bounds :
    (1383539 / 20000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (14331061 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch073Lower hpThetaJensenCellsBatch073Upper
    hpThetaShiftOneBatch073Neg20WeightLower hpThetaShiftOneBatch073Neg20WeightUpper hpThetaJensenCellsBatch073_bounds hpThetaShiftOneBatch073Neg20_weight_bounds
  have hl : (1383539 / 20000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch073Lower j * hpThetaShiftOneBatch073Neg20WeightLower j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftOneBatch073Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftOneBatch073Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch073Lower j * hpThetaShiftOneBatch073Neg20WeightUpper j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftOneBatch073Neg20WeightUpper j) / 1600) ≤ (14331061 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftOneBatch073Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1460 : ℝ) / 1600 = 73 / 80 by norm_num,
    show ((1460 : ℝ) + 20) / 1600 = (73 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch073Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch073Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch073Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch073Neg20_integral_bounds
end HodgeProofHP
