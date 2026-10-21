/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch069

/-! Exact signed weight and batch integral certificates, batch 69 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch069Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-20218312393 / 250000000000 : ℝ)
  | 1 => (-40882822981 / 500000000000 : ℝ)
  | 2 => (-16533343873 / 200000000000 : ℝ)
  | 3 => (-41788272011 / 500000000000 : ℝ)
  | 4 => (-84495194729 / 1000000000000 : ℝ)
  | 5 => (-17084549369 / 200000000000 : ℝ)
  | 6 => (-337340923 / 3906250000 : ℝ)
  | 7 => (-21826214887 / 250000000000 : ℝ)
  | 8 => (-1103244671 / 12500000000 : ℝ)
  | 9 => (-89223496319 / 1000000000000 : ℝ)
  | 10 => (-45098352837 / 500000000000 : ℝ)
  | 11 => (-45589640269 / 500000000000 : ℝ)
  | 12 => (-92171300289 / 1000000000000 : ℝ)
  | 13 => (-93172844893 / 1000000000000 : ℝ)
  | 14 => (-2943249841 / 31250000000 : ℝ)
  | 15 => (-47602415751 / 500000000000 : ℝ)
  | 16 => (-48117718211 / 500000000000 : ℝ)
  | 17 => (-19455178407 / 200000000000 : ℝ)
  | 18 => (-3072696291 / 31250000000 : ℝ)
  | 19 => (-99386687837 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch069Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-9998682063 / 125000000000 : ℝ)
  | 1 => (-80873249571 / 1000000000000 : ℝ)
  | 2 => (-81765645961 / 1000000000000 : ℝ)
  | 3 => (-20666679841 / 250000000000 : ℝ)
  | 4 => (-83576544021 / 1000000000000 : ℝ)
  | 5 => (-10561899341 / 125000000000 : ℝ)
  | 6 => (-21355686711 / 250000000000 : ℝ)
  | 7 => (-86359276287 / 1000000000000 : ℝ)
  | 8 => (-87304859547 / 1000000000000 : ℝ)
  | 9 => (-88259573679 / 1000000000000 : ℝ)
  | 10 => (-44611748159 / 500000000000 : ℝ)
  | 11 => (-90196705673 / 1000000000000 : ℝ)
  | 12 => (-91179280537 / 1000000000000 : ℝ)
  | 13 => (-1440176567 / 15625000000 : ℝ)
  | 14 => (-23293211223 / 250000000000 : ℝ)
  | 15 => (-94183994911 / 1000000000000 : ℝ)
  | 16 => (-95204831501 / 1000000000000 : ℝ)
  | 17 => (-96235436421 / 1000000000000 : ℝ)
  | 18 => (-48637946017 / 500000000000 : ℝ)
  | 19 => (-98326281311 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch069Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1380 : ℝ) + (j.val : ℝ)) / 1600)
      (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch069Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch069Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1380 : ℝ) + (j.val : ℝ)) / 1600)
    (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch069Neg100WeightLower j.val) (hpThetaShiftThreeBatch069Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch069Neg100WeightLower, hpThetaShiftThreeBatch069Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch069Neg100_integral_bounds :
    (-72406929 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-69655823 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch069Lower hpThetaJensenCellsBatch069Upper
    hpThetaShiftThreeBatch069Neg100WeightLower hpThetaShiftThreeBatch069Neg100WeightUpper hpThetaJensenCellsBatch069_bounds hpThetaShiftThreeBatch069Neg100_weight_bounds
  have hl : (-72406929 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch069Lower j * hpThetaShiftThreeBatch069Neg100WeightLower j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftThreeBatch069Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftThreeBatch069Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch069Lower j * hpThetaShiftThreeBatch069Neg100WeightUpper j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftThreeBatch069Neg100WeightUpper j) / 1600) ≤ (-69655823 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftThreeBatch069Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1380 : ℝ) / 1600 = 69 / 80 by norm_num,
    show ((1380 : ℝ) + 20) / 1600 = (69 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch069Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-11647316491 / 1000000000000 : ℝ)
  | 1 => (-738405049 / 62500000000 : ℝ)
  | 2 => (-5991788133 / 500000000000 : ℝ)
  | 3 => (-12154621599 / 1000000000000 : ℝ)
  | 4 => (-12327635599 / 1000000000000 : ℝ)
  | 5 => (-12502637233 / 1000000000000 : ℝ)
  | 6 => (-20287433 / 1600000000 : ℝ)
  | 7 => (-6429340027 / 500000000000 : ℝ)
  | 8 => (-6519879979 / 500000000000 : ℝ)
  | 9 => (-3305726233 / 250000000000 : ℝ)
  | 10 => (-13408134729 / 1000000000000 : ℝ)
  | 11 => (-6797734633 / 500000000000 : ℝ)
  | 12 => (-13784928617 / 1000000000000 : ℝ)
  | 13 => (-6988266511 / 500000000000 : ℝ)
  | 14 => (-2834060577 / 200000000000 : ℝ)
  | 15 => (-14366258771 / 1000000000000 : ℝ)
  | 16 => (-1820552677 / 125000000000 : ℝ)
  | 17 => (-369120293 / 25000000000 : ℝ)
  | 18 => (-116933209 / 7812500000 : ℝ)
  | 19 => (-15172359751 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch069Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2870516219 / 250000000000 : ℝ)
  | 1 => (-1164731649 / 100000000000 : ℝ)
  | 2 => (-11814480783 / 1000000000000 : ℝ)
  | 3 => (-2396715253 / 200000000000 : ℝ)
  | 4 => (-6077310799 / 500000000000 : ℝ)
  | 5 => (-6163817799 / 500000000000 : ℝ)
  | 6 => (-781414827 / 62500000000 : ℝ)
  | 7 => (-1584955703 / 125000000000 : ℝ)
  | 8 => (-12858680053 / 1000000000000 : ℝ)
  | 9 => (-13039759957 / 1000000000000 : ℝ)
  | 10 => (-13222904931 / 1000000000000 : ℝ)
  | 11 => (-1676016841 / 125000000000 : ℝ)
  | 12 => (-2719093853 / 200000000000 : ℝ)
  | 13 => (-1723116077 / 125000000000 : ℝ)
  | 14 => (-13976533021 / 1000000000000 : ℝ)
  | 15 => (-3542575721 / 250000000000 : ℝ)
  | 16 => (-1436625877 / 100000000000 : ℝ)
  | 17 => (-2912884283 / 200000000000 : ℝ)
  | 18 => (-14764811719 / 1000000000000 : ℝ)
  | 19 => (-14967450751 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch069Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1380 : ℝ) + (j.val : ℝ)) / 1600)
      (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch069Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch069Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1380 : ℝ) + (j.val : ℝ)) / 1600)
    (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch069Neg70WeightLower j.val) (hpThetaShiftThreeBatch069Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch069Neg70WeightLower, hpThetaShiftThreeBatch069Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch069Neg70_integral_bounds :
    (-5367751 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-5147903 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch069Lower hpThetaJensenCellsBatch069Upper
    hpThetaShiftThreeBatch069Neg70WeightLower hpThetaShiftThreeBatch069Neg70WeightUpper hpThetaJensenCellsBatch069_bounds hpThetaShiftThreeBatch069Neg70_weight_bounds
  have hl : (-5367751 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch069Lower j * hpThetaShiftThreeBatch069Neg70WeightLower j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftThreeBatch069Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftThreeBatch069Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch069Lower j * hpThetaShiftThreeBatch069Neg70WeightUpper j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftThreeBatch069Neg70WeightUpper j) / 1600) ≤ (-5147903 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftThreeBatch069Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1380 : ℝ) / 1600 = 69 / 80 by norm_num,
    show ((1380 : ℝ) + 20) / 1600 = (69 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch069Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1375171027 / 1000000000000 : ℝ)
  | 1 => (688578299 / 500000000000 : ℝ)
  | 2 => (27580487 / 20000000000 : ℝ)
  | 3 => (276154427 / 200000000000 : ℝ)
  | 4 => (691198893 / 500000000000 : ℝ)
  | 5 => (691949553 / 500000000000 : ℝ)
  | 6 => (1385273879 / 1000000000000 : ℝ)
  | 7 => (693259931 / 500000000000 : ℝ)
  | 8 => (693817393 / 500000000000 : ℝ)
  | 9 => (34715409 / 25000000000 : ℝ)
  | 10 => (1389462267 / 1000000000000 : ℝ)
  | 11 => (1390170163 / 1000000000000 : ℝ)
  | 12 => (1390737679 / 1000000000000 : ℝ)
  | 13 => (1391162423 / 1000000000000 : ℝ)
  | 14 => (695720987 / 500000000000 : ℝ)
  | 15 => (695777843 / 500000000000 : ℝ)
  | 16 => (11131079 / 8000000000 : ℝ)
  | 17 => (1391058927 / 1000000000000 : ℝ)
  | 18 => (173821911 / 125000000000 : ℝ)
  | 19 => (69496569 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch069Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1377156599 / 1000000000000 : ℝ)
  | 1 => (1379024351 / 1000000000000 : ℝ)
  | 2 => (172596517 / 125000000000 : ℝ)
  | 3 => (1382397787 / 1000000000000 : ℝ)
  | 4 => (1383899107 / 1000000000000 : ℝ)
  | 5 => (34631847 / 25000000000 : ℝ)
  | 6 => (1386519863 / 1000000000000 : ℝ)
  | 7 => (1387634787 / 1000000000000 : ℝ)
  | 8 => (1388616361 / 1000000000000 : ℝ)
  | 9 => (347365567 / 250000000000 : ℝ)
  | 10 => (347542541 / 250000000000 : ℝ)
  | 11 => (17384221 / 12500000000 : ℝ)
  | 12 => (173895303 / 125000000000 : ℝ)
  | 13 => (55657679 / 40000000000 : ℝ)
  | 14 => (1391573887 / 1000000000000 : ℝ)
  | 15 => (1391586359 / 1000000000000 : ℝ)
  | 16 => (1391555687 / 1000000000000 : ℝ)
  | 17 => (347846219 / 250000000000 : ℝ)
  | 18 => (86941183 / 62500000000 : ℝ)
  | 19 => (1390575289 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch069Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1380 : ℝ) + (j.val : ℝ)) / 1600)
      (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch069Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch069Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1380 : ℝ) + (j.val : ℝ)) / 1600)
    (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch069Neg45WeightLower j.val) (hpThetaShiftThreeBatch069Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch069Neg45WeightLower, hpThetaShiftThreeBatch069Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch069Neg45_integral_bounds :
    (218761 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (562749 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch069Lower hpThetaJensenCellsBatch069Upper
    hpThetaShiftThreeBatch069Neg45WeightLower hpThetaShiftThreeBatch069Neg45WeightUpper hpThetaJensenCellsBatch069_bounds hpThetaShiftThreeBatch069Neg45_weight_bounds
  have hl : (218761 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch069Lower j * hpThetaShiftThreeBatch069Neg45WeightLower j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftThreeBatch069Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftThreeBatch069Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch069Lower j * hpThetaShiftThreeBatch069Neg45WeightUpper j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftThreeBatch069Neg45WeightUpper j) / 1600) ≤ (562749 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftThreeBatch069Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1380 : ℝ) / 1600 = 69 / 80 by norm_num,
    show ((1380 : ℝ) + 20) / 1600 = (69 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch069Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-95810883 / 1000000000000 : ℝ)
  | 1 => (-11547703 / 125000000000 : ℝ)
  | 2 => (-22227099 / 250000000000 : ℝ)
  | 3 => (-85390917 / 1000000000000 : ℝ)
  | 4 => (-40914453 / 500000000000 : ℝ)
  | 5 => (-78222083 / 1000000000000 : ℝ)
  | 6 => (-37285083 / 500000000000 : ℝ)
  | 7 => (-70872871 / 1000000000000 : ℝ)
  | 8 => (-13425983 / 200000000000 : ℝ)
  | 9 => (-12668203 / 200000000000 : ℝ)
  | 10 => (-59505887 / 1000000000000 : ℝ)
  | 11 => (-27812123 / 500000000000 : ℝ)
  | 12 => (-25847903 / 500000000000 : ℝ)
  | 13 => (-23860141 / 500000000000 : ℝ)
  | 14 => (-10924347 / 250000000000 : ℝ)
  | 15 => (-9906709 / 250000000000 : ℝ)
  | 16 => (-1775417 / 50000000000 : ℝ)
  | 17 => (-7835403 / 250000000000 : ℝ)
  | 18 => (-6781591 / 250000000000 : ℝ)
  | 19 => (-22862307 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch069Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-92381623 / 1000000000000 : ℝ)
  | 1 => (-17781679 / 200000000000 : ℝ)
  | 2 => (-21347729 / 250000000000 : ℝ)
  | 3 => (-16365781 / 200000000000 : ℝ)
  | 4 => (-39111041 / 500000000000 : ℝ)
  | 5 => (-14914033 / 200000000000 : ℝ)
  | 6 => (-7087287 / 100000000000 : ℝ)
  | 7 => (-33564957 / 500000000000 : ℝ)
  | 8 => (-31670507 / 500000000000 : ℝ)
  | 9 => (-29752943 / 500000000000 : ℝ)
  | 10 => (-11124849 / 200000000000 : ℝ)
  | 11 => (-10339161 / 200000000000 : ℝ)
  | 12 => (-47720281 / 1000000000000 : ℝ)
  | 13 => (-43697387 / 1000000000000 : ℝ)
  | 14 => (-7925367 / 200000000000 : ℝ)
  | 15 => (-35508339 / 1000000000000 : ℝ)
  | 16 => (-31341611 / 1000000000000 : ℝ)
  | 17 => (-27126363 / 1000000000000 : ℝ)
  | 18 => (-11431153 / 500000000000 : ℝ)
  | 19 => (-579661 / 31250000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch069Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1380 : ℝ) + (j.val : ℝ)) / 1600)
      (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch069Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch069Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1380 : ℝ) + (j.val : ℝ)) / 1600)
    (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch069Neg25WeightLower j.val) (hpThetaShiftThreeBatch069Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch069Neg25WeightLower, hpThetaShiftThreeBatch069Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch069Neg25_integral_bounds :
    (-10243 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-9357 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch069Lower hpThetaJensenCellsBatch069Upper
    hpThetaShiftThreeBatch069Neg25WeightLower hpThetaShiftThreeBatch069Neg25WeightUpper hpThetaJensenCellsBatch069_bounds hpThetaShiftThreeBatch069Neg25_weight_bounds
  have hl : (-10243 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch069Lower j * hpThetaShiftThreeBatch069Neg25WeightLower j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftThreeBatch069Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftThreeBatch069Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch069Lower j * hpThetaShiftThreeBatch069Neg25WeightUpper j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftThreeBatch069Neg25WeightUpper j) / 1600) ≤ (-9357 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftThreeBatch069Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1380 : ℝ) / 1600 = 69 / 80 by norm_num,
    show ((1380 : ℝ) + 20) / 1600 = (69 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch069Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch069Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch069Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch069Neg25_integral_bounds
end HodgeProofHP
