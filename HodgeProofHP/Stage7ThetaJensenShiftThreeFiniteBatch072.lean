/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch072

/-! Exact signed weight and batch integral certificates, batch 72 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch072Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-953798971 / 6250000000 : ℝ)
  | 1 => (-15417316629 / 100000000000 : ℝ)
  | 2 => (-77876373513 / 500000000000 : ℝ)
  | 3 => (-157346692309 / 1000000000000 : ℝ)
  | 4 => (-158955117691 / 1000000000000 : ℝ)
  | 5 => (-160578139543 / 1000000000000 : ℝ)
  | 6 => (-162215875057 / 1000000000000 : ℝ)
  | 7 => (-163868442253 / 1000000000000 : ℝ)
  | 8 => (-8276797999 / 50000000000 : ℝ)
  | 9 => (-20902318491 / 125000000000 : ℝ)
  | 10 => (-168916326629 / 1000000000000 : ℝ)
  | 11 => (-170629417459 / 1000000000000 : ℝ)
  | 12 => (-43089485663 / 250000000000 : ℝ)
  | 13 => (-34820405059 / 200000000000 : ℝ)
  | 14 => (-87930894671 / 500000000000 : ℝ)
  | 15 => (-177637359613 / 1000000000000 : ℝ)
  | 16 => (-179428861803 / 1000000000000 : ℝ)
  | 17 => (-90618211243 / 500000000000 : ℝ)
  | 18 => (-1144126057 / 6250000000 : ℝ)
  | 19 => (-184900230053 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch072Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1510566403 / 10000000000 : ℝ)
  | 1 => (-152607835359 / 1000000000000 : ℝ)
  | 2 => (-154173166289 / 1000000000000 : ℝ)
  | 3 => (-6230109881 / 40000000000 : ℝ)
  | 4 => (-39336673077 / 250000000000 : ℝ)
  | 5 => (-15895511769 / 100000000000 : ℝ)
  | 6 => (-80289069771 / 500000000000 : ℝ)
  | 7 => (-10138492191 / 62500000000 : ℝ)
  | 8 => (-40967110563 / 250000000000 : ℝ)
  | 9 => (-165535959979 / 1000000000000 : ℝ)
  | 10 => (-167218547927 / 1000000000000 : ℝ)
  | 11 => (-42229081657 / 250000000000 : ℝ)
  | 12 => (-85314708729 / 500000000000 : ℝ)
  | 13 => (-172357942651 / 1000000000000 : ℝ)
  | 14 => (-87051012647 / 500000000000 : ℝ)
  | 15 => (-175861789341 / 1000000000000 : ℝ)
  | 16 => (-44409339903 / 250000000000 : ℝ)
  | 17 => (-89714430901 / 500000000000 : ℝ)
  | 18 => (-36247284497 / 200000000000 : ℝ)
  | 19 => (-183060169119 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch072Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1440 : ℝ) + (j.val : ℝ)) / 1600)
      (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch072Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch072Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1440 : ℝ) + (j.val : ℝ)) / 1600)
    (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch072Neg100WeightLower j.val) (hpThetaShiftThreeBatch072Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch072Neg100WeightLower, hpThetaShiftThreeBatch072Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch072Neg100_integral_bounds :
    (-40308977 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-3873939 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch072Lower hpThetaJensenCellsBatch072Upper
    hpThetaShiftThreeBatch072Neg100WeightLower hpThetaShiftThreeBatch072Neg100WeightUpper hpThetaJensenCellsBatch072_bounds hpThetaShiftThreeBatch072Neg100_weight_bounds
  have hl : (-40308977 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch072Lower j * hpThetaShiftThreeBatch072Neg100WeightLower j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftThreeBatch072Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftThreeBatch072Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch072Lower j * hpThetaShiftThreeBatch072Neg100WeightUpper j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftThreeBatch072Neg100WeightUpper j) / 1600) ≤ (-3873939 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftThreeBatch072Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1440 : ℝ) / 1600 = 72 / 80 by norm_num,
    show ((1440 : ℝ) + 20) / 1600 = (72 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch072Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-25814653981 / 1000000000000 : ℝ)
  | 1 => (-3267063209 / 125000000000 : ℝ)
  | 2 => (-5292343679 / 200000000000 : ℝ)
  | 3 => (-26790322091 / 1000000000000 : ℝ)
  | 4 => (-6780586733 / 250000000000 : ℝ)
  | 5 => (-686445583 / 25000000000 : ℝ)
  | 6 => (-27796781889 / 1000000000000 : ℝ)
  | 7 => (-28139253503 / 1000000000000 : ℝ)
  | 8 => (-14242634633 / 500000000000 : ℝ)
  | 9 => (-5766972103 / 200000000000 : ℝ)
  | 10 => (-3648507353 / 125000000000 : ℝ)
  | 11 => (-29544896009 / 1000000000000 : ℝ)
  | 12 => (-14952702063 / 500000000000 : ℝ)
  | 13 => (-30269615473 / 1000000000000 : ℝ)
  | 14 => (-30637562591 / 1000000000000 : ℝ)
  | 15 => (-31009278269 / 1000000000000 : ℝ)
  | 16 => (-15692397771 / 500000000000 : ℝ)
  | 17 => (-15882073847 / 500000000000 : ℝ)
  | 18 => (-16073684129 / 500000000000 : ℝ)
  | 19 => (-16267245511 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch072Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6374033401 / 250000000000 : ℝ)
  | 1 => (-1290732699 / 50000000000 : ℝ)
  | 2 => (-26136505671 / 1000000000000 : ℝ)
  | 3 => (-13230859197 / 500000000000 : ℝ)
  | 4 => (-2679032209 / 100000000000 : ℝ)
  | 5 => (-27122346931 / 1000000000000 : ℝ)
  | 6 => (-27457823319 / 1000000000000 : ℝ)
  | 7 => (-434324717 / 15625000000 : ℝ)
  | 8 => (-14069626751 / 500000000000 : ℝ)
  | 9 => (-5697053853 / 200000000000 : ℝ)
  | 10 => (-14417430257 / 500000000000 : ℝ)
  | 11 => (-29188058823 / 1000000000000 : ℝ)
  | 12 => (-3693112001 / 125000000000 : ℝ)
  | 13 => (-239243233 / 8000000000 : ℝ)
  | 14 => (-1891850967 / 62500000000 : ℝ)
  | 15 => (-3063756259 / 100000000000 : ℝ)
  | 16 => (-7752319567 / 250000000000 : ℝ)
  | 17 => (-31384795541 / 1000000000000 : ℝ)
  | 18 => (-31764147693 / 1000000000000 : ℝ)
  | 19 => (-32147368257 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch072Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1440 : ℝ) + (j.val : ℝ)) / 1600)
      (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch072Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch072Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1440 : ℝ) + (j.val : ℝ)) / 1600)
    (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch072Neg70WeightLower j.val) (hpThetaShiftThreeBatch072Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch072Neg70WeightLower, hpThetaShiftThreeBatch072Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch072Neg70_integral_bounds :
    (-6951849 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-208351 / 31250000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch072Lower hpThetaJensenCellsBatch072Upper
    hpThetaShiftThreeBatch072Neg70WeightLower hpThetaShiftThreeBatch072Neg70WeightUpper hpThetaJensenCellsBatch072_bounds hpThetaShiftThreeBatch072Neg70_weight_bounds
  have hl : (-6951849 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch072Lower j * hpThetaShiftThreeBatch072Neg70WeightLower j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftThreeBatch072Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftThreeBatch072Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch072Lower j * hpThetaShiftThreeBatch072Neg70WeightUpper j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftThreeBatch072Neg70WeightUpper j) / 1600) ≤ (-208351 / 31250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftThreeBatch072Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1440 : ℝ) / 1600 = 72 / 80 by norm_num,
    show ((1440 : ℝ) + 20) / 1600 = (72 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch072Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (594855489 / 500000000000 : ℝ)
  | 1 => (1179609761 / 1000000000000 : ℝ)
  | 2 => (1169208157 / 1000000000000 : ℝ)
  | 3 => (4525399 / 3906250000 : ℝ)
  | 4 => (1147487663 / 1000000000000 : ℝ)
  | 5 => (568080307 / 500000000000 : ℝ)
  | 6 => (1124516859 / 1000000000000 : ℝ)
  | 7 => (556276109 / 500000000000 : ℝ)
  | 8 => (44010499 / 40000000000 : ℝ)
  | 9 => (1087643371 / 1000000000000 : ℝ)
  | 10 => (537345303 / 500000000000 : ℝ)
  | 11 => (6633749 / 6250000000 : ℝ)
  | 12 => (1047766693 / 1000000000000 : ℝ)
  | 13 => (1033786741 / 1000000000000 : ℝ)
  | 14 => (6371597 / 6250000000 : ℝ)
  | 15 => (502384261 / 500000000000 : ℝ)
  | 16 => (2474303 / 2500000000 : ℝ)
  | 17 => (974308961 / 1000000000000 : ℝ)
  | 18 => (95852717 / 100000000000 : ℝ)
  | 19 => (235592787 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch072Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1199515791 / 1000000000000 : ℝ)
  | 1 => (1189710979 / 1000000000000 : ℝ)
  | 2 => (589804881 / 500000000000 : ℝ)
  | 3 => (584604079 / 500000000000 : ℝ)
  | 4 => (231700429 / 200000000000 : ℝ)
  | 5 => (71717979 / 62500000000 : ℝ)
  | 6 => (227232123 / 200000000000 : ℝ)
  | 7 => (56225843 / 50000000000 : ℝ)
  | 8 => (1112552219 / 1000000000000 : ℝ)
  | 9 => (275065619 / 250000000000 : ℝ)
  | 10 => (271910843 / 250000000000 : ℝ)
  | 11 => (1074690607 / 1000000000000 : ℝ)
  | 12 => (1061399841 / 1000000000000 : ℝ)
  | 13 => (523883347 / 500000000000 : ℝ)
  | 14 => (516893371 / 500000000000 : ℝ)
  | 15 => (1019455521 / 1000000000000 : ℝ)
  | 16 => (1004768523 / 1000000000000 : ℝ)
  | 17 => (989721201 / 1000000000000 : ℝ)
  | 18 => (487154481 / 500000000000 : ℝ)
  | 19 => (958527171 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch072Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1440 : ℝ) + (j.val : ℝ)) / 1600)
      (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch072Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch072Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1440 : ℝ) + (j.val : ℝ)) / 1600)
    (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch072Neg45WeightLower j.val) (hpThetaShiftThreeBatch072Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch072Neg45WeightLower, hpThetaShiftThreeBatch072Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch072Neg45_integral_bounds :
    (253981 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (66163 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch072Lower hpThetaJensenCellsBatch072Upper
    hpThetaShiftThreeBatch072Neg45WeightLower hpThetaShiftThreeBatch072Neg45WeightUpper hpThetaJensenCellsBatch072_bounds hpThetaShiftThreeBatch072Neg45_weight_bounds
  have hl : (253981 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch072Lower j * hpThetaShiftThreeBatch072Neg45WeightLower j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftThreeBatch072Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftThreeBatch072Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch072Lower j * hpThetaShiftThreeBatch072Neg45WeightUpper j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftThreeBatch072Neg45WeightUpper j) / 1600) ≤ (66163 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftThreeBatch072Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1440 : ℝ) / 1600 = 72 / 80 by norm_num,
    show ((1440 : ℝ) + 20) / 1600 = (72 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch072Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (19759637 / 100000000000 : ℝ)
  | 1 => (204175173 / 1000000000000 : ℝ)
  | 2 => (210815447 / 1000000000000 : ℝ)
  | 3 => (21751749 / 100000000000 : ℝ)
  | 4 => (224281597 / 1000000000000 : ℝ)
  | 5 => (7222127 / 31250000000 : ℝ)
  | 6 => (118998593 / 500000000000 : ℝ)
  | 7 => (244949259 / 1000000000000 : ℝ)
  | 8 => (125982289 / 500000000000 : ℝ)
  | 9 => (129521719 / 500000000000 : ℝ)
  | 10 => (66546533 / 250000000000 : ℝ)
  | 11 => (68348239 / 250000000000 : ℝ)
  | 12 => (70166051 / 250000000000 : ℝ)
  | 13 => (288000169 / 1000000000000 : ℝ)
  | 14 => (36925143 / 125000000000 : ℝ)
  | 15 => (151433711 / 500000000000 : ℝ)
  | 16 => (310399297 / 1000000000000 : ℝ)
  | 17 => (15899853 / 50000000000 : ℝ)
  | 18 => (325661003 / 1000000000000 : ℝ)
  | 19 => (166695709 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch072Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (102087587 / 500000000000 : ℝ)
  | 1 => (26351931 / 125000000000 : ℝ)
  | 2 => (217517491 / 1000000000000 : ℝ)
  | 3 => (112140799 / 500000000000 : ℝ)
  | 4 => (46221613 / 200000000000 : ℝ)
  | 5 => (237997187 / 1000000000000 : ℝ)
  | 6 => (12247463 / 50000000000 : ℝ)
  | 7 => (251964579 / 1000000000000 : ℝ)
  | 8 => (259043439 / 1000000000000 : ℝ)
  | 9 => (266186133 / 1000000000000 : ℝ)
  | 10 => (273392957 / 1000000000000 : ℝ)
  | 11 => (56132841 / 200000000000 : ℝ)
  | 12 => (28800017 / 100000000000 : ℝ)
  | 13 => (59080229 / 200000000000 : ℝ)
  | 14 => (302867423 / 1000000000000 : ℝ)
  | 15 => (155199649 / 500000000000 : ℝ)
  | 16 => (317997061 / 1000000000000 : ℝ)
  | 17 => (81415251 / 250000000000 : ℝ)
  | 18 => (333391419 / 1000000000000 : ℝ)
  | 19 => (85297149 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch072Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1440 : ℝ) + (j.val : ℝ)) / 1600)
      (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch072Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch072Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1440 : ℝ) + (j.val : ℝ)) / 1600)
    (((1440 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch072Neg25WeightLower j.val) (hpThetaShiftThreeBatch072Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch072Neg25WeightLower, hpThetaShiftThreeBatch072Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch072Neg25_integral_bounds :
    (30283 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (72 / 80 : ℝ) ((72 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (64109 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1440 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch072Lower hpThetaJensenCellsBatch072Upper
    hpThetaShiftThreeBatch072Neg25WeightLower hpThetaShiftThreeBatch072Neg25WeightUpper hpThetaJensenCellsBatch072_bounds hpThetaShiftThreeBatch072Neg25_weight_bounds
  have hl : (30283 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch072Lower j * hpThetaShiftThreeBatch072Neg25WeightLower j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftThreeBatch072Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftThreeBatch072Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch072Lower j * hpThetaShiftThreeBatch072Neg25WeightUpper j)
        (hpThetaJensenCellsBatch072Upper j * hpThetaShiftThreeBatch072Neg25WeightUpper j) / 1600) ≤ (64109 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch072Lower, hpThetaJensenCellsBatch072Upper,
      hpThetaShiftThreeBatch072Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1440 : ℝ) / 1600 = 72 / 80 by norm_num,
    show ((1440 : ℝ) + 20) / 1600 = (72 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch072Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch072Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch072Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch072Neg25_integral_bounds
end HodgeProofHP
