/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch069

/-! Exact signed weight and batch integral certificates, batch 69 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch069Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3075415032473 / 1000000000000 : ℝ)
  | 1 => (-1551481974853 / 500000000000 : ℝ)
  | 2 => (-3130726853823 / 1000000000000 : ℝ)
  | 3 => (-98709536763 / 31250000000 : ℝ)
  | 4 => (-318690035723 / 100000000000 : ℝ)
  | 5 => (-1607656922101 / 500000000000 : ℝ)
  | 6 => (-3243947093501 / 1000000000000 : ℝ)
  | 7 => (-102275049049 / 31250000000 : ℝ)
  | 8 => (-3301878745153 / 1000000000000 : ℝ)
  | 9 => (-1665590050677 / 500000000000 : ℝ)
  | 10 => (-168035356383 / 50000000000 : ℝ)
  | 11 => (-847615330497 / 250000000000 : ℝ)
  | 12 => (-1710222095363 / 500000000000 : ℝ)
  | 13 => (-1725328624383 / 500000000000 : ℝ)
  | 14 => (-1740551009777 / 500000000000 : ℝ)
  | 15 => (-3511780035123 / 1000000000000 : ℝ)
  | 16 => (-3542692836137 / 1000000000000 : ℝ)
  | 17 => (-446730246491 / 125000000000 : ℝ)
  | 18 => (-112663406267 / 31250000000 : ℝ)
  | 19 => (-1818427744391 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch069Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3048078678647 / 1000000000000 : ℝ)
  | 1 => (-384426879059 / 125000000000 : ℝ)
  | 2 => (-620592789941 / 200000000000 : ℝ)
  | 3 => (-1565363426911 / 500000000000 : ℝ)
  | 4 => (-631741035283 / 200000000000 : ℝ)
  | 5 => (-3186900357229 / 1000000000000 : ℝ)
  | 6 => (-3215313844201 / 1000000000000 : ℝ)
  | 7 => (-6487894187 / 2000000000 : ℝ)
  | 8 => (-3272801569567 / 1000000000000 : ℝ)
  | 9 => (-51591855393 / 15625000000 : ℝ)
  | 10 => (-3331180101353 / 1000000000000 : ℝ)
  | 11 => (-3360707127659 / 1000000000000 : ℝ)
  | 12 => (-3390461321987 / 1000000000000 : ℝ)
  | 13 => (-136817767629 / 40000000000 : ℝ)
  | 14 => (-690131449753 / 200000000000 : ℝ)
  | 15 => (-3481102019553 / 1000000000000 : ℝ)
  | 16 => (-1755890017561 / 500000000000 : ℝ)
  | 17 => (-442836604517 / 125000000000 : ℝ)
  | 18 => (-3573841971927 / 1000000000000 : ℝ)
  | 19 => (-3605229000543 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch069Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1380 : ℝ) + (j.val : ℝ)) / 1600)
      (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch069Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch069Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1380 : ℝ) + (j.val : ℝ)) / 1600)
    (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch069Neg100WeightLower j.val) (hpThetaShiftTwoBatch069Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch069Neg100WeightLower, hpThetaShiftTwoBatch069Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch069Neg100_integral_bounds :
    (-2702485211 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-2605081757 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch069Lower hpThetaJensenCellsBatch069Upper
    hpThetaShiftTwoBatch069Neg100WeightLower hpThetaShiftTwoBatch069Neg100WeightUpper hpThetaJensenCellsBatch069_bounds hpThetaShiftTwoBatch069Neg100_weight_bounds
  have hl : (-2702485211 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch069Lower j * hpThetaShiftTwoBatch069Neg100WeightLower j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftTwoBatch069Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftTwoBatch069Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch069Lower j * hpThetaShiftTwoBatch069Neg100WeightUpper j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftTwoBatch069Neg100WeightUpper j) / 1600) ≤ (-2605081757 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftTwoBatch069Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1380 : ℝ) / 1600 = 69 / 80 by norm_num,
    show ((1380 : ℝ) + 20) / 1600 = (69 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch069Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-77133195953 / 200000000000 : ℝ)
  | 1 => (-487624191 / 1250000000 : ℝ)
  | 2 => (-394573414391 / 1000000000000 : ℝ)
  | 3 => (-399088470789 / 1000000000000 : ℝ)
  | 4 => (-6306950471 / 15625000000 : ℝ)
  | 5 => (-81648560503 / 200000000000 : ℝ)
  | 6 => (-10322067497 / 25000000000 : ℝ)
  | 7 => (-417564836147 / 1000000000000 : ℝ)
  | 8 => (-422289527159 / 1000000000000 : ℝ)
  | 9 => (-42705709071 / 100000000000 : ℝ)
  | 10 => (-431867846551 / 1000000000000 : ℝ)
  | 11 => (-436722116403 / 1000000000000 : ℝ)
  | 12 => (-441620223961 / 1000000000000 : ℝ)
  | 13 => (-44656249491 / 100000000000 : ℝ)
  | 14 => (-451549256933 / 1000000000000 : ℝ)
  | 15 => (-11414520993 / 25000000000 : ℝ)
  | 16 => (-461657574979 / 1000000000000 : ℝ)
  | 17 => (-93355959289 / 200000000000 : ℝ)
  | 18 => (-471947839893 / 1000000000000 : ℝ)
  | 19 => (-95432408629 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch069Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-381272990927 / 1000000000000 : ℝ)
  | 1 => (-96416494941 / 250000000000 : ℝ)
  | 2 => (-390099352799 / 1000000000000 : ℝ)
  | 3 => (-39457341439 / 100000000000 : ℝ)
  | 4 => (-99772117697 / 250000000000 : ℝ)
  | 5 => (-403644830143 / 1000000000000 : ℝ)
  | 6 => (-204121401257 / 500000000000 : ℝ)
  | 7 => (-412882699879 / 1000000000000 : ℝ)
  | 8 => (-208782418073 / 500000000000 : ℝ)
  | 9 => (-211144763579 / 500000000000 : ℝ)
  | 10 => (-427057090709 / 1000000000000 : ℝ)
  | 11 => (-8637356931 / 20000000000 : ℝ)
  | 12 => (-218361058201 / 500000000000 : ℝ)
  | 13 => (-11040505599 / 25000000000 : ℝ)
  | 14 => (-446562494909 / 1000000000000 : ℝ)
  | 15 => (-112887314233 / 250000000000 : ℝ)
  | 16 => (-456580839719 / 1000000000000 : ℝ)
  | 17 => (-230828787489 / 500000000000 : ℝ)
  | 18 => (-116694949111 / 250000000000 : ℝ)
  | 19 => (-117986959973 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch069Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1380 : ℝ) + (j.val : ℝ)) / 1600)
      (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch069Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch069Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1380 : ℝ) + (j.val : ℝ)) / 1600)
    (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch069Neg65WeightLower j.val) (hpThetaShiftTwoBatch069Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch069Neg65WeightLower, hpThetaShiftTwoBatch069Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch069Neg65_integral_bounds :
    (-43316501 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-83311047 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch069Lower hpThetaJensenCellsBatch069Upper
    hpThetaShiftTwoBatch069Neg65WeightLower hpThetaShiftTwoBatch069Neg65WeightUpper hpThetaJensenCellsBatch069_bounds hpThetaShiftTwoBatch069Neg65_weight_bounds
  have hl : (-43316501 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch069Lower j * hpThetaShiftTwoBatch069Neg65WeightLower j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftTwoBatch069Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftTwoBatch069Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch069Lower j * hpThetaShiftTwoBatch069Neg65WeightUpper j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftTwoBatch069Neg65WeightUpper j) / 1600) ≤ (-83311047 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftTwoBatch069Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1380 : ℝ) / 1600 = 69 / 80 by norm_num,
    show ((1380 : ℝ) + 20) / 1600 = (69 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch069Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3447195181 / 1000000000000 : ℝ)
  | 1 => (1500955503 / 500000000000 : ℝ)
  | 2 => (39837603 / 15625000000 : ℝ)
  | 3 => (2090213489 / 1000000000000 : ℝ)
  | 4 => (811831377 / 500000000000 : ℝ)
  | 5 => (1149884947 / 1000000000000 : ℝ)
  | 6 => (668810127 / 1000000000000 : ℝ)
  | 7 => (22545981 / 125000000000 : ℝ)
  | 8 => (-315512839 / 1000000000000 : ℝ)
  | 9 => (-204725849 / 250000000000 : ℝ)
  | 10 => (-83117237 / 62500000000 : ℝ)
  | 11 => (-924251257 / 500000000000 : ℝ)
  | 12 => (-1187428283 / 500000000000 : ℝ)
  | 13 => (-2909011471 / 1000000000000 : ℝ)
  | 14 => (-138041651 / 40000000000 : ℝ)
  | 15 => (-4001020553 / 1000000000000 : ℝ)
  | 16 => (-2279512203 / 500000000000 : ℝ)
  | 17 => (-1281282117 / 250000000000 : ℝ)
  | 18 => (-5699408907 / 1000000000000 : ℝ)
  | 19 => (-628194243 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch069Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (121422721 / 31250000000 : ℝ)
  | 1 => (1723597591 / 500000000000 : ℝ)
  | 2 => (3001911007 / 1000000000000 : ℝ)
  | 3 => (2549606593 / 1000000000000 : ℝ)
  | 4 => (209021349 / 100000000000 : ℝ)
  | 5 => (324732551 / 200000000000 : ℝ)
  | 6 => (287471237 / 250000000000 : ℝ)
  | 7 => (41800633 / 62500000000 : ℝ)
  | 8 => (180367849 / 1000000000000 : ℝ)
  | 9 => (-157756419 / 500000000000 : ℝ)
  | 10 => (-163780679 / 200000000000 : ℝ)
  | 11 => (-1329875791 / 1000000000000 : ℝ)
  | 12 => (-1848502513 / 1000000000000 : ℝ)
  | 13 => (-474971313 / 200000000000 : ℝ)
  | 14 => (-290901147 / 100000000000 : ℝ)
  | 15 => (-1725520637 / 500000000000 : ℝ)
  | 16 => (-500127569 / 125000000000 : ℝ)
  | 17 => (-911804881 / 200000000000 : ℝ)
  | 18 => (-5125128467 / 1000000000000 : ℝ)
  | 19 => (-2849704453 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch069Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1380 : ℝ) + (j.val : ℝ)) / 1600)
      (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch069Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch069Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1380 : ℝ) + (j.val : ℝ)) / 1600)
    (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch069Neg45WeightLower j.val) (hpThetaShiftTwoBatch069Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch069Neg45WeightLower, hpThetaShiftTwoBatch069Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch069Neg45_integral_bounds :
    (-726179 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-33367 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch069Lower hpThetaJensenCellsBatch069Upper
    hpThetaShiftTwoBatch069Neg45WeightLower hpThetaShiftTwoBatch069Neg45WeightUpper hpThetaJensenCellsBatch069_bounds hpThetaShiftTwoBatch069Neg45_weight_bounds
  have hl : (-726179 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch069Lower j * hpThetaShiftTwoBatch069Neg45WeightLower j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftTwoBatch069Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftTwoBatch069Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch069Lower j * hpThetaShiftTwoBatch069Neg45WeightUpper j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftTwoBatch069Neg45WeightUpper j) / 1600) ≤ (-33367 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftTwoBatch069Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1380 : ℝ) / 1600 = 69 / 80 by norm_num,
    show ((1380 : ℝ) + 20) / 1600 = (69 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch069Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (12899414063 / 1000000000000 : ℝ)
  | 1 => (6521589407 / 500000000000 : ℝ)
  | 2 => (1648458583 / 125000000000 : ℝ)
  | 3 => (1666610461 / 125000000000 : ℝ)
  | 4 => (13478823931 / 1000000000000 : ℝ)
  | 5 => (13625489407 / 1000000000000 : ℝ)
  | 6 => (430402503 / 31250000000 : ℝ)
  | 7 => (13920995947 / 1000000000000 : ℝ)
  | 8 => (175872961 / 12500000000 : ℝ)
  | 9 => (14219402777 / 1000000000000 : ℝ)
  | 10 => (14369693491 / 1000000000000 : ℝ)
  | 11 => (363017721 / 25000000000 : ℝ)
  | 12 => (1467244861 / 100000000000 : ℝ)
  | 13 => (1853114069 / 125000000000 : ℝ)
  | 14 => (468065637 / 31250000000 : ℝ)
  | 15 => (3783002947 / 250000000000 : ℝ)
  | 16 => (15286646413 / 1000000000000 : ℝ)
  | 17 => (15442003871 / 1000000000000 : ℝ)
  | 18 => (7799041871 / 500000000000 : ℝ)
  | 19 => (7877442783 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch069Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2608635763 / 200000000000 : ℝ)
  | 1 => (2637533733 / 200000000000 : ℝ)
  | 2 => (13332883689 / 1000000000000 : ℝ)
  | 3 => (3369705983 / 250000000000 : ℝ)
  | 4 => (6653071 / 488281250 : ℝ)
  | 5 => (13772880097 / 1000000000000 : ℝ)
  | 6 => (3480248987 / 250000000000 : ℝ)
  | 7 => (14069836881 / 1000000000000 : ℝ)
  | 8 => (7109701389 / 500000000000 : ℝ)
  | 9 => (3592423373 / 250000000000 : ℝ)
  | 10 => (14520708841 / 1000000000000 : ℝ)
  | 11 => (14672448611 / 1000000000000 : ℝ)
  | 12 => (14824912553 / 1000000000000 : ℝ)
  | 13 => (2995620077 / 200000000000 : ℝ)
  | 14 => (15132011789 / 1000000000000 : ℝ)
  | 15 => (7643323207 / 500000000000 : ℝ)
  | 16 => (482562621 / 31250000000 : ℝ)
  | 17 => (15598083743 / 1000000000000 : ℝ)
  | 18 => (15754885567 / 1000000000000 : ℝ)
  | 19 => (3978102213 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch069Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1380 : ℝ) + (j.val : ℝ)) / 1600)
      (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch069Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch069Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1380 : ℝ) + (j.val : ℝ)) / 1600)
    (((1380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch069Neg25WeightLower j.val) (hpThetaShiftTwoBatch069Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch069Neg25WeightLower, hpThetaShiftTwoBatch069Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch069Neg25_integral_bounds :
    (11212787 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (69 / 80 : ℝ) ((69 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (5825801 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch069Lower hpThetaJensenCellsBatch069Upper
    hpThetaShiftTwoBatch069Neg25WeightLower hpThetaShiftTwoBatch069Neg25WeightUpper hpThetaJensenCellsBatch069_bounds hpThetaShiftTwoBatch069Neg25_weight_bounds
  have hl : (11212787 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch069Lower j * hpThetaShiftTwoBatch069Neg25WeightLower j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftTwoBatch069Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftTwoBatch069Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch069Lower j * hpThetaShiftTwoBatch069Neg25WeightUpper j)
        (hpThetaJensenCellsBatch069Upper j * hpThetaShiftTwoBatch069Neg25WeightUpper j) / 1600) ≤ (5825801 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch069Lower, hpThetaJensenCellsBatch069Upper,
      hpThetaShiftTwoBatch069Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1380 : ℝ) / 1600 = 69 / 80 by norm_num,
    show ((1380 : ℝ) + 20) / 1600 = (69 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch069Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch069Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch069Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch069Neg25_integral_bounds
end HodgeProofHP
