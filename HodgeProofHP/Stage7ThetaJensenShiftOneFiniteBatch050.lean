/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch050

/-! Exact signed weight and batch integral certificates, batch 50 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch050Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-653427777131 / 250000000000 : ℝ)
  | 1 => (-662652296179 / 250000000000 : ℝ)
  | 2 => (-1343943835829 / 500000000000 : ℝ)
  | 3 => (-272554957467 / 100000000000 : ℝ)
  | 4 => (-276359791733 / 100000000000 : ℝ)
  | 5 => (-70050893539 / 25000000000 : ℝ)
  | 6 => (-2840866107707 / 1000000000000 : ℝ)
  | 7 => (-2880092094627 / 1000000000000 : ℝ)
  | 8 => (-2919716799769 / 1000000000000 : ℝ)
  | 9 => (-1479871669631 / 500000000000 : ℝ)
  | 10 => (-750043711999 / 250000000000 : ℝ)
  | 11 => (-3041014479711 / 1000000000000 : ℝ)
  | 12 => (-3082265407077 / 1000000000000 : ℝ)
  | 13 => (-624786164357 / 200000000000 : ℝ)
  | 14 => (-316601393463 / 100000000000 : ℝ)
  | 15 => (-3208517975597 / 1000000000000 : ℝ)
  | 16 => (-3251446193947 / 1000000000000 : ℝ)
  | 17 => (-3294801858307 / 1000000000000 : ℝ)
  | 18 => (-208661766047 / 62500000000 : ℝ)
  | 19 => (-676561739379 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch050Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-20134300437 / 7812500000 : ℝ)
  | 1 => (-2613711108523 / 1000000000000 : ℝ)
  | 2 => (-530121836943 / 200000000000 : ℝ)
  | 3 => (-2687887671657 / 1000000000000 : ℝ)
  | 4 => (-2725549574669 / 1000000000000 : ℝ)
  | 5 => (-2763597917329 / 1000000000000 : ℝ)
  | 6 => (-2802035741559 / 1000000000000 : ℝ)
  | 7 => (-1420433053853 / 500000000000 : ℝ)
  | 8 => (-1440046047313 / 500000000000 : ℝ)
  | 9 => (-364964599971 / 125000000000 : ℝ)
  | 10 => (-2959743339261 / 1000000000000 : ℝ)
  | 11 => (-600034969599 / 200000000000 : ℝ)
  | 12 => (-304101447971 / 100000000000 : ℝ)
  | 13 => (-770566351769 / 250000000000 : ℝ)
  | 14 => (-390491352723 / 125000000000 : ℝ)
  | 15 => (-3166013934629 / 1000000000000 : ℝ)
  | 16 => (-802129493899 / 250000000000 : ℝ)
  | 17 => (-1625723096973 / 500000000000 : ℝ)
  | 18 => (-1647400929153 / 500000000000 : ℝ)
  | 19 => (-3338588256751 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch050Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1000 : ℝ) + (j.val : ℝ)) / 1600)
      (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch050Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch050Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1000 : ℝ) + (j.val : ℝ)) / 1600)
    (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch050Neg100WeightLower j.val) (hpThetaShiftOneBatch050Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch050Neg100WeightLower, hpThetaShiftOneBatch050Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch050Neg100_integral_bounds :
    (-662959513317 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-641362643023 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1000 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch050Lower hpThetaJensenCellsBatch050Upper
    hpThetaShiftOneBatch050Neg100WeightLower hpThetaShiftOneBatch050Neg100WeightUpper hpThetaJensenCellsBatch050_bounds hpThetaShiftOneBatch050Neg100_weight_bounds
  have hl : (-662959513317 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch050Lower j * hpThetaShiftOneBatch050Neg100WeightLower j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftOneBatch050Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftOneBatch050Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch050Lower j * hpThetaShiftOneBatch050Neg100WeightUpper j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftOneBatch050Neg100WeightUpper j) / 1600) ≤ (-641362643023 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftOneBatch050Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1000 : ℝ) / 1600 = 50 / 80 by norm_num,
    show ((1000 : ℝ) + 20) / 1600 = (50 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch050Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (101626447467 / 500000000000 : ℝ)
  | 1 => (200970474549 / 1000000000000 : ℝ)
  | 2 => (49658312719 / 250000000000 : ℝ)
  | 3 => (196240630537 / 1000000000000 : ℝ)
  | 4 => (193792015901 / 1000000000000 : ℝ)
  | 5 => (191286805067 / 1000000000000 : ℝ)
  | 6 => (188724391839 / 1000000000000 : ℝ)
  | 7 => (46526041427 / 250000000000 : ℝ)
  | 8 => (45856377957 / 250000000000 : ℝ)
  | 9 => (36137562199 / 200000000000 : ℝ)
  | 10 => (88945219813 / 500000000000 : ℝ)
  | 11 => (21879096217 / 125000000000 : ℝ)
  | 12 => (172114168917 / 1000000000000 : ℝ)
  | 13 => (169134000317 / 1000000000000 : ℝ)
  | 14 => (20761452827 / 125000000000 : ℝ)
  | 15 => (162986390007 / 1000000000000 : ℝ)
  | 16 => (159817652169 / 1000000000000 : ℝ)
  | 17 => (626339017 / 4000000000 : ℝ)
  | 18 => (76643518421 / 500000000000 : ℝ)
  | 19 => (149923835959 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch050Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (205481101183 / 1000000000000 : ℝ)
  | 1 => (40650578987 / 200000000000 : ℝ)
  | 2 => (4019409491 / 20000000000 : ℝ)
  | 3 => (198633250877 / 1000000000000 : ℝ)
  | 4 => (98120315269 / 500000000000 : ℝ)
  | 5 => (96896007951 / 500000000000 : ℝ)
  | 6 => (47821701267 / 250000000000 : ℝ)
  | 7 => (1179527449 / 6250000000 : ℝ)
  | 8 => (186104165709 / 1000000000000 : ℝ)
  | 9 => (183425511829 / 1000000000000 : ℝ)
  | 10 => (45171952749 / 250000000000 : ℝ)
  | 11 => (177890439627 / 1000000000000 : ℝ)
  | 12 => (175032769737 / 1000000000000 : ℝ)
  | 13 => (86057084459 / 500000000000 : ℝ)
  | 14 => (84567000159 / 500000000000 : ℝ)
  | 15 => (166091622617 / 1000000000000 : ℝ)
  | 16 => (20373298751 / 125000000000 : ℝ)
  | 17 => (15981765217 / 100000000000 : ℝ)
  | 18 => (156584754251 / 1000000000000 : ℝ)
  | 19 => (153287036843 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch050Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1000 : ℝ) + (j.val : ℝ)) / 1600)
      (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch050Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch050Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1000 : ℝ) + (j.val : ℝ)) / 1600)
    (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch050Neg65WeightLower j.val) (hpThetaShiftOneBatch050Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch050Neg65WeightLower, hpThetaShiftOneBatch050Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch050Neg65_integral_bounds :
    (9806142193 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (40612043509 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1000 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch050Lower hpThetaJensenCellsBatch050Upper
    hpThetaShiftOneBatch050Neg65WeightLower hpThetaShiftOneBatch050Neg65WeightUpper hpThetaJensenCellsBatch050_bounds hpThetaShiftOneBatch050Neg65_weight_bounds
  have hl : (9806142193 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch050Lower j * hpThetaShiftOneBatch050Neg65WeightLower j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftOneBatch050Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftOneBatch050Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch050Lower j * hpThetaShiftOneBatch050Neg65WeightUpper j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftOneBatch050Neg65WeightUpper j) / 1600) ≤ (40612043509 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftOneBatch050Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1000 : ℝ) / 1600 = 50 / 80 by norm_num,
    show ((1000 : ℝ) + 20) / 1600 = (50 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch050Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (166645504179 / 1000000000000 : ℝ)
  | 1 => (84071948347 / 500000000000 : ℝ)
  | 2 => (169646175391 / 1000000000000 : ℝ)
  | 3 => (1069701817 / 6250000000 : ℝ)
  | 4 => (172662192453 / 1000000000000 : ℝ)
  | 5 => (174175829683 / 1000000000000 : ℝ)
  | 6 => (35138630163 / 200000000000 : ℝ)
  | 7 => (177214103567 / 1000000000000 : ℝ)
  | 8 => (178738634959 / 1000000000000 : ℝ)
  | 9 => (180266691317 / 1000000000000 : ℝ)
  | 10 => (181798218261 / 1000000000000 : ℝ)
  | 11 => (36666632141 / 200000000000 : ℝ)
  | 12 => (184871462849 / 1000000000000 : ℝ)
  | 13 => (186413068181 / 1000000000000 : ℝ)
  | 14 => (23494739933 / 125000000000 : ℝ)
  | 15 => (189505958741 / 1000000000000 : ℝ)
  | 16 => (4776428183 / 25000000000 : ℝ)
  | 17 => (192611365779 / 1000000000000 : ℝ)
  | 18 => (48542153489 / 250000000000 : ℝ)
  | 19 => (48932202737 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch050Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (33628779339 / 200000000000 : ℝ)
  | 1 => (5301442981 / 31250000000 : ℝ)
  | 2 => (171152290721 / 1000000000000 : ℝ)
  | 3 => (86331096227 / 500000000000 : ℝ)
  | 4 => (43543957421 / 250000000000 : ℝ)
  | 5 => (5490410963 / 31250000000 : ℝ)
  | 6 => (11075881473 / 62500000000 : ℝ)
  | 7 => (2234232937 / 12500000000 : ℝ)
  | 8 => (90133345659 / 500000000000 : ℝ)
  | 9 => (90899109131 / 500000000000 : ℝ)
  | 10 => (91666580353 / 500000000000 : ℝ)
  | 11 => (3697429257 / 20000000000 : ℝ)
  | 12 => (93206534091 / 500000000000 : ℝ)
  | 13 => (37591583893 / 200000000000 : ℝ)
  | 14 => (94752979371 / 500000000000 : ℝ)
  | 15 => (191057127321 / 1000000000000 : ℝ)
  | 16 => (9630568289 / 50000000000 : ℝ)
  | 17 => (194168613957 / 1000000000000 : ℝ)
  | 18 => (195728810949 / 1000000000000 : ℝ)
  | 19 => (98645947551 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch050Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1000 : ℝ) + (j.val : ℝ)) / 1600)
      (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch050Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch050Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1000 : ℝ) + (j.val : ℝ)) / 1600)
    (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch050Neg40WeightLower j.val) (hpThetaShiftOneBatch050Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch050Neg40WeightLower, hpThetaShiftOneBatch050Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch050Neg40_integral_bounds :
    (39492564599 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (40612561103 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1000 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch050Lower hpThetaJensenCellsBatch050Upper
    hpThetaShiftOneBatch050Neg40WeightLower hpThetaShiftOneBatch050Neg40WeightUpper hpThetaJensenCellsBatch050_bounds hpThetaShiftOneBatch050Neg40_weight_bounds
  have hl : (39492564599 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch050Lower j * hpThetaShiftOneBatch050Neg40WeightLower j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftOneBatch050Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftOneBatch050Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch050Lower j * hpThetaShiftOneBatch050Neg40WeightUpper j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftOneBatch050Neg40WeightUpper j) / 1600) ≤ (40612561103 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftOneBatch050Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1000 : ℝ) / 1600 = 50 / 80 by norm_num,
    show ((1000 : ℝ) + 20) / 1600 = (50 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch050Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-16490448089 / 200000000000 : ℝ)
  | 1 => (-82422611827 / 1000000000000 : ℝ)
  | 2 => (-82390059313 / 1000000000000 : ℝ)
  | 3 => (-82354566927 / 1000000000000 : ℝ)
  | 4 => (-41158059341 / 500000000000 : ℝ)
  | 5 => (-82274698583 / 1000000000000 : ℝ)
  | 6 => (-82230290627 / 1000000000000 : ℝ)
  | 7 => (-82182878801 / 1000000000000 : ℝ)
  | 8 => (-41066223543 / 500000000000 : ℝ)
  | 9 => (-82078979451 / 1000000000000 : ℝ)
  | 10 => (-82022459863 / 1000000000000 : ℝ)
  | 11 => (-81962872279 / 1000000000000 : ℝ)
  | 12 => (-81900200649 / 1000000000000 : ℝ)
  | 13 => (-40917214459 / 500000000000 : ℝ)
  | 14 => (-81765541023 / 1000000000000 : ℝ)
  | 15 => (-40846760449 / 500000000000 : ℝ)
  | 16 => (-81618352469 / 1000000000000 : ℝ)
  | 17 => (-40770009829 / 500000000000 : ℝ)
  | 18 => (-81458506383 / 1000000000000 : ℝ)
  | 19 => (-20343449139 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch050Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-41211305913 / 500000000000 : ℝ)
  | 1 => (-5149378707 / 62500000000 : ℝ)
  | 2 => (-41177283463 / 500000000000 : ℝ)
  | 3 => (-82316118681 / 1000000000000 : ℝ)
  | 4 => (-41137349291 / 500000000000 : ℝ)
  | 5 => (-41115145313 / 500000000000 : ℝ)
  | 6 => (-205457197 / 2500000000 : ℝ)
  | 7 => (-16426489417 / 200000000000 : ℝ)
  | 8 => (-1641579589 / 20000000000 : ℝ)
  | 9 => (-41011229931 / 500000000000 : ℝ)
  | 10 => (-40981436139 / 500000000000 : ℝ)
  | 11 => (-10237525081 / 125000000000 : ℝ)
  | 12 => (-81834428917 / 1000000000000 : ℝ)
  | 13 => (-40882770511 / 500000000000 : ℝ)
  | 14 => (-81693520897 / 1000000000000 : ℝ)
  | 15 => (-20404588117 / 250000000000 : ℝ)
  | 16 => (-81540019657 / 1000000000000 : ℝ)
  | 17 => (-40729253191 / 500000000000 : ℝ)
  | 18 => (-16274759311 / 200000000000 : ℝ)
  | 19 => (-16257174817 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch050Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1000 : ℝ) + (j.val : ℝ)) / 1600)
      (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch050Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch050Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1000 : ℝ) + (j.val : ℝ)) / 1600)
    (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch050Neg20WeightLower j.val) (hpThetaShiftOneBatch050Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch050Neg20WeightLower, hpThetaShiftOneBatch050Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch050Neg20_integral_bounds :
    (-18295735017 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-17929643673 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1000 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch050Lower hpThetaJensenCellsBatch050Upper
    hpThetaShiftOneBatch050Neg20WeightLower hpThetaShiftOneBatch050Neg20WeightUpper hpThetaJensenCellsBatch050_bounds hpThetaShiftOneBatch050Neg20_weight_bounds
  have hl : (-18295735017 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch050Lower j * hpThetaShiftOneBatch050Neg20WeightLower j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftOneBatch050Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftOneBatch050Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch050Lower j * hpThetaShiftOneBatch050Neg20WeightUpper j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftOneBatch050Neg20WeightUpper j) / 1600) ≤ (-17929643673 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftOneBatch050Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1000 : ℝ) / 1600 = 50 / 80 by norm_num,
    show ((1000 : ℝ) + 20) / 1600 = (50 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch050Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch050Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch050Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch050Neg20_integral_bounds
end HodgeProofHP
