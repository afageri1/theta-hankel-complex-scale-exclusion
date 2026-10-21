/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch030

/-! Exact signed weight and batch integral certificates, batch 30 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch030Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (19189442907 / 500000000000 : ℝ)
  | 1 => (4896095309 / 125000000000 : ℝ)
  | 2 => (39964244673 / 1000000000000 : ℝ)
  | 3 => (20382649921 / 500000000000 : ℝ)
  | 4 => (41571894199 / 1000000000000 : ℝ)
  | 5 => (42383992741 / 1000000000000 : ℝ)
  | 6 => (10800389809 / 250000000000 : ℝ)
  | 7 => (44024556203 / 1000000000000 : ℝ)
  | 8 => (44852944899 / 1000000000000 : ℝ)
  | 9 => (9137337061 / 200000000000 : ℝ)
  | 10 => (2907858507 / 62500000000 : ℝ)
  | 11 => (11842513677 / 250000000000 : ℝ)
  | 12 => (1205489929 / 25000000000 : ℝ)
  | 13 => (49074318201 / 1000000000000 : ℝ)
  | 14 => (49934171217 / 1000000000000 : ℝ)
  | 15 => (50799108229 / 1000000000000 : ℝ)
  | 16 => (51669079879 / 1000000000000 : ℝ)
  | 17 => (52544035419 / 1000000000000 : ℝ)
  | 18 => (5342392269 / 100000000000 : ℝ)
  | 19 => (54308688109 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch030Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (39168762473 / 1000000000000 : ℝ)
  | 1 => (19982122337 / 500000000000 : ℝ)
  | 2 => (40765299843 / 1000000000000 : ℝ)
  | 3 => (207859471 / 5000000000 : ℝ)
  | 4 => (21191996371 / 500000000000 : ℝ)
  | 5 => (43201559237 / 1000000000000 : ℝ)
  | 6 => (11006139051 / 250000000000 : ℝ)
  | 7 => (448529449 / 10000000000 : ℝ)
  | 8 => (22843342653 / 500000000000 : ℝ)
  | 9 => (46525736113 / 1000000000000 : ℝ)
  | 10 => (47370054709 / 1000000000000 : ℝ)
  | 11 => (48219597161 / 1000000000000 : ℝ)
  | 12 => (24537159101 / 500000000000 : ℝ)
  | 13 => (24967085609 / 500000000000 : ℝ)
  | 14 => (5079910823 / 100000000000 : ℝ)
  | 15 => (1291726997 / 25000000000 : ℝ)
  | 16 => (2627201771 / 50000000000 : ℝ)
  | 17 => (53423922691 / 1000000000000 : ℝ)
  | 18 => (5430868811 / 100000000000 : ℝ)
  | 19 => (3449892291 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch030Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((600 : ℝ) + (j.val : ℝ)) / 1600)
      (((600 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch030Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch030Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((600 : ℝ) + (j.val : ℝ)) / 1600)
    (((600 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch030Neg100WeightLower j.val) (hpThetaShiftOneBatch030Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch030Neg100WeightLower, hpThetaShiftOneBatch030Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch030Neg100_integral_bounds :
    (232295476241 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (239922324561 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (600 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch030Lower hpThetaJensenCellsBatch030Upper
    hpThetaShiftOneBatch030Neg100WeightLower hpThetaShiftOneBatch030Neg100WeightUpper hpThetaJensenCellsBatch030_bounds hpThetaShiftOneBatch030Neg100_weight_bounds
  have hl : (232295476241 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch030Lower j * hpThetaShiftOneBatch030Neg100WeightLower j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftOneBatch030Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftOneBatch030Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch030Lower j * hpThetaShiftOneBatch030Neg100WeightUpper j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftOneBatch030Neg100WeightUpper j) / 1600) ≤ (239922324561 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftOneBatch030Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (600 : ℝ) / 1600 = 30 / 80 by norm_num,
    show ((600 : ℝ) + 20) / 1600 = (30 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch030Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-21230024419 / 1000000000000 : ℝ)
  | 1 => (-4210177 / 200000000 : ℝ)
  | 2 => (-1304219057 / 62500000000 : ℝ)
  | 3 => (-20679856229 / 1000000000000 : ℝ)
  | 4 => (-10243955551 / 500000000000 : ℝ)
  | 5 => (-20291641763 / 1000000000000 : ℝ)
  | 6 => (-20091020527 / 1000000000000 : ℝ)
  | 7 => (-4971504949 / 250000000000 : ℝ)
  | 8 => (-9838306031 / 500000000000 : ℝ)
  | 9 => (-4865692477 / 250000000000 : ℝ)
  | 10 => (-3848893203 / 200000000000 : ℝ)
  | 11 => (-475541829 / 25000000000 : ℝ)
  | 12 => (-18794364223 / 1000000000000 : ℝ)
  | 13 => (-18562512187 / 1000000000000 : ℝ)
  | 14 => (-3665218029 / 200000000000 : ℝ)
  | 15 => (-18085071297 / 1000000000000 : ℝ)
  | 16 => (-17839428961 / 1000000000000 : ℝ)
  | 17 => (-1758913657 / 100000000000 : ℝ)
  | 18 => (-4333541919 / 250000000000 : ℝ)
  | 19 => (-4268623989 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch030Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-21050884999 / 1000000000000 : ℝ)
  | 1 => (-20867504911 / 1000000000000 : ℝ)
  | 2 => (-5169964057 / 250000000000 : ℝ)
  | 3 => (-20487911101 / 1000000000000 : ℝ)
  | 4 => (-10145820881 / 500000000000 : ℝ)
  | 5 => (-10045510263 / 500000000000 : ℝ)
  | 6 => (-3977203959 / 200000000000 : ℝ)
  | 7 => (-19676612061 / 1000000000000 : ℝ)
  | 8 => (-19462769907 / 1000000000000 : ℝ)
  | 9 => (-9622233007 / 500000000000 : ℝ)
  | 10 => (-19021673159 / 1000000000000 : ℝ)
  | 11 => (-9397182111 / 500000000000 : ℝ)
  | 12 => (-9281256093 / 500000000000 : ℝ)
  | 13 => (-572690317 / 31250000000 : ℝ)
  | 14 => (-282579239 / 15625000000 : ℝ)
  | 15 => (-111496431 / 6250000000 : ℝ)
  | 16 => (-17589136569 / 1000000000000 : ℝ)
  | 17 => (-693366707 / 40000000000 : ℝ)
  | 18 => (-3414899191 / 200000000000 : ℝ)
  | 19 => (-16810095213 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch030Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((600 : ℝ) + (j.val : ℝ)) / 1600)
      (((600 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch030Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch030Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((600 : ℝ) + (j.val : ℝ)) / 1600)
    (((600 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch030Neg65WeightLower j.val) (hpThetaShiftOneBatch030Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch030Neg65WeightLower, hpThetaShiftOneBatch030Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch030Neg65_integral_bounds :
    (-49424714897 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-96343166957 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (600 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch030Lower hpThetaJensenCellsBatch030Upper
    hpThetaShiftOneBatch030Neg65WeightLower hpThetaShiftOneBatch030Neg65WeightUpper hpThetaJensenCellsBatch030_bounds hpThetaShiftOneBatch030Neg65_weight_bounds
  have hl : (-49424714897 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch030Lower j * hpThetaShiftOneBatch030Neg65WeightLower j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftOneBatch030Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftOneBatch030Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch030Lower j * hpThetaShiftOneBatch030Neg65WeightUpper j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftOneBatch030Neg65WeightUpper j) / 1600) ≤ (-96343166957 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftOneBatch030Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (600 : ℝ) / 1600 = 30 / 80 by norm_num,
    show ((600 : ℝ) + 20) / 1600 = (30 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch030Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-7818116563 / 250000000000 : ℝ)
  | 1 => (-15720787747 / 500000000000 : ℝ)
  | 2 => (-6321980031 / 200000000000 : ℝ)
  | 3 => (-31777423387 / 1000000000000 : ℝ)
  | 4 => (-15972064131 / 500000000000 : ℝ)
  | 5 => (-2006874861 / 62500000000 : ℝ)
  | 6 => (-16137507423 / 500000000000 : ℝ)
  | 7 => (-32439162311 / 1000000000000 : ℝ)
  | 8 => (-32602422933 / 1000000000000 : ℝ)
  | 9 => (-16382389699 / 500000000000 : ℝ)
  | 10 => (-32926214313 / 1000000000000 : ℝ)
  | 11 => (-3308671021 / 100000000000 : ℝ)
  | 12 => (-16623124773 / 500000000000 : ℝ)
  | 13 => (-334048147 / 10000000000 : ℝ)
  | 14 => (-4195298497 / 125000000000 : ℝ)
  | 15 => (-6743790321 / 200000000000 : ℝ)
  | 16 => (-33874487739 / 1000000000000 : ℝ)
  | 17 => (-1701448923 / 50000000000 : ℝ)
  | 18 => (-34182405773 / 1000000000000 : ℝ)
  | 19 => (-34334751609 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch030Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-15551294599 / 500000000000 : ℝ)
  | 1 => (-31272466251 / 1000000000000 : ℝ)
  | 2 => (-31441575493 / 1000000000000 : ℝ)
  | 3 => (-15804950077 / 500000000000 : ℝ)
  | 4 => (-15888711693 / 500000000000 : ℝ)
  | 5 => (-31944128261 / 1000000000000 : ℝ)
  | 6 => (-1284399911 / 40000000000 : ℝ)
  | 7 => (-6455002969 / 200000000000 : ℝ)
  | 8 => (-3243916231 / 100000000000 : ℝ)
  | 9 => (-8150605733 / 250000000000 : ℝ)
  | 10 => (-32764779397 / 1000000000000 : ℝ)
  | 11 => (-4115776789 / 125000000000 : ℝ)
  | 12 => (-33086710209 / 1000000000000 : ℝ)
  | 13 => (-6649249909 / 200000000000 : ℝ)
  | 14 => (-33404814699 / 1000000000000 : ℝ)
  | 15 => (-1342495519 / 40000000000 : ℝ)
  | 16 => (-8429737901 / 250000000000 : ℝ)
  | 17 => (-16937243869 / 500000000000 : ℝ)
  | 18 => (-34028978459 / 1000000000000 : ℝ)
  | 19 => (-8545601443 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch030Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((600 : ℝ) + (j.val : ℝ)) / 1600)
      (((600 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch030Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch030Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((600 : ℝ) + (j.val : ℝ)) / 1600)
    (((600 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch030Neg40WeightLower j.val) (hpThetaShiftOneBatch030Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch030Neg40WeightLower, hpThetaShiftOneBatch030Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch030Neg40_integral_bounds :
    (-6713919091 / 40000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-82330844741 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (600 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch030Lower hpThetaJensenCellsBatch030Upper
    hpThetaShiftOneBatch030Neg40WeightLower hpThetaShiftOneBatch030Neg40WeightUpper hpThetaJensenCellsBatch030_bounds hpThetaShiftOneBatch030Neg40_weight_bounds
  have hl : (-6713919091 / 40000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch030Lower j * hpThetaShiftOneBatch030Neg40WeightLower j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftOneBatch030Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftOneBatch030Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch030Lower j * hpThetaShiftOneBatch030Neg40WeightUpper j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftOneBatch030Neg40WeightUpper j) / 1600) ≤ (-82330844741 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftOneBatch030Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (600 : ℝ) / 1600 = 30 / 80 by norm_num,
    show ((600 : ℝ) + 20) / 1600 = (30 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch030Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2789510809 / 1000000000000 : ℝ)
  | 1 => (-1481184047 / 500000000000 : ℝ)
  | 2 => (-196006231 / 62500000000 : ℝ)
  | 3 => (-3310703963 / 1000000000000 : ℝ)
  | 4 => (-1743089603 / 500000000000 : ℝ)
  | 5 => (-36625237 / 10000000000 : ℝ)
  | 6 => (-1919867843 / 500000000000 : ℝ)
  | 7 => (-4017813369 / 1000000000000 : ℝ)
  | 8 => (-104918873 / 25000000000 : ℝ)
  | 9 => (-4376558473 / 1000000000000 : ℝ)
  | 10 => (-4557222127 / 1000000000000 : ℝ)
  | 11 => (-592342993 / 125000000000 : ℝ)
  | 12 => (-153785061 / 31250000000 : ℝ)
  | 13 => (-5104354141 / 1000000000000 : ℝ)
  | 14 => (-1322109617 / 250000000000 : ℝ)
  | 15 => (-109467457 / 20000000000 : ℝ)
  | 16 => (-1414788793 / 250000000000 : ℝ)
  | 17 => (-5845783279 / 1000000000000 : ℝ)
  | 18 => (-3016627491 / 500000000000 : ℝ)
  | 19 => (-3110784027 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch030Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-130876473 / 50000000000 : ℝ)
  | 1 => (-348688851 / 125000000000 : ℝ)
  | 2 => (-2962368093 / 1000000000000 : ℝ)
  | 3 => (-627219939 / 200000000000 : ℝ)
  | 4 => (-1655351981 / 500000000000 : ℝ)
  | 5 => (-697235841 / 200000000000 : ℝ)
  | 6 => (-3662523699 / 1000000000000 : ℝ)
  | 7 => (-767947137 / 200000000000 : ℝ)
  | 8 => (-502226671 / 125000000000 : ℝ)
  | 9 => (-4196754919 / 1000000000000 : ℝ)
  | 10 => (-547069809 / 125000000000 : ℝ)
  | 11 => (-2278611063 / 500000000000 : ℝ)
  | 12 => (-4738743943 / 1000000000000 : ℝ)
  | 13 => (-4921121951 / 1000000000000 : ℝ)
  | 14 => (-255217707 / 50000000000 : ℝ)
  | 15 => (-5288438467 / 1000000000000 : ℝ)
  | 16 => (-5473372849 / 1000000000000 : ℝ)
  | 17 => (-5659155171 / 1000000000000 : ℝ)
  | 18 => (-2922891639 / 500000000000 : ℝ)
  | 19 => (-6033254981 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch030Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((600 : ℝ) + (j.val : ℝ)) / 1600)
      (((600 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch030Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch030Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((600 : ℝ) + (j.val : ℝ)) / 1600)
    (((600 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch030Neg20WeightLower j.val) (hpThetaShiftOneBatch030Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch030Neg20WeightLower, hpThetaShiftOneBatch030Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch030Neg20_integral_bounds :
    (-22768536521 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (30 / 80 : ℝ) ((30 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-5384609527 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (600 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch030Lower hpThetaJensenCellsBatch030Upper
    hpThetaShiftOneBatch030Neg20WeightLower hpThetaShiftOneBatch030Neg20WeightUpper hpThetaJensenCellsBatch030_bounds hpThetaShiftOneBatch030Neg20_weight_bounds
  have hl : (-22768536521 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch030Lower j * hpThetaShiftOneBatch030Neg20WeightLower j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftOneBatch030Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftOneBatch030Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch030Lower j * hpThetaShiftOneBatch030Neg20WeightUpper j)
        (hpThetaJensenCellsBatch030Upper j * hpThetaShiftOneBatch030Neg20WeightUpper j) / 1600) ≤ (-5384609527 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch030Lower, hpThetaJensenCellsBatch030Upper,
      hpThetaShiftOneBatch030Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (600 : ℝ) / 1600 = 30 / 80 by norm_num,
    show ((600 : ℝ) + 20) / 1600 = (30 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch030Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch030Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch030Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch030Neg20_integral_bounds
end HodgeProofHP
