/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch020

/-! Exact signed weight and batch integral certificates, batch 20 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch020Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-14539472873 / 1000000000000 : ℝ)
  | 1 => (-365596941 / 25000000000 : ℝ)
  | 2 => (-14706890197 / 1000000000000 : ℝ)
  | 3 => (-3697119997 / 250000000000 : ℝ)
  | 4 => (-1486861629 / 100000000000 : ℝ)
  | 5 => (-1868408527 / 125000000000 : ℝ)
  | 6 => (-7512202359 / 500000000000 : ℝ)
  | 7 => (-7549997293 / 500000000000 : ℝ)
  | 8 => (-3034801291 / 200000000000 : ℝ)
  | 9 => (-19058011 / 1250000000 : ℝ)
  | 10 => (-3063433989 / 200000000000 : ℝ)
  | 11 => (-15386258061 / 1000000000000 : ℝ)
  | 12 => (-7726820583 / 500000000000 : ℝ)
  | 13 => (-7759643567 / 500000000000 : ℝ)
  | 14 => (-1558316369 / 100000000000 : ℝ)
  | 15 => (-977827401 / 62500000000 : ℝ)
  | 16 => (-490796211 / 31250000000 : ℝ)
  | 17 => (-3940963 / 250000000 : ℝ)
  | 18 => (-7910162661 / 500000000000 : ℝ)
  | 19 => (-3968716437 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch020Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-14453706287 / 1000000000000 : ℝ)
  | 1 => (-1817434109 / 125000000000 : ℝ)
  | 2 => (-14623877639 / 1000000000000 : ℝ)
  | 3 => (-3676722549 / 250000000000 : ℝ)
  | 4 => (-14788479987 / 1000000000000 : ℝ)
  | 5 => (-14868616289 / 1000000000000 : ℝ)
  | 6 => (-2989453643 / 200000000000 : ℝ)
  | 7 => (-15024404717 / 1000000000000 : ℝ)
  | 8 => (-3019998917 / 200000000000 : ℝ)
  | 9 => (-7587003227 / 500000000000 : ℝ)
  | 10 => (-15246408799 / 1000000000000 : ℝ)
  | 11 => (-1914646243 / 125000000000 : ℝ)
  | 12 => (-769312903 / 50000000000 : ℝ)
  | 13 => (-3090728233 / 200000000000 : ℝ)
  | 14 => (-15519287133 / 1000000000000 : ℝ)
  | 15 => (-15583163689 / 1000000000000 : ℝ)
  | 16 => (-3129047683 / 200000000000 : ℝ)
  | 17 => (-15705478751 / 1000000000000 : ℝ)
  | 18 => (-15763851999 / 1000000000000 : ℝ)
  | 19 => (-15820325321 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch020Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((400 : ℝ) + (j.val : ℝ)) / 1600)
      (((400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch020Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch020Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((400 : ℝ) + (j.val : ℝ)) / 1600)
    (((400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch020Neg100WeightLower j.val) (hpThetaShiftOneBatch020Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch020Neg100WeightLower, hpThetaShiftOneBatch020Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch020Neg100_integral_bounds :
    (-180924977649 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-177842296277 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch020Lower hpThetaJensenCellsBatch020Upper
    hpThetaShiftOneBatch020Neg100WeightLower hpThetaShiftOneBatch020Neg100WeightUpper hpThetaJensenCellsBatch020_bounds hpThetaShiftOneBatch020Neg100_weight_bounds
  have hl : (-180924977649 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch020Lower j * hpThetaShiftOneBatch020Neg100WeightLower j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftOneBatch020Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftOneBatch020Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch020Lower j * hpThetaShiftOneBatch020Neg100WeightUpper j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftOneBatch020Neg100WeightUpper j) / 1600) ≤ (-177842296277 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftOneBatch020Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (400 : ℝ) / 1600 = 20 / 80 by norm_num,
    show ((400 : ℝ) + 20) / 1600 = (20 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch020Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-9075315109 / 1000000000000 : ℝ)
  | 1 => (-9217505229 / 1000000000000 : ℝ)
  | 2 => (-9360080151 / 1000000000000 : ℝ)
  | 3 => (-9503028073 / 1000000000000 : ℝ)
  | 4 => (-1929267411 / 200000000000 : ℝ)
  | 5 => (-4894997507 / 500000000000 : ℝ)
  | 6 => (-9933989729 / 1000000000000 : ℝ)
  | 7 => (-10078308837 / 1000000000000 : ℝ)
  | 8 => (-10222939837 / 1000000000000 : ℝ)
  | 9 => (-2591967521 / 250000000000 : ℝ)
  | 10 => (-5256543397 / 500000000000 : ℝ)
  | 11 => (-2664644261 / 250000000000 : ℝ)
  | 12 => (-10804327767 / 1000000000000 : ℝ)
  | 13 => (-10950325757 / 1000000000000 : ℝ)
  | 14 => (-11096557667 / 1000000000000 : ℝ)
  | 15 => (-5621505003 / 500000000000 : ℝ)
  | 16 => (-11389669147 / 1000000000000 : ℝ)
  | 17 => (-2884130329 / 250000000000 : ℝ)
  | 18 => (-11683552603 / 1000000000000 : ℝ)
  | 19 => (-11830748953 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch020Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2233380363 / 250000000000 : ℝ)
  | 1 => (-2268828777 / 250000000000 : ℝ)
  | 2 => (-2304376307 / 250000000000 : ℝ)
  | 3 => (-187201603 / 20000000000 : ℝ)
  | 4 => (-1187878509 / 125000000000 : ℝ)
  | 5 => (-4823168527 / 500000000000 : ℝ)
  | 6 => (-9789995013 / 1000000000000 : ℝ)
  | 7 => (-310437179 / 31250000000 : ℝ)
  | 8 => (-2519577209 / 250000000000 : ℝ)
  | 9 => (-2555734959 / 250000000000 : ℝ)
  | 10 => (-10367870083 / 1000000000000 : ℝ)
  | 11 => (-10513086793 / 1000000000000 : ℝ)
  | 12 => (-10658577043 / 1000000000000 : ℝ)
  | 13 => (-5402163883 / 500000000000 : ℝ)
  | 14 => (-2737581439 / 250000000000 : ℝ)
  | 15 => (-5548278833 / 500000000000 : ℝ)
  | 16 => (-2248602001 / 200000000000 : ℝ)
  | 17 => (-5694834573 / 500000000000 : ℝ)
  | 18 => (-2307304263 / 200000000000 : ℝ)
  | 19 => (-5841776301 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch020Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((400 : ℝ) + (j.val : ℝ)) / 1600)
      (((400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch020Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch020Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((400 : ℝ) + (j.val : ℝ)) / 1600)
    (((400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch020Neg65WeightLower j.val) (hpThetaShiftOneBatch020Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch020Neg65WeightLower, hpThetaShiftOneBatch020Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch020Neg65_integral_bounds :
    (-123760034981 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-60262427053 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch020Lower hpThetaJensenCellsBatch020Upper
    hpThetaShiftOneBatch020Neg65WeightLower hpThetaShiftOneBatch020Neg65WeightUpper hpThetaJensenCellsBatch020_bounds hpThetaShiftOneBatch020Neg65_weight_bounds
  have hl : (-123760034981 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch020Lower j * hpThetaShiftOneBatch020Neg65WeightLower j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftOneBatch020Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftOneBatch020Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch020Lower j * hpThetaShiftOneBatch020Neg65WeightUpper j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftOneBatch020Neg65WeightUpper j) / 1600) ≤ (-60262427053 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftOneBatch020Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (400 : ℝ) / 1600 = 20 / 80 by norm_num,
    show ((400 : ℝ) + 20) / 1600 = (20 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch020Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1271865803 / 1000000000000 : ℝ)
  | 1 => (585491499 / 500000000000 : ℝ)
  | 2 => (534595043 / 500000000000 : ℝ)
  | 3 => (193297567 / 200000000000 : ℝ)
  | 4 => (34515083 / 40000000000 : ℝ)
  | 5 => (758358703 / 1000000000000 : ℝ)
  | 6 => (326466839 / 500000000000 : ℝ)
  | 7 => (546603021 / 1000000000000 : ℝ)
  | 8 => (439367823 / 1000000000000 : ℝ)
  | 9 => (66245847 / 200000000000 : ℝ)
  | 10 => (55547119 / 250000000000 : ℝ)
  | 11 => (11224683 / 100000000000 : ℝ)
  | 12 => (1405647 / 1000000000000 : ℝ)
  | 13 => (-110333657 / 1000000000000 : ℝ)
  | 14 => (-222969601 / 1000000000000 : ℝ)
  | 15 => (-67300127 / 200000000000 : ℝ)
  | 16 => (-450925143 / 1000000000000 : ℝ)
  | 17 => (-283120721 / 500000000000 : ℝ)
  | 18 => (-341223891 / 500000000000 : ℝ)
  | 19 => (-399771171 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch020Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (685918899 / 500000000000 : ℝ)
  | 1 => (317966451 / 250000000000 : ℝ)
  | 2 => (1170982999 / 1000000000000 : ℝ)
  | 3 => (1069190087 / 1000000000000 : ℝ)
  | 4 => (241621959 / 250000000000 : ℝ)
  | 5 => (215719269 / 250000000000 : ℝ)
  | 6 => (47397419 / 62500000000 : ℝ)
  | 7 => (652933679 / 1000000000000 : ℝ)
  | 8 => (273301511 / 500000000000 : ℝ)
  | 9 => (27460489 / 62500000000 : ℝ)
  | 10 => (82807309 / 250000000000 : ℝ)
  | 11 => (222188477 / 1000000000000 : ℝ)
  | 12 => (112246831 / 1000000000000 : ℝ)
  | 13 => (87853 / 62500000000 : ℝ)
  | 14 => (-13791707 / 125000000000 : ℝ)
  | 15 => (-34839 / 156250000 : ℝ)
  | 16 => (-168250317 / 500000000000 : ℝ)
  | 17 => (-225462571 / 500000000000 : ℝ)
  | 18 => (-566241441 / 1000000000000 : ℝ)
  | 19 => (-682447781 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch020Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((400 : ℝ) + (j.val : ℝ)) / 1600)
      (((400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch020Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch020Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((400 : ℝ) + (j.val : ℝ)) / 1600)
    (((400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch020Neg40WeightLower j.val) (hpThetaShiftOneBatch020Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch020Neg40WeightLower, hpThetaShiftOneBatch020Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch020Neg40_integral_bounds :
    (1591740703 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (2275331517 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch020Lower hpThetaJensenCellsBatch020Upper
    hpThetaShiftOneBatch020Neg40WeightLower hpThetaShiftOneBatch020Neg40WeightUpper hpThetaJensenCellsBatch020_bounds hpThetaShiftOneBatch020Neg40_weight_bounds
  have hl : (1591740703 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch020Lower j * hpThetaShiftOneBatch020Neg40WeightLower j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftOneBatch020Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftOneBatch020Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch020Lower j * hpThetaShiftOneBatch020Neg40WeightUpper j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftOneBatch020Neg40WeightUpper j) / 1600) ≤ (2275331517 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftOneBatch020Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (400 : ℝ) / 1600 = 20 / 80 by norm_num,
    show ((400 : ℝ) + 20) / 1600 = (20 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch020Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (14083279261 / 1000000000000 : ℝ)
  | 1 => (2815683633 / 200000000000 : ℝ)
  | 2 => (281458179 / 20000000000 : ℝ)
  | 3 => (3516687129 / 250000000000 : ℝ)
  | 4 => (14059933777 / 1000000000000 : ℝ)
  | 5 => (7026230827 / 500000000000 : ℝ)
  | 6 => (7022164543 / 500000000000 : ℝ)
  | 7 => (7017766509 / 500000000000 : ℝ)
  | 8 => (14026070411 / 1000000000000 : ℝ)
  | 9 => (14015938237 / 1000000000000 : ℝ)
  | 10 => (14005133481 / 1000000000000 : ℝ)
  | 11 => (13993653139 / 1000000000000 : ℝ)
  | 12 => (13981494221 / 1000000000000 : ℝ)
  | 13 => (11174923 / 800000000 : ℝ)
  | 14 => (348878219 / 25000000000 : ℝ)
  | 15 => (139409163 / 10000000000 : ℝ)
  | 16 => (13926013431 / 1000000000000 : ℝ)
  | 17 => (3477604307 / 250000000000 : ℝ)
  | 18 => (13894124779 / 1000000000000 : ℝ)
  | 19 => (108415103 / 7812500000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch020Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (281749907 / 20000000000 : ℝ)
  | 1 => (7041639631 / 500000000000 : ℝ)
  | 2 => (7039209083 / 500000000000 : ℝ)
  | 3 => (14072908951 / 1000000000000 : ℝ)
  | 4 => (14066748517 / 1000000000000 : ℝ)
  | 5 => (7029966889 / 500000000000 : ℝ)
  | 6 => (2810492331 / 200000000000 : ℝ)
  | 7 => (14044329087 / 1000000000000 : ℝ)
  | 8 => (14035533019 / 1000000000000 : ℝ)
  | 9 => (3506517603 / 250000000000 : ℝ)
  | 10 => (7007969119 / 500000000000 : ℝ)
  | 11 => (7002566741 / 500000000000 : ℝ)
  | 12 => (699682657 / 50000000000 : ℝ)
  | 13 => (6990747111 / 500000000000 : ℝ)
  | 14 => (13968653751 / 1000000000000 : ℝ)
  | 15 => (13955128761 / 1000000000000 : ℝ)
  | 16 => (13940916301 / 1000000000000 : ℝ)
  | 17 => (1740751679 / 125000000000 : ℝ)
  | 18 => (13910417229 / 1000000000000 : ℝ)
  | 19 => (694706239 / 50000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch020Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((400 : ℝ) + (j.val : ℝ)) / 1600)
      (((400 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch020Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch020Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((400 : ℝ) + (j.val : ℝ)) / 1600)
    (((400 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch020Neg20WeightLower j.val) (hpThetaShiftOneBatch020Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch020Neg20WeightLower, hpThetaShiftOneBatch020Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch020Neg20_integral_bounds :
    (128181533 / 781250000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (20 / 80 : ℝ) ((20 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (33252047451 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (400 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch020Lower hpThetaJensenCellsBatch020Upper
    hpThetaShiftOneBatch020Neg20WeightLower hpThetaShiftOneBatch020Neg20WeightUpper hpThetaJensenCellsBatch020_bounds hpThetaShiftOneBatch020Neg20_weight_bounds
  have hl : (128181533 / 781250000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch020Lower j * hpThetaShiftOneBatch020Neg20WeightLower j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftOneBatch020Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftOneBatch020Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch020Lower j * hpThetaShiftOneBatch020Neg20WeightUpper j)
        (hpThetaJensenCellsBatch020Upper j * hpThetaShiftOneBatch020Neg20WeightUpper j) / 1600) ≤ (33252047451 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch020Lower, hpThetaJensenCellsBatch020Upper,
      hpThetaShiftOneBatch020Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (400 : ℝ) / 1600 = 20 / 80 by norm_num,
    show ((400 : ℝ) + 20) / 1600 = (20 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch020Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch020Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch020Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch020Neg20_integral_bounds
end HodgeProofHP
