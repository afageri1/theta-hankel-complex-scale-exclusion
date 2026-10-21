/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch019

/-! Exact signed weight and batch integral certificates, batch 19 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch019Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-12604536093 / 1000000000000 : ℝ)
  | 1 => (-12710637329 / 1000000000000 : ℝ)
  | 2 => (-3203980071 / 250000000000 : ℝ)
  | 3 => (-2584071607 / 200000000000 : ℝ)
  | 4 => (-1627990433 / 125000000000 : ℝ)
  | 5 => (-13126589263 / 1000000000000 : ℝ)
  | 6 => (-1653540991 / 125000000000 : ℝ)
  | 7 => (-13329111767 / 1000000000000 : ℝ)
  | 8 => (-13428912897 / 1000000000000 : ℝ)
  | 9 => (-13527703247 / 1000000000000 : ℝ)
  | 10 => (-85159091 / 6250000000 : ℝ)
  | 11 => (-1715267299 / 125000000000 : ℝ)
  | 12 => (-6908863057 / 500000000000 : ℝ)
  | 13 => (-3478047229 / 250000000000 : ℝ)
  | 14 => (-3501374451 / 250000000000 : ℝ)
  | 15 => (-14097623607 / 1000000000000 : ℝ)
  | 16 => (-14188536973 / 1000000000000 : ℝ)
  | 17 => (-7139104187 / 500000000000 : ℝ)
  | 18 => (-1795826013 / 125000000000 : ℝ)
  | 19 => (-903356643 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch019Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-124976433 / 10000000000 : ℝ)
  | 1 => (-3151134023 / 250000000000 : ℝ)
  | 2 => (-794414833 / 62500000000 : ℝ)
  | 3 => (-12815920283 / 1000000000000 : ℝ)
  | 4 => (-6460179017 / 500000000000 : ℝ)
  | 5 => (-13023923463 / 1000000000000 : ℝ)
  | 6 => (-6563294631 / 500000000000 : ℝ)
  | 7 => (-13228327927 / 1000000000000 : ℝ)
  | 8 => (-6664555883 / 500000000000 : ℝ)
  | 9 => (-52456691 / 3906250000 : ℝ)
  | 10 => (-6763851623 / 500000000000 : ℝ)
  | 11 => (-13625454559 / 1000000000000 : ℝ)
  | 12 => (-13722138391 / 1000000000000 : ℝ)
  | 13 => (-13817726113 / 1000000000000 : ℝ)
  | 14 => (-2782437783 / 200000000000 : ℝ)
  | 15 => (-14005497803 / 1000000000000 : ℝ)
  | 16 => (-7048811803 / 500000000000 : ℝ)
  | 17 => (-3547134243 / 250000000000 : ℝ)
  | 18 => (-14278208373 / 1000000000000 : ℝ)
  | 19 => (-14366608103 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch019Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((380 : ℝ) + (j.val : ℝ)) / 1600)
      (((380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch019Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch019Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((380 : ℝ) + (j.val : ℝ)) / 1600)
    (((380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch019Neg100WeightLower j.val) (hpThetaShiftOneBatch019Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch019Neg100WeightLower, hpThetaShiftOneBatch019Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch019Neg100_integral_bounds :
    (-171229709347 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-5247012219 / 31250000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch019Lower hpThetaJensenCellsBatch019Upper
    hpThetaShiftOneBatch019Neg100WeightLower hpThetaShiftOneBatch019Neg100WeightUpper hpThetaJensenCellsBatch019_bounds hpThetaShiftOneBatch019Neg100_weight_bounds
  have hl : (-171229709347 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch019Lower j * hpThetaShiftOneBatch019Neg100WeightLower j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftOneBatch019Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftOneBatch019Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch019Lower j * hpThetaShiftOneBatch019Neg100WeightUpper j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftOneBatch019Neg100WeightUpper j) / 1600) ≤ (-5247012219 / 31250000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftOneBatch019Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (380 : ℝ) / 1600 = 19 / 80 by norm_num,
    show ((380 : ℝ) + 20) / 1600 = (19 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch019Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6329264221 / 1000000000000 : ℝ)
  | 1 => (-6461493811 / 1000000000000 : ℝ)
  | 2 => (-3297157573 / 500000000000 : ℝ)
  | 3 => (-3363859591 / 500000000000 : ℝ)
  | 4 => (-214428023 / 31250000000 : ℝ)
  | 5 => (-6996238491 / 1000000000000 : ℝ)
  | 6 => (-1426266999 / 200000000000 : ℝ)
  | 7 => (-7266976659 / 1000000000000 : ℝ)
  | 8 => (-1850788439 / 250000000000 : ℝ)
  | 9 => (-942482053 / 125000000000 : ℝ)
  | 10 => (-7677074663 / 1000000000000 : ℝ)
  | 11 => (-7814798337 / 1000000000000 : ℝ)
  | 12 => (-7953017171 / 1000000000000 : ℝ)
  | 13 => (-8091720753 / 1000000000000 : ℝ)
  | 14 => (-8230898533 / 1000000000000 : ℝ)
  | 15 => (-4185269911 / 500000000000 : ℝ)
  | 16 => (-4255316897 / 500000000000 : ℝ)
  | 17 => (-4325584741 / 500000000000 : ℝ)
  | 18 => (-8792135783 / 1000000000000 : ℝ)
  | 19 => (-8933521453 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch019Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-774704411 / 125000000000 : ℝ)
  | 1 => (-316463211 / 50000000000 : ℝ)
  | 2 => (-646149381 / 100000000000 : ℝ)
  | 3 => (-1318863029 / 200000000000 : ℝ)
  | 4 => (-6727719181 / 1000000000000 : ℝ)
  | 5 => (-1372339347 / 200000000000 : ℝ)
  | 6 => (-699623849 / 100000000000 : ℝ)
  | 7 => (-3565667497 / 500000000000 : ℝ)
  | 8 => (-3633488329 / 500000000000 : ℝ)
  | 9 => (-1480630751 / 200000000000 : ℝ)
  | 10 => (-7539856423 / 1000000000000 : ℝ)
  | 11 => (-3838537331 / 500000000000 : ℝ)
  | 12 => (-7631639 / 976562500 : ℝ)
  | 13 => (-795301717 / 100000000000 : ℝ)
  | 14 => (-505732547 / 62500000000 : ℝ)
  | 15 => (-2057724633 / 250000000000 : ℝ)
  | 16 => (-8370539821 / 1000000000000 : ℝ)
  | 17 => (-8510633793 / 1000000000000 : ℝ)
  | 18 => (-8651169481 / 1000000000000 : ℝ)
  | 19 => (-4396067891 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch019Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((380 : ℝ) + (j.val : ℝ)) / 1600)
      (((380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch019Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch019Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((380 : ℝ) + (j.val : ℝ)) / 1600)
    (((380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch019Neg65WeightLower j.val) (hpThetaShiftOneBatch019Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch019Neg65WeightLower, hpThetaShiftOneBatch019Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch019Neg65_integral_bounds :
    (-96082492413 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-46597613873 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch019Lower hpThetaJensenCellsBatch019Upper
    hpThetaShiftOneBatch019Neg65WeightLower hpThetaShiftOneBatch019Neg65WeightUpper hpThetaJensenCellsBatch019_bounds hpThetaShiftOneBatch019Neg65_weight_bounds
  have hl : (-96082492413 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch019Lower j * hpThetaShiftOneBatch019Neg65WeightLower j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftOneBatch019Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftOneBatch019Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch019Lower j * hpThetaShiftOneBatch019Neg65WeightUpper j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftOneBatch019Neg65WeightUpper j) / 1600) ≤ (-46597613873 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftOneBatch019Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (380 : ℝ) / 1600 = 19 / 80 by norm_num,
    show ((380 : ℝ) + 20) / 1600 = (19 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch019Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1548883093 / 500000000000 : ℝ)
  | 1 => (94223491 / 31250000000 : ℝ)
  | 2 => (366453079 / 125000000000 : ℝ)
  | 3 => (2847184509 / 1000000000000 : ℝ)
  | 4 => (2761830963 / 1000000000000 : ℝ)
  | 5 => (2675563673 / 1000000000000 : ℝ)
  | 6 => (1294191187 / 500000000000 : ℝ)
  | 7 => (125014343 / 50000000000 : ℝ)
  | 8 => (301409623 / 125000000000 : ℝ)
  | 9 => (2321352657 / 1000000000000 : ℝ)
  | 10 => (44610277 / 20000000000 : ℝ)
  | 11 => (2138760593 / 1000000000000 : ℝ)
  | 12 => (81843719 / 40000000000 : ℝ)
  | 13 => (1952511147 / 1000000000000 : ℝ)
  | 14 => (1858015319 / 1000000000000 : ℝ)
  | 15 => (1762605761 / 1000000000000 : ℝ)
  | 16 => (833141403 / 500000000000 : ℝ)
  | 17 => (784523423 / 500000000000 : ℝ)
  | 18 => (735449169 / 500000000000 : ℝ)
  | 19 => (1371837797 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch019Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (794867137 / 250000000000 : ℝ)
  | 1 => (3097766187 / 1000000000000 : ℝ)
  | 2 => (3015151713 / 1000000000000 : ℝ)
  | 3 => (2931624633 / 1000000000000 : ℝ)
  | 4 => (284718451 / 100000000000 : ℝ)
  | 5 => (690457741 / 250000000000 : ℝ)
  | 6 => (1337781837 / 500000000000 : ℝ)
  | 7 => (20707059 / 8000000000 : ℝ)
  | 8 => (2500286861 / 1000000000000 : ℝ)
  | 9 => (482255397 / 200000000000 : ℝ)
  | 10 => (1160676329 / 500000000000 : ℝ)
  | 11 => (2230513851 / 1000000000000 : ℝ)
  | 12 => (1069380297 / 500000000000 : ℝ)
  | 13 => (127880811 / 62500000000 : ℝ)
  | 14 => (488127787 / 250000000000 : ℝ)
  | 15 => (46450383 / 25000000000 : ℝ)
  | 16 => (881302881 / 500000000000 : ℝ)
  | 17 => (1666282807 / 1000000000000 : ℝ)
  | 18 => (1569046847 / 1000000000000 : ℝ)
  | 19 => (1470898339 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch019Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((380 : ℝ) + (j.val : ℝ)) / 1600)
      (((380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch019Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch019Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((380 : ℝ) + (j.val : ℝ)) / 1600)
    (((380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch019Neg40WeightLower j.val) (hpThetaShiftOneBatch019Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch019Neg40WeightLower, hpThetaShiftOneBatch019Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch019Neg40_integral_bounds :
    (2833631487 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (745735027 / 25000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch019Lower hpThetaJensenCellsBatch019Upper
    hpThetaShiftOneBatch019Neg40WeightLower hpThetaShiftOneBatch019Neg40WeightUpper hpThetaJensenCellsBatch019_bounds hpThetaShiftOneBatch019Neg40_weight_bounds
  have hl : (2833631487 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch019Lower j * hpThetaShiftOneBatch019Neg40WeightLower j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftOneBatch019Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftOneBatch019Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch019Lower j * hpThetaShiftOneBatch019Neg40WeightUpper j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftOneBatch019Neg40WeightUpper j) / 1600) ≤ (745735027 / 25000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftOneBatch019Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (380 : ℝ) / 1600 = 19 / 80 by norm_num,
    show ((380 : ℝ) + 20) / 1600 = (19 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch019Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (7020626507 / 500000000000 : ℝ)
  | 1 => (7024633577 / 500000000000 : ℝ)
  | 2 => (1405670073 / 100000000000 : ℝ)
  | 3 => (14063550429 / 1000000000000 : ℝ)
  | 4 => (14069812943 / 1000000000000 : ℝ)
  | 5 => (14075484977 / 1000000000000 : ℝ)
  | 6 => (14080563243 / 1000000000000 : ℝ)
  | 7 => (14085044461 / 1000000000000 : ℝ)
  | 8 => (2817785073 / 200000000000 : ℝ)
  | 9 => (7046101347 / 500000000000 : ℝ)
  | 10 => (35237183 / 2500000000 : ℝ)
  | 11 => (7048466821 / 500000000000 : ℝ)
  | 12 => (1762297599 / 125000000000 : ℝ)
  | 13 => (14099211431 / 1000000000000 : ℝ)
  | 14 => (3524752587 / 250000000000 : ℝ)
  | 15 => (176224653 / 12500000000 : ℝ)
  | 16 => (14096304847 / 1000000000000 : ℝ)
  | 17 => (14094005003 / 1000000000000 : ℝ)
  | 18 => (880691847 / 62500000000 : ℝ)
  | 19 => (14087495349 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch019Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2809853431 / 200000000000 : ℝ)
  | 1 => (14056700731 / 1000000000000 : ℝ)
  | 2 => (1406355043 / 100000000000 : ℝ)
  | 3 => (879363309 / 62500000000 : ℝ)
  | 4 => (7037742489 / 500000000000 : ℝ)
  | 5 => (3520140811 / 250000000000 : ℝ)
  | 6 => (7042522231 / 500000000000 : ℝ)
  | 7 => (7044462683 / 500000000000 : ℝ)
  | 8 => (2818440539 / 200000000000 : ℝ)
  | 9 => (14094873201 / 1000000000000 : ℝ)
  | 10 => (14096933643 / 1000000000000 : ℝ)
  | 11 => (14098380793 / 1000000000000 : ℝ)
  | 12 => (1762401429 / 125000000000 : ℝ)
  | 13 => (14099436229 / 1000000000000 : ℝ)
  | 14 => (281988447 / 20000000000 : ℝ)
  | 15 => (14099010349 / 1000000000000 : ℝ)
  | 16 => (14097972241 / 1000000000000 : ℝ)
  | 17 => (881019053 / 62500000000 : ℝ)
  | 18 => (3523501251 / 250000000000 : ℝ)
  | 19 => (14091069553 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch019Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((380 : ℝ) + (j.val : ℝ)) / 1600)
      (((380 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch019Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch019Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((380 : ℝ) + (j.val : ℝ)) / 1600)
    (((380 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch019Neg20WeightLower j.val) (hpThetaShiftOneBatch019Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch019Neg20WeightLower, hpThetaShiftOneBatch019Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch019Neg20_integral_bounds :
    (175784613607 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (19 / 80 : ℝ) ((19 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (35603003317 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (380 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch019Lower hpThetaJensenCellsBatch019Upper
    hpThetaShiftOneBatch019Neg20WeightLower hpThetaShiftOneBatch019Neg20WeightUpper hpThetaJensenCellsBatch019_bounds hpThetaShiftOneBatch019Neg20_weight_bounds
  have hl : (175784613607 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch019Lower j * hpThetaShiftOneBatch019Neg20WeightLower j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftOneBatch019Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftOneBatch019Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch019Lower j * hpThetaShiftOneBatch019Neg20WeightUpper j)
        (hpThetaJensenCellsBatch019Upper j * hpThetaShiftOneBatch019Neg20WeightUpper j) / 1600) ≤ (35603003317 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch019Lower, hpThetaJensenCellsBatch019Upper,
      hpThetaShiftOneBatch019Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (380 : ℝ) / 1600 = 19 / 80 by norm_num,
    show ((380 : ℝ) + 20) / 1600 = (19 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch019Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch019Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch019Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch019Neg20_integral_bounds
end HodgeProofHP
