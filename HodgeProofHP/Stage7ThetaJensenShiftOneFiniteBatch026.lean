/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch026

/-! Exact signed weight and batch integral certificates, batch 26 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch026Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5588134857 / 1000000000000 : ℝ)
  | 1 => (-5268388139 / 1000000000000 : ℝ)
  | 2 => (-4943260697 / 1000000000000 : ℝ)
  | 3 => (-2306363141 / 500000000000 : ℝ)
  | 4 => (-855351801 / 200000000000 : ℝ)
  | 5 => (-1967666671 / 500000000000 : ℝ)
  | 6 => (-3588424143 / 1000000000000 : ℝ)
  | 7 => (-40450083 / 12500000000 : ℝ)
  | 8 => (-575611291 / 200000000000 : ℝ)
  | 9 => (-314318701 / 125000000000 : ℝ)
  | 10 => (-2145462523 / 1000000000000 : ℝ)
  | 11 => (-1770772039 / 1000000000000 : ℝ)
  | 12 => (-1390455417 / 1000000000000 : ℝ)
  | 13 => (-251122587 / 250000000000 : ℝ)
  | 14 => (-612854959 / 1000000000000 : ℝ)
  | 15 => (-53881957 / 250000000000 : ℝ)
  | 16 => (11719501 / 62500000000 : ℝ)
  | 17 => (596285079 / 1000000000000 : ℝ)
  | 18 => (1974241 / 1953125000 : ℝ)
  | 19 => (143111051 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch026Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2634194069 / 500000000000 : ℝ)
  | 1 => (-617907587 / 125000000000 : ℝ)
  | 2 => (-4612726281 / 1000000000000 : ℝ)
  | 3 => (-1069189751 / 250000000000 : ℝ)
  | 4 => (-3935333341 / 1000000000000 : ℝ)
  | 5 => (-1794212071 / 500000000000 : ℝ)
  | 6 => (-3236006639 / 1000000000000 : ℝ)
  | 7 => (-1439028227 / 500000000000 : ℝ)
  | 8 => (-2514549607 / 1000000000000 : ℝ)
  | 9 => (-1072731261 / 500000000000 : ℝ)
  | 10 => (-885386019 / 500000000000 : ℝ)
  | 11 => (-173806927 / 125000000000 : ℝ)
  | 12 => (-1004490347 / 1000000000000 : ℝ)
  | 13 => (-306427479 / 500000000000 : ℝ)
  | 14 => (-215527827 / 1000000000000 : ℝ)
  | 15 => (187512017 / 1000000000000 : ℝ)
  | 16 => (14907127 / 25000000000 : ℝ)
  | 17 => (1010811393 / 1000000000000 : ℝ)
  | 18 => (1431110511 / 1000000000000 : ℝ)
  | 19 => (1857201497 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch026Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((520 : ℝ) + (j.val : ℝ)) / 1600)
      (((520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch026Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch026Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((520 : ℝ) + (j.val : ℝ)) / 1600)
    (((520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch026Neg100WeightLower j.val) (hpThetaShiftOneBatch026Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch026Neg100WeightLower, hpThetaShiftOneBatch026Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch026Neg100_integral_bounds :
    (-8622561389 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-14219670837 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch026Lower hpThetaJensenCellsBatch026Upper
    hpThetaShiftOneBatch026Neg100WeightLower hpThetaShiftOneBatch026Neg100WeightUpper hpThetaJensenCellsBatch026_bounds hpThetaShiftOneBatch026Neg100_weight_bounds
  have hl : (-8622561389 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch026Lower j * hpThetaShiftOneBatch026Neg100WeightLower j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftOneBatch026Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftOneBatch026Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch026Lower j * hpThetaShiftOneBatch026Neg100WeightUpper j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftOneBatch026Neg100WeightUpper j) / 1600) ≤ (-14219670837 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftOneBatch026Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (520 : ℝ) / 1600 = 26 / 80 by norm_num,
    show ((520 : ℝ) + 20) / 1600 = (26 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch026Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4885292541 / 200000000000 : ℝ)
  | 1 => (-4898360953 / 200000000000 : ℝ)
  | 2 => (-1534697037 / 62500000000 : ℝ)
  | 3 => (-12308239657 / 500000000000 : ℝ)
  | 4 => (-12337878989 / 500000000000 : ℝ)
  | 5 => (-24732961547 / 1000000000000 : ℝ)
  | 6 => (-24788062909 / 1000000000000 : ℝ)
  | 7 => (-24841034869 / 1000000000000 : ℝ)
  | 8 => (-311148127 / 12500000000 : ℝ)
  | 9 => (-6235120359 / 250000000000 : ℝ)
  | 10 => (-156168133 / 6250000000 : ℝ)
  | 11 => (-25031082199 / 1000000000000 : ℝ)
  | 12 => (-3134124579 / 125000000000 : ℝ)
  | 13 => (-12556308473 / 500000000000 : ℝ)
  | 14 => (-25149915441 / 1000000000000 : ℝ)
  | 15 => (-503697287 / 20000000000 : ℝ)
  | 16 => (-25217435839 / 1000000000000 : ℝ)
  | 17 => (-25247602013 / 1000000000000 : ℝ)
  | 18 => (-98731777 / 3906250000 : ℝ)
  | 19 => (-25300606517 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch026Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-60897883 / 2500000000 : ℝ)
  | 1 => (-1526653919 / 62500000000 : ℝ)
  | 2 => (-6122951191 / 250000000000 : ℝ)
  | 3 => (-24555152591 / 1000000000000 : ℝ)
  | 4 => (-24616479313 / 1000000000000 : ℝ)
  | 5 => (-24675757977 / 1000000000000 : ℝ)
  | 6 => (-12366480773 / 500000000000 : ℝ)
  | 7 => (-6197015727 / 250000000000 : ℝ)
  | 8 => (-6210258717 / 250000000000 : ℝ)
  | 9 => (-24891850159 / 1000000000000 : ℝ)
  | 10 => (-4988096287 / 200000000000 : ℝ)
  | 11 => (-24986901279 / 1000000000000 : ℝ)
  | 12 => (-12515541099 / 500000000000 : ℝ)
  | 13 => (-25072996631 / 1000000000000 : ℝ)
  | 14 => (-5022523389 / 200000000000 : ℝ)
  | 15 => (-314373943 / 12500000000 : ℝ)
  | 16 => (-25184864349 / 1000000000000 : ℝ)
  | 17 => (-12608717919 / 500000000000 : ℝ)
  | 18 => (-6311900503 / 250000000000 : ℝ)
  | 19 => (-25275334911 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch026Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((520 : ℝ) + (j.val : ℝ)) / 1600)
      (((520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch026Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch026Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((520 : ℝ) + (j.val : ℝ)) / 1600)
    (((520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch026Neg65WeightLower j.val) (hpThetaShiftOneBatch026Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch026Neg65WeightLower, hpThetaShiftOneBatch026Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch026Neg65_integral_bounds :
    (-187356444323 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-92249067849 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch026Lower hpThetaJensenCellsBatch026Upper
    hpThetaShiftOneBatch026Neg65WeightLower hpThetaShiftOneBatch026Neg65WeightUpper hpThetaJensenCellsBatch026_bounds hpThetaShiftOneBatch026Neg65_weight_bounds
  have hl : (-187356444323 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch026Lower j * hpThetaShiftOneBatch026Neg65WeightLower j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftOneBatch026Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftOneBatch026Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch026Lower j * hpThetaShiftOneBatch026Neg65WeightUpper j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftOneBatch026Neg65WeightUpper j) / 1600) ≤ (-92249067849 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftOneBatch026Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (520 : ℝ) / 1600 = 26 / 80 by norm_num,
    show ((520 : ℝ) + 20) / 1600 = (26 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch026Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-16543134409 / 1000000000000 : ℝ)
  | 1 => (-8363866953 / 500000000000 : ℝ)
  | 2 => (-16912626401 / 1000000000000 : ℝ)
  | 3 => (-683912073 / 40000000000 : ℝ)
  | 4 => (-864162501 / 50000000000 : ℝ)
  | 5 => (-17468960743 / 1000000000000 : ℝ)
  | 6 => (-17654923661 / 1000000000000 : ℝ)
  | 7 => (-8920564179 / 500000000000 : ℝ)
  | 8 => (-2253445541 / 125000000000 : ℝ)
  | 9 => (-18214220981 / 1000000000000 : ℝ)
  | 10 => (-18401087639 / 1000000000000 : ℝ)
  | 11 => (-3717630707 / 200000000000 : ℝ)
  | 12 => (-18775407819 / 1000000000000 : ℝ)
  | 13 => (-18962839551 / 1000000000000 : ℝ)
  | 14 => (-3830087541 / 200000000000 : ℝ)
  | 15 => (-302159237 / 15625000000 : ℝ)
  | 16 => (-19526088741 / 1000000000000 : ℝ)
  | 17 => (-616066223 / 31250000000 : ℝ)
  | 18 => (-995113549 / 50000000000 : ℝ)
  | 19 => (-5022633203 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch026Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2044854737 / 125000000000 : ℝ)
  | 1 => (-2067891801 / 125000000000 : ℝ)
  | 2 => (-3345546781 / 200000000000 : ℝ)
  | 3 => (-21140783 / 1250000000 : ℝ)
  | 4 => (-534306307 / 31250000000 : ℝ)
  | 5 => (-17283250019 / 1000000000000 : ℝ)
  | 6 => (-8734480371 / 500000000000 : ℝ)
  | 7 => (-882746183 / 50000000000 : ℝ)
  | 8 => (-17841128357 / 1000000000000 : ℝ)
  | 9 => (-18027564327 / 1000000000000 : ℝ)
  | 10 => (-910711049 / 50000000000 : ℝ)
  | 11 => (-9200543819 / 500000000000 : ℝ)
  | 12 => (-9294076767 / 500000000000 : ℝ)
  | 13 => (-9387703909 / 500000000000 : ℝ)
  | 14 => (-379256791 / 20000000000 : ℝ)
  | 15 => (-2393804713 / 125000000000 : ℝ)
  | 16 => (-19338191167 / 1000000000000 : ℝ)
  | 17 => (-976304437 / 50000000000 : ℝ)
  | 18 => (-3942823827 / 200000000000 : ℝ)
  | 19 => (-19902270979 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch026Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((520 : ℝ) + (j.val : ℝ)) / 1600)
      (((520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch026Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch026Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((520 : ℝ) + (j.val : ℝ)) / 1600)
    (((520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch026Neg40WeightLower j.val) (hpThetaShiftOneBatch026Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch026Neg40WeightLower, hpThetaShiftOneBatch026Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch026Neg40_integral_bounds :
    (-17182727461 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-134238517843 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch026Lower hpThetaJensenCellsBatch026Upper
    hpThetaShiftOneBatch026Neg40WeightLower hpThetaShiftOneBatch026Neg40WeightUpper hpThetaJensenCellsBatch026_bounds hpThetaShiftOneBatch026Neg40_weight_bounds
  have hl : (-17182727461 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch026Lower j * hpThetaShiftOneBatch026Neg40WeightLower j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftOneBatch026Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftOneBatch026Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch026Lower j * hpThetaShiftOneBatch026Neg40WeightUpper j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftOneBatch026Neg40WeightUpper j) / 1600) ≤ (-134238517843 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftOneBatch026Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (520 : ℝ) / 1600 = 26 / 80 by norm_num,
    show ((520 : ℝ) + 20) / 1600 = (26 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch026Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1015150903 / 125000000000 : ℝ)
  | 1 => (8020732039 / 1000000000000 : ℝ)
  | 2 => (1979838713 / 250000000000 : ℝ)
  | 3 => (156341497 / 20000000000 : ℝ)
  | 4 => (3856945621 / 500000000000 : ℝ)
  | 5 => (7609803267 / 1000000000000 : ℝ)
  | 6 => (7504810189 / 1000000000000 : ℝ)
  | 7 => (73989113 / 10000000000 : ℝ)
  | 8 => (7292105917 / 1000000000000 : ℝ)
  | 9 => (7184393387 / 1000000000000 : ℝ)
  | 10 => (7075773081 / 1000000000000 : ℝ)
  | 11 => (6966244399 / 1000000000000 : ℝ)
  | 12 => (428487923 / 62500000000 : ℝ)
  | 13 => (6744459643 / 1000000000000 : ℝ)
  | 14 => (3316101253 / 500000000000 : ℝ)
  | 15 => (6519034867 / 1000000000000 : ℝ)
  | 16 => (6404956263 / 1000000000000 : ℝ)
  | 17 => (6289966261 / 1000000000000 : ℝ)
  | 18 => (3087032227 / 500000000000 : ℝ)
  | 19 => (189289077 / 31250000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch026Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (52613 / 6400000 : ℝ)
  | 1 => (324848289 / 40000000000 : ℝ)
  | 2 => (200518301 / 25000000000 : ℝ)
  | 3 => (7919354853 / 1000000000000 : ℝ)
  | 4 => (7817074851 / 1000000000000 : ℝ)
  | 5 => (7713891243 / 1000000000000 : ℝ)
  | 6 => (1902450817 / 250000000000 : ℝ)
  | 7 => (750481019 / 100000000000 : ℝ)
  | 8 => (7398911301 / 1000000000000 : ℝ)
  | 9 => (3646052959 / 500000000000 : ℝ)
  | 10 => (1796098347 / 250000000000 : ℝ)
  | 11 => (3537886541 / 500000000000 : ℝ)
  | 12 => (17415611 / 2500000000 : ℝ)
  | 13 => (6855806769 / 1000000000000 : ℝ)
  | 14 => (1686114911 / 250000000000 : ℝ)
  | 15 => (6632202507 / 1000000000000 : ℝ)
  | 16 => (1629758717 / 250000000000 : ℝ)
  | 17 => (800619533 / 125000000000 : ℝ)
  | 18 => (3144983131 / 500000000000 : ℝ)
  | 19 => (1234812891 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch026Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((520 : ℝ) + (j.val : ℝ)) / 1600)
      (((520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch026Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch026Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((520 : ℝ) + (j.val : ℝ)) / 1600)
    (((520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch026Neg20WeightLower j.val) (hpThetaShiftOneBatch026Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch026Neg20WeightLower, hpThetaShiftOneBatch026Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch026Neg20_integral_bounds :
    (6611909131 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (26 / 80 : ℝ) ((26 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (54424616429 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch026Lower hpThetaJensenCellsBatch026Upper
    hpThetaShiftOneBatch026Neg20WeightLower hpThetaShiftOneBatch026Neg20WeightUpper hpThetaJensenCellsBatch026_bounds hpThetaShiftOneBatch026Neg20_weight_bounds
  have hl : (6611909131 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch026Lower j * hpThetaShiftOneBatch026Neg20WeightLower j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftOneBatch026Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftOneBatch026Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch026Lower j * hpThetaShiftOneBatch026Neg20WeightUpper j)
        (hpThetaJensenCellsBatch026Upper j * hpThetaShiftOneBatch026Neg20WeightUpper j) / 1600) ≤ (54424616429 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch026Lower, hpThetaJensenCellsBatch026Upper,
      hpThetaShiftOneBatch026Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (520 : ℝ) / 1600 = 26 / 80 by norm_num,
    show ((520 : ℝ) + 20) / 1600 = (26 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch026Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch026Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch026Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch026Neg20_integral_bounds
end HodgeProofHP
