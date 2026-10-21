/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch041

/-! Exact signed weight and batch integral certificates, batch 41 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch041Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (10108772451 / 100000000000 : ℝ)
  | 1 => (49202781147 / 500000000000 : ℝ)
  | 2 => (5978596179 / 62500000000 : ℝ)
  | 3 => (23210705253 / 250000000000 : ℝ)
  | 4 => (22490142097 / 250000000000 : ℝ)
  | 5 => (87009933461 / 1000000000000 : ℝ)
  | 6 => (83990061471 / 1000000000000 : ℝ)
  | 7 => (80900090391 / 1000000000000 : ℝ)
  | 8 => (38869575439 / 500000000000 : ℝ)
  | 9 => (74506366233 / 1000000000000 : ℝ)
  | 10 => (14240170471 / 200000000000 : ℝ)
  | 11 => (67821717699 / 1000000000000 : ℝ)
  | 12 => (2574722529 / 40000000000 : ℝ)
  | 13 => (15209745591 / 250000000000 : ℝ)
  | 14 => (14308390241 / 250000000000 : ℝ)
  | 15 => (836732457 / 15625000000 : ℝ)
  | 16 => (12447500443 / 250000000000 : ℝ)
  | 17 => (45949997373 / 1000000000000 : ℝ)
  | 18 => (4202991913 / 100000000000 : ℝ)
  | 19 => (7605762863 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch041Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (103704851627 / 1000000000000 : ℝ)
  | 1 => (101087724511 / 1000000000000 : ℝ)
  | 2 => (19681112459 / 200000000000 : ℝ)
  | 3 => (19131507773 / 200000000000 : ℝ)
  | 4 => (92842821013 / 1000000000000 : ℝ)
  | 5 => (89960568389 / 1000000000000 : ℝ)
  | 6 => (43504966731 / 500000000000 : ℝ)
  | 7 => (2624689421 / 31250000000 : ℝ)
  | 8 => (10112511299 / 125000000000 : ℝ)
  | 9 => (77739150879 / 1000000000000 : ℝ)
  | 10 => (37253183117 / 500000000000 : ℝ)
  | 11 => (17800213089 / 250000000000 : ℝ)
  | 12 => (678217177 / 10000000000 : ℝ)
  | 13 => (32184031613 / 500000000000 : ℝ)
  | 14 => (12167796473 / 200000000000 : ℝ)
  | 15 => (11446712193 / 200000000000 : ℝ)
  | 16 => (53550877249 / 1000000000000 : ℝ)
  | 17 => (49790001773 / 1000000000000 : ℝ)
  | 18 => (22974998687 / 500000000000 : ℝ)
  | 19 => (42029919131 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch041Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((820 : ℝ) + (j.val : ℝ)) / 1600)
      (((820 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch041Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch041Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((820 : ℝ) + (j.val : ℝ)) / 1600)
    (((820 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch041Neg100WeightLower j.val) (hpThetaShiftOneBatch041Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch041Neg100WeightLower, hpThetaShiftOneBatch041Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch041Neg100_integral_bounds :
    (43042501789 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (91480077087 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (820 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch041Lower hpThetaJensenCellsBatch041Upper
    hpThetaShiftOneBatch041Neg100WeightLower hpThetaShiftOneBatch041Neg100WeightUpper hpThetaJensenCellsBatch041_bounds hpThetaShiftOneBatch041Neg100_weight_bounds
  have hl : (43042501789 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch041Lower j * hpThetaShiftOneBatch041Neg100WeightLower j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftOneBatch041Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftOneBatch041Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch041Lower j * hpThetaShiftOneBatch041Neg100WeightUpper j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftOneBatch041Neg100WeightUpper j) / 1600) ≤ (91480077087 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftOneBatch041Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (820 : ℝ) / 1600 = 41 / 80 by norm_num,
    show ((820 : ℝ) + 20) / 1600 = (41 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch041Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (36552863359 / 250000000000 : ℝ)
  | 1 => (147477863671 / 1000000000000 : ℝ)
  | 2 => (5949805939 / 40000000000 : ℝ)
  | 3 => (150013199341 / 1000000000000 : ℝ)
  | 4 => (151281906313 / 1000000000000 : ℝ)
  | 5 => (152551157977 / 1000000000000 : ℝ)
  | 6 => (153820841451 / 1000000000000 : ℝ)
  | 7 => (1240726739 / 8000000000 : ℝ)
  | 8 => (156361044899 / 1000000000000 : ℝ)
  | 9 => (157631331671 / 1000000000000 : ℝ)
  | 10 => (158901583829 / 1000000000000 : ℝ)
  | 11 => (16017168099 / 100000000000 : ℝ)
  | 12 => (161441501239 / 1000000000000 : ℝ)
  | 13 => (162710921113 / 1000000000000 : ℝ)
  | 14 => (163979815601 / 1000000000000 : ℝ)
  | 15 => (4131201453 / 25000000000 : ℝ)
  | 16 => (33303104103 / 200000000000 : ℝ)
  | 17 => (167782073043 / 1000000000000 : ℝ)
  | 18 => (169047584359 / 1000000000000 : ℝ)
  | 19 => (21288990189 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch041Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (18434732959 / 125000000000 : ℝ)
  | 1 => (37186287119 / 250000000000 : ℝ)
  | 2 => (75006599671 / 500000000000 : ℝ)
  | 3 => (75640953157 / 500000000000 : ℝ)
  | 4 => (76275578989 / 500000000000 : ℝ)
  | 5 => (38455210363 / 250000000000 : ℝ)
  | 6 => (19386355297 / 125000000000 : ℝ)
  | 7 => (1563610449 / 10000000000 : ℝ)
  | 8 => (19703916459 / 125000000000 : ℝ)
  | 9 => (15890158383 / 100000000000 : ℝ)
  | 10 => (160171680991 / 1000000000000 : ℝ)
  | 11 => (4036037531 / 25000000000 : ℝ)
  | 12 => (81355460557 / 500000000000 : ℝ)
  | 13 => (81989907801 / 500000000000 : ℝ)
  | 14 => (165248058121 / 1000000000000 : ℝ)
  | 15 => (41628880129 / 250000000000 : ℝ)
  | 16 => (41945518261 / 250000000000 : ℝ)
  | 17 => (4226189609 / 25000000000 : ℝ)
  | 18 => (170311921513 / 1000000000000 : ℝ)
  | 19 => (171574949929 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch041Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((820 : ℝ) + (j.val : ℝ)) / 1600)
      (((820 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch041Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch041Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((820 : ℝ) + (j.val : ℝ)) / 1600)
    (((820 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch041Neg65WeightLower j.val) (hpThetaShiftOneBatch041Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch041Neg65WeightLower, hpThetaShiftOneBatch041Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch041Neg65_integral_bounds :
    (23430660641 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (38429712613 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (820 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch041Lower hpThetaJensenCellsBatch041Upper
    hpThetaShiftOneBatch041Neg65WeightLower hpThetaShiftOneBatch041Neg65WeightUpper hpThetaJensenCellsBatch041_bounds hpThetaShiftOneBatch041Neg65_weight_bounds
  have hl : (23430660641 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch041Lower j * hpThetaShiftOneBatch041Neg65WeightLower j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftOneBatch041Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftOneBatch041Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch041Lower j * hpThetaShiftOneBatch041Neg65WeightUpper j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftOneBatch041Neg65WeightUpper j) / 1600) ≤ (38429712613 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftOneBatch041Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (820 : ℝ) / 1600 = 41 / 80 by norm_num,
    show ((820 : ℝ) + 20) / 1600 = (41 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch041Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3011300049 / 200000000000 : ℝ)
  | 1 => (-728210567 / 50000000000 : ℝ)
  | 2 => (-7033294289 / 500000000000 : ℝ)
  | 3 => (-1356361493 / 100000000000 : ℝ)
  | 4 => (-13055273507 / 1000000000000 : ℝ)
  | 5 => (-6270773779 / 500000000000 : ℝ)
  | 6 => (-1502802559 / 125000000000 : ℝ)
  | 7 => (-5748937891 / 500000000000 : ℝ)
  | 8 => (-2741974291 / 250000000000 : ℝ)
  | 9 => (-10432468443 / 1000000000000 : ℝ)
  | 10 => (-989157359 / 100000000000 : ℝ)
  | 11 => (-1168149591 / 125000000000 : ℝ)
  | 12 => (-2198330533 / 250000000000 : ℝ)
  | 13 => (-1029491779 / 125000000000 : ℝ)
  | 14 => (-1534603523 / 200000000000 : ℝ)
  | 15 => (-284182281 / 40000000000 : ℝ)
  | 16 => (-6530537367 / 1000000000000 : ℝ)
  | 17 => (-595094371 / 100000000000 : ℝ)
  | 18 => (-1073152257 / 200000000000 : ℝ)
  | 19 => (-4774975493 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch041Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-14564211339 / 1000000000000 : ℝ)
  | 1 => (-14066588577 / 1000000000000 : ℝ)
  | 2 => (-13563614929 / 1000000000000 : ℝ)
  | 3 => (-6527636753 / 500000000000 : ℝ)
  | 4 => (-12541547557 / 1000000000000 : ℝ)
  | 5 => (-12022420471 / 1000000000000 : ℝ)
  | 6 => (-11497875781 / 1000000000000 : ℝ)
  | 7 => (-10967897163 / 1000000000000 : ℝ)
  | 8 => (-5216234221 / 500000000000 : ℝ)
  | 9 => (-9891573589 / 1000000000000 : ℝ)
  | 10 => (-9345196727 / 1000000000000 : ℝ)
  | 11 => (-8793322131 / 1000000000000 : ℝ)
  | 12 => (-8235934231 / 1000000000000 : ℝ)
  | 13 => (-3836508807 / 500000000000 : ℝ)
  | 14 => (-222017407 / 31250000000 : ℝ)
  | 15 => (-3265268683 / 500000000000 : ℝ)
  | 16 => (-5950943709 / 1000000000000 : ℝ)
  | 17 => (-1341440321 / 250000000000 : ℝ)
  | 18 => (-1193743873 / 250000000000 : ℝ)
  | 19 => (-4178571899 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch041Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((820 : ℝ) + (j.val : ℝ)) / 1600)
      (((820 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch041Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch041Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((820 : ℝ) + (j.val : ℝ)) / 1600)
    (((820 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch041Neg40WeightLower j.val) (hpThetaShiftOneBatch041Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch041Neg40WeightLower, hpThetaShiftOneBatch041Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch041Neg40_integral_bounds :
    (-2466054901 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-2870390443 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (820 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch041Lower hpThetaJensenCellsBatch041Upper
    hpThetaShiftOneBatch041Neg40WeightLower hpThetaShiftOneBatch041Neg40WeightUpper hpThetaJensenCellsBatch041_bounds hpThetaShiftOneBatch041Neg40_weight_bounds
  have hl : (-2466054901 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch041Lower j * hpThetaShiftOneBatch041Neg40WeightLower j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftOneBatch041Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftOneBatch041Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch041Lower j * hpThetaShiftOneBatch041Neg40WeightUpper j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftOneBatch041Neg40WeightUpper j) / 1600) ≤ (-2870390443 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftOneBatch041Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (820 : ℝ) / 1600 = 41 / 80 by norm_num,
    show ((820 : ℝ) + 20) / 1600 = (41 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch041Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-55332403299 / 1000000000000 : ℝ)
  | 1 => (-138973283 / 2500000000 : ℝ)
  | 2 => (-3490360633 / 62500000000 : ℝ)
  | 3 => (-28050881683 / 500000000000 : ℝ)
  | 4 => (-56357282159 / 1000000000000 : ℝ)
  | 5 => (-14153078927 / 250000000000 : ℝ)
  | 6 => (-14216713293 / 250000000000 : ℝ)
  | 7 => (-7140110459 / 125000000000 : ℝ)
  | 8 => (-57374396283 / 1000000000000 : ℝ)
  | 9 => (-57627380043 / 1000000000000 : ℝ)
  | 10 => (-28939911973 / 500000000000 : ℝ)
  | 11 => (-58131716947 / 1000000000000 : ℝ)
  | 12 => (-58383047957 / 1000000000000 : ℝ)
  | 13 => (-1172676117 / 20000000000 : ℝ)
  | 14 => (-11776795891 / 200000000000 : ℝ)
  | 15 => (-14783389391 / 250000000000 : ℝ)
  | 16 => (-2375301157 / 40000000000 : ℝ)
  | 17 => (-59630882247 / 1000000000000 : ℝ)
  | 18 => (-59878606199 / 1000000000000 : ℝ)
  | 19 => (-939463897 / 15625000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch041Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-55075051097 / 1000000000000 : ℝ)
  | 1 => (-27666201649 / 500000000000 : ℝ)
  | 2 => (-55589313199 / 1000000000000 : ℝ)
  | 3 => (-55845770127 / 1000000000000 : ℝ)
  | 4 => (-11220352673 / 200000000000 : ℝ)
  | 5 => (-28178641079 / 500000000000 : ℝ)
  | 6 => (-56612315707 / 1000000000000 : ℝ)
  | 7 => (-56866853171 / 1000000000000 : ℝ)
  | 8 => (-57120883671 / 1000000000000 : ℝ)
  | 9 => (-28687198141 / 500000000000 : ℝ)
  | 10 => (-28813690021 / 500000000000 : ℝ)
  | 11 => (-11575964789 / 200000000000 : ℝ)
  | 12 => (-29065858473 / 500000000000 : ℝ)
  | 13 => (-14595761989 / 250000000000 : ℝ)
  | 14 => (-58633805849 / 1000000000000 : ℝ)
  | 15 => (-29441989727 / 500000000000 : ℝ)
  | 16 => (-59133557563 / 1000000000000 : ℝ)
  | 17 => (-14845632231 / 250000000000 : ℝ)
  | 18 => (-29815441123 / 500000000000 : ℝ)
  | 19 => (-29939303099 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch041Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((820 : ℝ) + (j.val : ℝ)) / 1600)
      (((820 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch041Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch041Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((820 : ℝ) + (j.val : ℝ)) / 1600)
    (((820 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch041Neg20WeightLower j.val) (hpThetaShiftOneBatch041Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch041Neg20WeightLower, hpThetaShiftOneBatch041Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch041Neg20_integral_bounds :
    (-348083157 / 5000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-34079088829 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (820 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch041Lower hpThetaJensenCellsBatch041Upper
    hpThetaShiftOneBatch041Neg20WeightLower hpThetaShiftOneBatch041Neg20WeightUpper hpThetaJensenCellsBatch041_bounds hpThetaShiftOneBatch041Neg20_weight_bounds
  have hl : (-348083157 / 5000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch041Lower j * hpThetaShiftOneBatch041Neg20WeightLower j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftOneBatch041Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftOneBatch041Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch041Lower j * hpThetaShiftOneBatch041Neg20WeightUpper j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftOneBatch041Neg20WeightUpper j) / 1600) ≤ (-34079088829 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftOneBatch041Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (820 : ℝ) / 1600 = 41 / 80 by norm_num,
    show ((820 : ℝ) + 20) / 1600 = (41 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch041Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch041Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch041Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch041Neg20_integral_bounds
end HodgeProofHP
