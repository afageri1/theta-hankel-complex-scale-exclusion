/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch077

/-! Exact signed weight and batch integral certificates, batch 77 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch077Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-11413896403627 / 1000000000000 : ℝ)
  | 1 => (-460020437833 / 40000000000 : ℝ)
  | 2 => (-2317540527599 / 200000000000 : ℝ)
  | 3 => (-11675474824537 / 1000000000000 : ℝ)
  | 4 => (-5881915433237 / 500000000000 : ℝ)
  | 5 => (-474110965661 / 40000000000 : ℝ)
  | 6 => (-11942308044173 / 1000000000000 : ℝ)
  | 7 => (-1504054498217 / 125000000000 : ℝ)
  | 8 => (-12123161394437 / 1000000000000 : ℝ)
  | 9 => (-12214487715473 / 1000000000000 : ℝ)
  | 10 => (-1230641841109 / 100000000000 : ℝ)
  | 11 => (-12398956960649 / 1000000000000 : ℝ)
  | 12 => (-124921068607 / 10000000000 : ℝ)
  | 13 => (-12585871625053 / 1000000000000 : ℝ)
  | 14 => (-12680254784851 / 1000000000000 : ℝ)
  | 15 => (-6387629944319 / 500000000000 : ℝ)
  | 16 => (-12870890502437 / 1000000000000 : ℝ)
  | 17 => (-12967150209817 / 1000000000000 : ℝ)
  | 18 => (-51031416453 / 3906250000 : ℝ)
  | 19 => (-13161571327777 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch077Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5663927841779 / 500000000000 : ℝ)
  | 1 => (-5706948201813 / 500000000000 : ℝ)
  | 2 => (-359390967057 / 31250000000 : ℝ)
  | 3 => (-5793851318997 / 500000000000 : ℝ)
  | 4 => (-1459434353067 / 125000000000 : ℝ)
  | 5 => (-11763830866473 / 1000000000000 : ℝ)
  | 6 => (-2963193535381 / 250000000000 : ℝ)
  | 7 => (-2985577011043 / 250000000000 : ℝ)
  | 8 => (-2406487197147 / 200000000000 : ℝ)
  | 9 => (-3030790348609 / 250000000000 : ℝ)
  | 10 => (-763405482217 / 62500000000 : ℝ)
  | 11 => (-12306418411089 / 1000000000000 : ℝ)
  | 12 => (-1549869620081 / 125000000000 : ℝ)
  | 13 => (-12492106860699 / 1000000000000 : ℝ)
  | 14 => (-3146467906263 / 250000000000 : ℝ)
  | 15 => (-253605095697 / 20000000000 : ℝ)
  | 16 => (-12775259888637 / 1000000000000 : ℝ)
  | 17 => (-3217722625609 / 250000000000 : ℝ)
  | 18 => (-1620893776227 / 125000000000 : ℝ)
  | 19 => (-13064042611967 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch077Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1540 : ℝ) + (j.val : ℝ)) / 1600)
      (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch077Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch077Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1540 : ℝ) + (j.val : ℝ)) / 1600)
    (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch077Neg100WeightLower j.val) (hpThetaShiftTwoBatch077Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch077Neg100WeightLower, hpThetaShiftTwoBatch077Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch077Neg100_integral_bounds :
    (-76181251 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-292677121 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch077Lower hpThetaJensenCellsBatch077Upper
    hpThetaShiftTwoBatch077Neg100WeightLower hpThetaShiftTwoBatch077Neg100WeightUpper hpThetaJensenCellsBatch077_bounds hpThetaShiftTwoBatch077Neg100_weight_bounds
  have hl : (-76181251 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch077Lower j * hpThetaShiftTwoBatch077Neg100WeightLower j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftTwoBatch077Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftTwoBatch077Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch077Lower j * hpThetaShiftTwoBatch077Neg100WeightUpper j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftTwoBatch077Neg100WeightUpper j) / 1600) ≤ (-292677121 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftTwoBatch077Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1540 : ℝ) / 1600 = 77 / 80 by norm_num,
    show ((1540 : ℝ) + 20) / 1600 = (77 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch077Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1876466363123 / 1000000000000 : ℝ)
  | 1 => (-1892866061433 / 1000000000000 : ℝ)
  | 2 => (-1909387198573 / 1000000000000 : ℝ)
  | 3 => (-1926030536899 / 1000000000000 : ℝ)
  | 4 => (-4856992107 / 2500000000 : ℝ)
  | 5 => (-1959686886707 / 1000000000000 : ℝ)
  | 6 => (-988350721557 / 500000000000 : ℝ)
  | 7 => (-1993841290599 / 1000000000000 : ℝ)
  | 8 => (-502776802959 / 250000000000 : ℝ)
  | 9 => (-1014249996809 / 500000000000 : ℝ)
  | 10 => (-2046020426871 / 1000000000000 : ℝ)
  | 11 => (-1031834653337 / 500000000000 : ℝ)
  | 12 => (-2081447432279 / 1000000000000 : ℝ)
  | 13 => (-16794844857 / 8000000000 : ℝ)
  | 14 => (-1058697319429 / 500000000000 : ℝ)
  | 15 => (-2135565339351 / 1000000000000 : ℝ)
  | 16 => (-2153868524719 / 1000000000000 : ℝ)
  | 17 => (-2172305015341 / 1000000000000 : ℝ)
  | 18 => (-2190875635877 / 1000000000000 : ℝ)
  | 19 => (-552395303821 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch077Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1860187345293 / 1000000000000 : ℝ)
  | 1 => (-938233181561 / 500000000000 : ℝ)
  | 2 => (-236608257679 / 125000000000 : ℝ)
  | 3 => (-477346799643 / 250000000000 : ℝ)
  | 4 => (-963015268449 / 500000000000 : ℝ)
  | 5 => (-1942796842799 / 1000000000000 : ℝ)
  | 6 => (-979843443353 / 500000000000 : ℝ)
  | 7 => (-1976701443113 / 1000000000000 : ℝ)
  | 8 => (-996920645299 / 500000000000 : ℝ)
  | 9 => (-402221442367 / 200000000000 : ℝ)
  | 10 => (-2028499993617 / 1000000000000 : ℝ)
  | 11 => (-204602042687 / 100000000000 : ℝ)
  | 12 => (-2063669306673 / 1000000000000 : ℝ)
  | 13 => (-1040723716139 / 500000000000 : ℝ)
  | 14 => (-524838901781 / 250000000000 : ℝ)
  | 15 => (-2117394638857 / 1000000000000 : ℝ)
  | 16 => (-42711306787 / 20000000000 : ℝ)
  | 17 => (-1076934262359 / 500000000000 : ℝ)
  | 18 => (-108615250767 / 50000000000 : ℝ)
  | 19 => (-547718908969 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch077Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1540 : ℝ) + (j.val : ℝ)) / 1600)
      (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch077Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch077Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1540 : ℝ) + (j.val : ℝ)) / 1600)
    (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch077Neg65WeightLower j.val) (hpThetaShiftTwoBatch077Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch077Neg65WeightLower, hpThetaShiftTwoBatch077Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch077Neg65_integral_bounds :
    (-50600809 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-48546399 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch077Lower hpThetaJensenCellsBatch077Upper
    hpThetaShiftTwoBatch077Neg65WeightLower hpThetaShiftTwoBatch077Neg65WeightUpper hpThetaJensenCellsBatch077_bounds hpThetaShiftTwoBatch077Neg65_weight_bounds
  have hl : (-50600809 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch077Lower j * hpThetaShiftTwoBatch077Neg65WeightLower j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftTwoBatch077Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftTwoBatch077Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch077Lower j * hpThetaShiftTwoBatch077Neg65WeightUpper j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftTwoBatch077Neg65WeightUpper j) / 1600) ≤ (-48546399 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftTwoBatch077Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1540 : ℝ) / 1600 = 77 / 80 by norm_num,
    show ((1540 : ℝ) + 20) / 1600 = (77 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch077Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-13656897607 / 62500000000 : ℝ)
  | 1 => (-110682331447 / 500000000000 : ℝ)
  | 2 => (-14015339803 / 62500000000 : ℝ)
  | 3 => (-227152875591 / 1000000000000 : ℝ)
  | 4 => (-115043586131 / 500000000000 : ℝ)
  | 5 => (-233048521121 / 1000000000000 : ℝ)
  | 6 => (-118018558781 / 500000000000 : ℝ)
  | 7 => (-7470411191 / 31250000000 : ℝ)
  | 8 => (-242096840439 / 1000000000000 : ℝ)
  | 9 => (-245168363357 / 1000000000000 : ℝ)
  | 10 => (-15516745427 / 62500000000 : ℝ)
  | 11 => (-251395731987 / 1000000000000 : ℝ)
  | 12 => (-127275990553 / 500000000000 : ℝ)
  | 13 => (-257736877641 / 1000000000000 : ℝ)
  | 14 => (-130475313109 / 500000000000 : ℝ)
  | 15 => (-264193432639 / 1000000000000 : ℝ)
  | 16 => (-267465503893 / 1000000000000 : ℝ)
  | 17 => (-67691762039 / 250000000000 : ℝ)
  | 18 => (-274098274801 / 1000000000000 : ℝ)
  | 19 => (-138729697199 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch077Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-215682342397 / 1000000000000 : ℝ)
  | 1 => (-218510361711 / 1000000000000 : ℝ)
  | 2 => (-221364662893 / 1000000000000 : ℝ)
  | 3 => (-224245436847 / 1000000000000 : ℝ)
  | 4 => (-22715287559 / 100000000000 : ℝ)
  | 5 => (-230087172261 / 1000000000000 : ℝ)
  | 6 => (-1456553257 / 6250000000 : ℝ)
  | 7 => (-236037117561 / 1000000000000 : ℝ)
  | 8 => (-239053158111 / 1000000000000 : ℝ)
  | 9 => (-121048420219 / 500000000000 : ℝ)
  | 10 => (-61292090839 / 250000000000 : ℝ)
  | 11 => (-248267926831 / 1000000000000 : ℝ)
  | 12 => (-125697865993 / 500000000000 : ℝ)
  | 13 => (-50910396221 / 200000000000 : ℝ)
  | 14 => (-6443421941 / 25000000000 : ℝ)
  | 15 => (-260950626217 / 1000000000000 : ℝ)
  | 16 => (-132096716319 / 500000000000 : ℝ)
  | 17 => (-66866375973 / 250000000000 : ℝ)
  | 18 => (-54153409631 / 200000000000 : ℝ)
  | 19 => (-685245687 / 2500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch077Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1540 : ℝ) + (j.val : ℝ)) / 1600)
      (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch077Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch077Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1540 : ℝ) + (j.val : ℝ)) / 1600)
    (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch077Neg45WeightLower j.val) (hpThetaShiftTwoBatch077Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch077Neg45WeightLower, hpThetaShiftTwoBatch077Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch077Neg45_integral_bounds :
    (-1528363 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-5841809 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch077Lower hpThetaJensenCellsBatch077Upper
    hpThetaShiftTwoBatch077Neg45WeightLower hpThetaShiftTwoBatch077Neg45WeightUpper hpThetaJensenCellsBatch077_bounds hpThetaShiftTwoBatch077Neg45_weight_bounds
  have hl : (-1528363 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch077Lower j * hpThetaShiftTwoBatch077Neg45WeightLower j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftTwoBatch077Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftTwoBatch077Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch077Lower j * hpThetaShiftTwoBatch077Neg45WeightUpper j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftTwoBatch077Neg45WeightUpper j) / 1600) ≤ (-5841809 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftTwoBatch077Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1540 : ℝ) / 1600 = 77 / 80 by norm_num,
    show ((1540 : ℝ) + 20) / 1600 = (77 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch077Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (11020128217 / 250000000000 : ℝ)
  | 1 => (22155627491 / 500000000000 : ℝ)
  | 2 => (22271047231 / 500000000000 : ℝ)
  | 3 => (44773021419 / 1000000000000 : ℝ)
  | 4 => (45004025861 / 1000000000000 : ℝ)
  | 5 => (45235097693 / 1000000000000 : ℝ)
  | 6 => (22733113357 / 500000000000 : ℝ)
  | 7 => (45697402619 / 1000000000000 : ℝ)
  | 8 => (45928614997 / 1000000000000 : ℝ)
  | 9 => (46159853329 / 1000000000000 : ℝ)
  | 10 => (2899444187 / 62500000000 : ℝ)
  | 11 => (23311182627 / 500000000000 : ℝ)
  | 12 => (5856702159 / 125000000000 : ℝ)
  | 13 => (47084852099 / 1000000000000 : ℝ)
  | 14 => (23658029337 / 500000000000 : ℝ)
  | 15 => (47547225827 / 1000000000000 : ℝ)
  | 16 => (23889171139 / 500000000000 : ℝ)
  | 17 => (9601879327 / 200000000000 : ℝ)
  | 18 => (48240377391 / 1000000000000 : ℝ)
  | 19 => (48471272929 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch077Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (44311254983 / 1000000000000 : ℝ)
  | 1 => (44542094463 / 1000000000000 : ℝ)
  | 2 => (2238651071 / 50000000000 : ℝ)
  | 3 => (22502012931 / 500000000000 : ℝ)
  | 4 => (22617548847 / 500000000000 : ℝ)
  | 5 => (9093245343 / 200000000000 : ℝ)
  | 6 => (2284870131 / 50000000000 : ℝ)
  | 7 => (22964307499 / 500000000000 : ℝ)
  | 8 => (4615985333 / 100000000000 : ℝ)
  | 9 => (46391106993 / 1000000000000 : ℝ)
  | 10 => (9324473051 / 200000000000 : ℝ)
  | 11 => (46853617273 / 1000000000000 : ℝ)
  | 12 => (470848521 / 10000000000 : ℝ)
  | 13 => (1892642347 / 40000000000 : ℝ)
  | 14 => (11886806457 / 250000000000 : ℝ)
  | 15 => (47778342279 / 1000000000000 : ℝ)
  | 16 => (12002349159 / 250000000000 : ℝ)
  | 17 => (3015023587 / 62500000000 : ℝ)
  | 18 => (4847127293 / 100000000000 : ℝ)
  | 19 => (48702071519 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch077Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1540 : ℝ) + (j.val : ℝ)) / 1600)
      (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch077Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch077Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1540 : ℝ) + (j.val : ℝ)) / 1600)
    (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch077Neg25WeightLower j.val) (hpThetaShiftTwoBatch077Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch077Neg25WeightLower, hpThetaShiftTwoBatch077Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch077Neg25_integral_bounds :
    (55717 / 50000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (578653 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch077Lower hpThetaJensenCellsBatch077Upper
    hpThetaShiftTwoBatch077Neg25WeightLower hpThetaShiftTwoBatch077Neg25WeightUpper hpThetaJensenCellsBatch077_bounds hpThetaShiftTwoBatch077Neg25_weight_bounds
  have hl : (55717 / 50000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch077Lower j * hpThetaShiftTwoBatch077Neg25WeightLower j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftTwoBatch077Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftTwoBatch077Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch077Lower j * hpThetaShiftTwoBatch077Neg25WeightUpper j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftTwoBatch077Neg25WeightUpper j) / 1600) ≤ (578653 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftTwoBatch077Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1540 : ℝ) / 1600 = 77 / 80 by norm_num,
    show ((1540 : ℝ) + 20) / 1600 = (77 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch077Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch077Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch077Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch077Neg25_integral_bounds
end HodgeProofHP
