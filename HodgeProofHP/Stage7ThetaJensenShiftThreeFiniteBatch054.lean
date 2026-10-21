/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch054

/-! Exact signed weight and batch integral certificates, batch 54 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch054Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-179450109 / 200000000000 : ℝ)
  | 1 => (-919484703 / 1000000000000 : ℝ)
  | 2 => (-942096833 / 1000000000000 : ℝ)
  | 3 => (-965092009 / 1000000000000 : ℝ)
  | 4 => (-6177971 / 6250000000 : ℝ)
  | 5 => (-101225207 / 100000000000 : ℝ)
  | 6 => (-129553423 / 125000000000 : ℝ)
  | 7 => (-5305033 / 5000000000 : ℝ)
  | 8 => (-1085995079 / 1000000000000 : ℝ)
  | 9 => (-1111398237 / 1000000000000 : ℝ)
  | 10 => (-1137221551 / 1000000000000 : ℝ)
  | 11 => (-1163470557 / 1000000000000 : ℝ)
  | 12 => (-297537713 / 250000000000 : ℝ)
  | 13 => (-1217268093 / 1000000000000 : ℝ)
  | 14 => (-311207 / 250000000 : ℝ)
  | 15 => (-636418177 / 500000000000 : ℝ)
  | 16 => (-650649499 / 500000000000 : ℝ)
  | 17 => (-1330221839 / 1000000000000 : ℝ)
  | 18 => (-1359610847 / 1000000000000 : ℝ)
  | 19 => (-694736029 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch054Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-875389341 / 1000000000000 : ℝ)
  | 1 => (-56078159 / 62500000000 : ℝ)
  | 2 => (-459742351 / 500000000000 : ℝ)
  | 3 => (-14720263 / 15625000000 : ℝ)
  | 4 => (-120636501 / 125000000000 : ℝ)
  | 5 => (-988475359 / 1000000000000 : ℝ)
  | 6 => (-1012252069 / 1000000000000 : ℝ)
  | 7 => (-1036427383 / 1000000000000 : ℝ)
  | 8 => (-1061006599 / 1000000000000 : ℝ)
  | 9 => (-542997539 / 500000000000 : ℝ)
  | 10 => (-277849559 / 250000000000 : ℝ)
  | 11 => (-22744431 / 20000000000 : ℝ)
  | 12 => (-290867639 / 250000000000 : ℝ)
  | 13 => (-1190150851 / 1000000000000 : ℝ)
  | 14 => (-304317023 / 250000000000 : ℝ)
  | 15 => (-1244827999 / 1000000000000 : ℝ)
  | 16 => (-1272836353 / 1000000000000 : ℝ)
  | 17 => (-1301298997 / 1000000000000 : ℝ)
  | 18 => (-665110919 / 500000000000 : ℝ)
  | 19 => (-679805423 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch054Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1080 : ℝ) + (j.val : ℝ)) / 1600)
      (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch054Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch054Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1080 : ℝ) + (j.val : ℝ)) / 1600)
    (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch054Neg100WeightLower j.val) (hpThetaShiftThreeBatch054Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch054Neg100WeightLower, hpThetaShiftThreeBatch054Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch054Neg100_integral_bounds :
    (-98957421 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-94696497 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1080 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch054Lower hpThetaJensenCellsBatch054Upper
    hpThetaShiftThreeBatch054Neg100WeightLower hpThetaShiftThreeBatch054Neg100WeightUpper hpThetaJensenCellsBatch054_bounds hpThetaShiftThreeBatch054Neg100_weight_bounds
  have hl : (-98957421 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch054Lower j * hpThetaShiftThreeBatch054Neg100WeightLower j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftThreeBatch054Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftThreeBatch054Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch054Lower j * hpThetaShiftThreeBatch054Neg100WeightUpper j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftThreeBatch054Neg100WeightUpper j) / 1600) ≤ (-94696497 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftThreeBatch054Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1080 : ℝ) / 1600 = 54 / 80 by norm_num,
    show ((1080 : ℝ) + 20) / 1600 = (54 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch054Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2607423 / 7812500000 : ℝ)
  | 1 => (83835803 / 250000000000 : ℝ)
  | 2 => (168455839 / 500000000000 : ℝ)
  | 3 => (338454787 / 1000000000000 : ℝ)
  | 4 => (33997177 / 100000000000 : ℝ)
  | 5 => (341461847 / 1000000000000 : ℝ)
  | 6 => (171462113 / 500000000000 : ℝ)
  | 7 => (43044763 / 125000000000 : ℝ)
  | 8 => (345762663 / 1000000000000 : ℝ)
  | 9 => (86784269 / 250000000000 : ℝ)
  | 10 => (174240251 / 500000000000 : ℝ)
  | 11 => (43724011 / 125000000000 : ℝ)
  | 12 => (43883871 / 125000000000 : ℝ)
  | 13 => (352316263 / 1000000000000 : ℝ)
  | 14 => (353527081 / 1000000000000 : ℝ)
  | 15 => (354702517 / 1000000000000 : ℝ)
  | 16 => (177920827 / 500000000000 : ℝ)
  | 17 => (8923589 / 25000000000 : ℝ)
  | 18 => (35800729 / 100000000000 : ℝ)
  | 19 => (71806377 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch054Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (335343213 / 1000000000000 : ℝ)
  | 1 => (336911679 / 1000000000000 : ℝ)
  | 2 => (84613697 / 250000000000 : ℝ)
  | 3 => (339971771 / 1000000000000 : ℝ)
  | 4 => (42682731 / 125000000000 : ℝ)
  | 5 => (342924227 / 1000000000000 : ℝ)
  | 6 => (68871621 / 200000000000 : ℝ)
  | 7 => (43220333 / 125000000000 : ℝ)
  | 8 => (347137077 / 1000000000000 : ℝ)
  | 9 => (348480503 / 1000000000000 : ℝ)
  | 10 => (349792089 / 1000000000000 : ℝ)
  | 11 => (351070969 / 1000000000000 : ℝ)
  | 12 => (44039533 / 125000000000 : ℝ)
  | 13 => (176763541 / 500000000000 : ℝ)
  | 14 => (177351259 / 500000000000 : ℝ)
  | 15 => (71168331 / 200000000000 : ℝ)
  | 16 => (356943561 / 1000000000000 : ℝ)
  | 17 => (358007291 / 1000000000000 : ℝ)
  | 18 => (179515943 / 500000000000 : ℝ)
  | 19 => (180008187 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch054Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1080 : ℝ) + (j.val : ℝ)) / 1600)
      (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch054Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch054Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1080 : ℝ) + (j.val : ℝ)) / 1600)
    (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch054Neg70WeightLower j.val) (hpThetaShiftThreeBatch054Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch054Neg70WeightLower, hpThetaShiftThreeBatch054Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch054Neg70_integral_bounds :
    (29982281 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (30734307 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1080 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch054Lower hpThetaJensenCellsBatch054Upper
    hpThetaShiftThreeBatch054Neg70WeightLower hpThetaShiftThreeBatch054Neg70WeightUpper hpThetaJensenCellsBatch054_bounds hpThetaShiftThreeBatch054Neg70_weight_bounds
  have hl : (29982281 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch054Lower j * hpThetaShiftThreeBatch054Neg70WeightLower j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftThreeBatch054Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftThreeBatch054Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch054Lower j * hpThetaShiftThreeBatch054Neg70WeightUpper j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftThreeBatch054Neg70WeightUpper j) / 1600) ≤ (30734307 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftThreeBatch054Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1080 : ℝ) / 1600 = 54 / 80 by norm_num,
    show ((1080 : ℝ) + 20) / 1600 = (54 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch054Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (11095881 / 250000000000 : ℝ)
  | 1 => (46028793 / 1000000000000 : ℝ)
  | 2 => (11923471 / 250000000000 : ℝ)
  | 3 => (49378919 / 1000000000000 : ℝ)
  | 4 => (51084017 / 1000000000000 : ℝ)
  | 5 => (26404651 / 500000000000 : ℝ)
  | 6 => (27277447 / 500000000000 : ℝ)
  | 7 => (28160457 / 500000000000 : ℝ)
  | 8 => (29053741 / 500000000000 : ℝ)
  | 9 => (374467 / 6250000000 : ℝ)
  | 10 => (30871373 / 500000000000 : ℝ)
  | 11 => (63591681 / 1000000000000 : ℝ)
  | 12 => (16365411 / 250000000000 : ℝ)
  | 13 => (13470551 / 200000000000 : ℝ)
  | 14 => (69265133 / 1000000000000 : ℝ)
  | 15 => (14239779 / 200000000000 : ℝ)
  | 16 => (914427 / 12500000000 : ℝ)
  | 17 => (37565523 / 500000000000 : ℝ)
  | 18 => (7712967 / 100000000000 : ℝ)
  | 19 => (1583003 / 20000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch054Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (23014397 / 500000000000 : ℝ)
  | 1 => (9538777 / 200000000000 : ℝ)
  | 2 => (1234473 / 25000000000 : ℝ)
  | 3 => (25542009 / 500000000000 : ℝ)
  | 4 => (52809303 / 1000000000000 : ℝ)
  | 5 => (10910979 / 200000000000 : ℝ)
  | 6 => (11264183 / 200000000000 : ℝ)
  | 7 => (58107483 / 1000000000000 : ℝ)
  | 8 => (59914721 / 1000000000000 : ℝ)
  | 9 => (61742747 / 1000000000000 : ℝ)
  | 10 => (31795841 / 500000000000 : ℝ)
  | 11 => (13092329 / 200000000000 : ℝ)
  | 12 => (16838189 / 250000000000 : ℝ)
  | 13 => (34632567 / 500000000000 : ℝ)
  | 14 => (4449931 / 62500000000 : ℝ)
  | 15 => (73154161 / 1000000000000 : ℝ)
  | 16 => (75131047 / 1000000000000 : ℝ)
  | 17 => (77129671 / 1000000000000 : ℝ)
  | 18 => (79150151 / 1000000000000 : ℝ)
  | 19 => (40596301 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch054Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1080 : ℝ) + (j.val : ℝ)) / 1600)
      (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch054Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch054Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1080 : ℝ) + (j.val : ℝ)) / 1600)
    (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch054Neg45WeightLower j.val) (hpThetaShiftThreeBatch054Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch054Neg45WeightLower, hpThetaShiftThreeBatch054Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch054Neg45_integral_bounds :
    (2612331 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (687143 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1080 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch054Lower hpThetaJensenCellsBatch054Upper
    hpThetaShiftThreeBatch054Neg45WeightLower hpThetaShiftThreeBatch054Neg45WeightUpper hpThetaJensenCellsBatch054_bounds hpThetaShiftThreeBatch054Neg45_weight_bounds
  have hl : (2612331 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch054Lower j * hpThetaShiftThreeBatch054Neg45WeightLower j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftThreeBatch054Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftThreeBatch054Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch054Lower j * hpThetaShiftThreeBatch054Neg45WeightUpper j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftThreeBatch054Neg45WeightUpper j) / 1600) ≤ (687143 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftThreeBatch054Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1080 : ℝ) / 1600 = 54 / 80 by norm_num,
    show ((1080 : ℝ) + 20) / 1600 = (54 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch054Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-32318557 / 250000000000 : ℝ)
  | 1 => (-65105517 / 500000000000 : ℝ)
  | 2 => (-65574849 / 500000000000 : ℝ)
  | 3 => (-6604509 / 50000000000 : ℝ)
  | 4 => (-133032441 / 1000000000000 : ℝ)
  | 5 => (-133976441 / 1000000000000 : ℝ)
  | 6 => (-6746107 / 50000000000 : ℝ)
  | 7 => (-135869497 / 1000000000000 : ℝ)
  | 8 => (-13681847 / 100000000000 : ℝ)
  | 9 => (-137769017 / 1000000000000 : ℝ)
  | 10 => (-17340137 / 125000000000 : ℝ)
  | 11 => (-139674663 / 1000000000000 : ℝ)
  | 12 => (-5625187 / 40000000000 : ℝ)
  | 13 => (-141586087 / 1000000000000 : ℝ)
  | 14 => (-8908991 / 62500000000 : ℝ)
  | 15 => (-28700587 / 200000000000 : ℝ)
  | 16 => (-144463279 / 1000000000000 : ℝ)
  | 17 => (-145424841 / 1000000000000 : ℝ)
  | 18 => (-5855503 / 40000000000 : ℝ)
  | 19 => (-18418929 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch054Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-128339317 / 1000000000000 : ℝ)
  | 1 => (-129274227 / 1000000000000 : ℝ)
  | 2 => (-130211033 / 1000000000000 : ℝ)
  | 3 => (-131149697 / 1000000000000 : ℝ)
  | 4 => (-132090179 / 1000000000000 : ℝ)
  | 5 => (-3325811 / 25000000000 : ℝ)
  | 6 => (-3349411 / 25000000000 : ℝ)
  | 7 => (-134922139 / 1000000000000 : ℝ)
  | 8 => (-16983687 / 125000000000 : ℝ)
  | 9 => (-136818469 / 1000000000000 : ℝ)
  | 10 => (-17221127 / 125000000000 : ℝ)
  | 11 => (-27744219 / 200000000000 : ℝ)
  | 12 => (-69837331 / 500000000000 : ℝ)
  | 13 => (-70314837 / 500000000000 : ℝ)
  | 14 => (-70793043 / 500000000000 : ℝ)
  | 15 => (-28508771 / 200000000000 : ℝ)
  | 16 => (-71751467 / 500000000000 : ℝ)
  | 17 => (-72231639 / 500000000000 : ℝ)
  | 18 => (-3635621 / 25000000000 : ℝ)
  | 19 => (-73193787 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch054Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1080 : ℝ) + (j.val : ℝ)) / 1600)
      (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch054Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch054Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1080 : ℝ) + (j.val : ℝ)) / 1600)
    (((1080 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch054Neg25WeightLower j.val) (hpThetaShiftThreeBatch054Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch054Neg25WeightLower, hpThetaShiftThreeBatch054Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch054Neg25_integral_bounds :
    (-6087383 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (54 / 80 : ℝ) ((54 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (-2960033 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1080 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch054Lower hpThetaJensenCellsBatch054Upper
    hpThetaShiftThreeBatch054Neg25WeightLower hpThetaShiftThreeBatch054Neg25WeightUpper hpThetaJensenCellsBatch054_bounds hpThetaShiftThreeBatch054Neg25_weight_bounds
  have hl : (-6087383 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch054Lower j * hpThetaShiftThreeBatch054Neg25WeightLower j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftThreeBatch054Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftThreeBatch054Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch054Lower j * hpThetaShiftThreeBatch054Neg25WeightUpper j)
        (hpThetaJensenCellsBatch054Upper j * hpThetaShiftThreeBatch054Neg25WeightUpper j) / 1600) ≤ (-2960033 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch054Lower, hpThetaJensenCellsBatch054Upper,
      hpThetaShiftThreeBatch054Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1080 : ℝ) / 1600 = 54 / 80 by norm_num,
    show ((1080 : ℝ) + 20) / 1600 = (54 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch054Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch054Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch054Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch054Neg25_integral_bounds
end HodgeProofHP
