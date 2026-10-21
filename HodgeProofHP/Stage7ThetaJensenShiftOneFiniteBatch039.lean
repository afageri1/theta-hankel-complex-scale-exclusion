/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch039

/-! Exact signed weight and batch integral certificates, batch 39 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch039Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (163097597273 / 1000000000000 : ℝ)
  | 1 => (162443478957 / 1000000000000 : ℝ)
  | 2 => (80875723621 / 500000000000 : ℝ)
  | 3 => (161020921107 / 1000000000000 : ℝ)
  | 4 => (40062828493 / 250000000000 : ℝ)
  | 5 => (159442033669 / 1000000000000 : ℝ)
  | 6 => (158592482403 / 1000000000000 : ℝ)
  | 7 => (31540411343 / 200000000000 : ℝ)
  | 8 => (78385073721 / 500000000000 : ℝ)
  | 9 => (19474517461 / 125000000000 : ℝ)
  | 10 => (154779412779 / 1000000000000 : ℝ)
  | 11 => (153719340229 / 1000000000000 : ℝ)
  | 12 => (152615289701 / 1000000000000 : ℝ)
  | 13 => (75733311487 / 500000000000 : ℝ)
  | 14 => (150272695897 / 1000000000000 : ℝ)
  | 15 => (149032858359 / 1000000000000 : ℝ)
  | 16 => (29549290849 / 200000000000 : ℝ)
  | 17 => (146412821401 / 1000000000000 : ℝ)
  | 18 => (72515645797 / 500000000000 : ℝ)
  | 19 => (35900297619 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch039Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (163714377699 / 1000000000000 : ℝ)
  | 1 => (81548798637 / 500000000000 : ℝ)
  | 2 => (81221739479 / 500000000000 : ℝ)
  | 3 => (161751447243 / 1000000000000 : ℝ)
  | 4 => (40255230277 / 250000000000 : ℝ)
  | 5 => (160251313973 / 1000000000000 : ℝ)
  | 6 => (15944203367 / 100000000000 : ℝ)
  | 7 => (39648120601 / 250000000000 : ℝ)
  | 8 => (39425514179 / 250000000000 : ℝ)
  | 9 => (156770147443 / 1000000000000 : ℝ)
  | 10 => (155796139689 / 1000000000000 : ℝ)
  | 11 => (7738970639 / 50000000000 : ℝ)
  | 12 => (15371934023 / 100000000000 : ℝ)
  | 13 => (76307644851 / 500000000000 : ℝ)
  | 14 => (6058664919 / 40000000000 : ℝ)
  | 15 => (75136347949 / 500000000000 : ℝ)
  | 16 => (3725821459 / 25000000000 : ℝ)
  | 17 => (73873227123 / 500000000000 : ℝ)
  | 18 => (73206410701 / 500000000000 : ℝ)
  | 19 => (29006258319 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch039Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((780 : ℝ) + (j.val : ℝ)) / 1600)
      (((780 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch039Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch039Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((780 : ℝ) + (j.val : ℝ)) / 1600)
    (((780 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch039Neg100WeightLower j.val) (hpThetaShiftOneBatch039Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch039Neg100WeightLower, hpThetaShiftOneBatch039Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch039Neg100_integral_bounds :
    (125220892191 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (256181340139 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (780 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch039Lower hpThetaJensenCellsBatch039Upper
    hpThetaShiftOneBatch039Neg100WeightLower hpThetaShiftOneBatch039Neg100WeightUpper hpThetaJensenCellsBatch039_bounds hpThetaShiftOneBatch039Neg100_weight_bounds
  have hl : (125220892191 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch039Lower j * hpThetaShiftOneBatch039Neg100WeightLower j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftOneBatch039Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftOneBatch039Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch039Lower j * hpThetaShiftOneBatch039Neg100WeightUpper j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftOneBatch039Neg100WeightUpper j) / 1600) ≤ (256181340139 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftOneBatch039Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (780 : ℝ) / 1600 = 39 / 80 by norm_num,
    show ((780 : ℝ) + 20) / 1600 = (39 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch039Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (97350278697 / 1000000000000 : ℝ)
  | 1 => (19701619791 / 200000000000 : ℝ)
  | 2 => (24917515541 / 250000000000 : ℝ)
  | 3 => (50418054813 / 500000000000 : ℝ)
  | 4 => (102006181577 / 1000000000000 : ℝ)
  | 5 => (103180217181 / 1000000000000 : ℝ)
  | 6 => (52179077259 / 500000000000 : ℝ)
  | 7 => (5276996529 / 50000000000 : ℝ)
  | 8 => (106725481257 / 1000000000000 : ℝ)
  | 9 => (10791474133 / 100000000000 : ℝ)
  | 10 => (21821528893 / 200000000000 : ℝ)
  | 11 => (55152061599 / 500000000000 : ℝ)
  | 12 => (27876027233 / 250000000000 : ℝ)
  | 13 => (28176882981 / 250000000000 : ℝ)
  | 14 => (177991127 / 1562500000 : ℝ)
  | 15 => (5756220247 / 50000000000 : ℝ)
  | 16 => (116337709673 / 1000000000000 : ℝ)
  | 17 => (117554161067 / 1000000000000 : ℝ)
  | 18 => (371167761 / 3125000000 : ℝ)
  | 19 => (119996200229 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch039Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (24627024739 / 250000000000 : ℝ)
  | 1 => (19934012433 / 200000000000 : ℝ)
  | 2 => (100836109627 / 1000000000000 : ℝ)
  | 3 => (51003090789 / 500000000000 : ℝ)
  | 4 => (51590108591 / 500000000000 : ℝ)
  | 5 => (104358154519 / 1000000000000 : ℝ)
  | 6 => (105539930581 / 1000000000000 : ℝ)
  | 7 => (53362740629 / 500000000000 : ℝ)
  | 8 => (107914741331 / 1000000000000 : ℝ)
  | 9 => (54553822233 / 500000000000 : ℝ)
  | 10 => (110304123199 / 1000000000000 : ℝ)
  | 11 => (111504108933 / 1000000000000 : ℝ)
  | 12 => (4508301277 / 40000000000 : ℝ)
  | 13 => (113914321281 / 1000000000000 : ℝ)
  | 14 => (115124404941 / 1000000000000 : ℝ)
  | 15 => (58168854837 / 500000000000 : ℝ)
  | 16 => (29388540267 / 250000000000 : ℝ)
  | 17 => (118773683521 / 1000000000000 : ℝ)
  | 18 => (11999620023 / 100000000000 : ℝ)
  | 19 => (24244326637 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch039Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((780 : ℝ) + (j.val : ℝ)) / 1600)
      (((780 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch039Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch039Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((780 : ℝ) + (j.val : ℝ)) / 1600)
    (((780 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch039Neg65WeightLower j.val) (hpThetaShiftOneBatch039Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch039Neg65WeightLower, hpThetaShiftOneBatch039Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch039Neg65_integral_bounds :
    (87568437203 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (179968726921 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (780 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch039Lower hpThetaJensenCellsBatch039Upper
    hpThetaShiftOneBatch039Neg65WeightLower hpThetaShiftOneBatch039Neg65WeightUpper hpThetaJensenCellsBatch039_bounds hpThetaShiftOneBatch039Neg65_weight_bounds
  have hl : (87568437203 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch039Lower j * hpThetaShiftOneBatch039Neg65WeightLower j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftOneBatch039Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftOneBatch039Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch039Lower j * hpThetaShiftOneBatch039Neg65WeightUpper j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftOneBatch039Neg65WeightUpper j) / 1600) ≤ (179968726921 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftOneBatch039Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (780 : ℝ) / 1600 = 39 / 80 by norm_num,
    show ((780 : ℝ) + 20) / 1600 = (39 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch039Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-30584684521 / 1000000000000 : ℝ)
  | 1 => (-7572609769 / 250000000000 : ℝ)
  | 2 => (-14995816287 / 500000000000 : ℝ)
  | 3 => (-14844121977 / 500000000000 : ℝ)
  | 4 => (-14690126113 / 500000000000 : ℝ)
  | 5 => (-29067636467 / 1000000000000 : ℝ)
  | 6 => (-28750375829 / 1000000000000 : ℝ)
  | 7 => (-111048631 / 3906250000 : ℝ)
  | 8 => (-3512729611 / 125000000000 : ℝ)
  | 9 => (-1388525863 / 50000000000 : ℝ)
  | 10 => (-27434470109 / 1000000000000 : ℝ)
  | 11 => (-27093674967 / 1000000000000 : ℝ)
  | 12 => (-534962229 / 20000000000 : ℝ)
  | 13 => (-13198879629 / 500000000000 : ℝ)
  | 14 => (-6510649543 / 250000000000 : ℝ)
  | 15 => (-12841304031 / 500000000000 : ℝ)
  | 16 => (-5063553777 / 200000000000 : ℝ)
  | 17 => (-1559253793 / 62500000000 : ℝ)
  | 18 => (-24573463607 / 1000000000000 : ℝ)
  | 19 => (-24193957873 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch039Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1211617563 / 40000000000 : ℝ)
  | 1 => (-29991632573 / 1000000000000 : ℝ)
  | 2 => (-29688243953 / 1000000000000 : ℝ)
  | 3 => (-1175210089 / 40000000000 : ℝ)
  | 4 => (-14533818233 / 500000000000 : ℝ)
  | 5 => (-7187593957 / 250000000000 : ℝ)
  | 6 => (-5685689907 / 200000000000 : ℝ)
  | 7 => (-28101836887 / 1000000000000 : ℝ)
  | 8 => (-27770517259 / 1000000000000 : ℝ)
  | 9 => (-6858617527 / 250000000000 : ℝ)
  | 10 => (-13546837483 / 500000000000 : ℝ)
  | 11 => (-26748111449 / 1000000000000 : ℝ)
  | 12 => (-26397759257 / 1000000000000 : ℝ)
  | 13 => (-26042598171 / 1000000000000 : ℝ)
  | 14 => (-25682608061 / 1000000000000 : ℝ)
  | 15 => (-6329442221 / 250000000000 : ℝ)
  | 16 => (-24948060687 / 1000000000000 : ℝ)
  | 17 => (-12286731803 / 500000000000 : ℝ)
  | 18 => (-1512122367 / 62500000000 : ℝ)
  | 19 => (-23809523809 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch039Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((780 : ℝ) + (j.val : ℝ)) / 1600)
      (((780 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch039Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch039Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((780 : ℝ) + (j.val : ℝ)) / 1600)
    (((780 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch039Neg40WeightLower j.val) (hpThetaShiftOneBatch039Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch039Neg40WeightLower, hpThetaShiftOneBatch039Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch039Neg40_integral_bounds :
    (-22693819071 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-22054993897 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (780 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch039Lower hpThetaJensenCellsBatch039Upper
    hpThetaShiftOneBatch039Neg40WeightLower hpThetaShiftOneBatch039Neg40WeightUpper hpThetaJensenCellsBatch039_bounds hpThetaShiftOneBatch039Neg40_weight_bounds
  have hl : (-22693819071 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch039Lower j * hpThetaShiftOneBatch039Neg40WeightLower j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftOneBatch039Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftOneBatch039Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch039Lower j * hpThetaShiftOneBatch039Neg40WeightUpper j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftOneBatch039Neg40WeightUpper j) / 1600) ≤ (-22054993897 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftOneBatch039Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (780 : ℝ) / 1600 = 39 / 80 by norm_num,
    show ((780 : ℝ) + 20) / 1600 = (39 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch039Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-44802390747 / 1000000000000 : ℝ)
  | 1 => (-9013823377 / 200000000000 : ℝ)
  | 2 => (-45335783981 / 1000000000000 : ℝ)
  | 3 => (-2850148939 / 62500000000 : ℝ)
  | 4 => (-11467226239 / 250000000000 : ℝ)
  | 5 => (-23067670339 / 500000000000 : ℝ)
  | 6 => (-5800210131 / 125000000000 : ℝ)
  | 7 => (-46667916881 / 1000000000000 : ℝ)
  | 8 => (-23467019473 / 500000000000 : ℝ)
  | 9 => (-11800009493 / 250000000000 : ℝ)
  | 10 => (-11866476161 / 250000000000 : ℝ)
  | 11 => (-11932907401 / 250000000000 : ℝ)
  | 12 => (-959944069 / 20000000000 : ℝ)
  | 13 => (-48262616739 / 1000000000000 : ℝ)
  | 14 => (-48527859983 / 1000000000000 : ℝ)
  | 15 => (-12198230913 / 250000000000 : ℝ)
  | 16 => (-49057798173 / 1000000000000 : ℝ)
  | 17 => (-4932247393 / 100000000000 : ℝ)
  | 18 => (-9917388253 / 200000000000 : ℝ)
  | 19 => (-49851190477 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch039Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-44535614537 / 1000000000000 : ℝ)
  | 1 => (-22401195373 / 500000000000 : ℝ)
  | 2 => (-11267279221 / 250000000000 : ℝ)
  | 3 => (-2266789199 / 50000000000 : ℝ)
  | 4 => (-45602383023 / 1000000000000 : ℝ)
  | 5 => (-9173780991 / 200000000000 : ℝ)
  | 6 => (-46135340677 / 1000000000000 : ℝ)
  | 7 => (-46401681047 / 1000000000000 : ℝ)
  | 8 => (-583348961 / 12500000000 : ℝ)
  | 9 => (-9386807789 / 200000000000 : ℝ)
  | 10 => (-47200037971 / 1000000000000 : ℝ)
  | 11 => (-47465904643 / 1000000000000 : ℝ)
  | 12 => (-47731629603 / 1000000000000 : ℝ)
  | 13 => (-47997203449 / 1000000000000 : ℝ)
  | 14 => (-24131308369 / 500000000000 : ℝ)
  | 15 => (-24263929991 / 500000000000 : ℝ)
  | 16 => (-48792923651 / 1000000000000 : ℝ)
  | 17 => (-12264449543 / 250000000000 : ℝ)
  | 18 => (-49322473929 / 1000000000000 : ℝ)
  | 19 => (-3099183829 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch039Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((780 : ℝ) + (j.val : ℝ)) / 1600)
      (((780 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch039Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch039Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((780 : ℝ) + (j.val : ℝ)) / 1600)
    (((780 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch039Neg20WeightLower j.val) (hpThetaShiftOneBatch039Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch039Neg20WeightLower, hpThetaShiftOneBatch039Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch039Neg20_integral_bounds :
    (-38852419751 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (39 / 80 : ℝ) ((39 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-152043553 / 2000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (780 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch039Lower hpThetaJensenCellsBatch039Upper
    hpThetaShiftOneBatch039Neg20WeightLower hpThetaShiftOneBatch039Neg20WeightUpper hpThetaJensenCellsBatch039_bounds hpThetaShiftOneBatch039Neg20_weight_bounds
  have hl : (-38852419751 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch039Lower j * hpThetaShiftOneBatch039Neg20WeightLower j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftOneBatch039Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftOneBatch039Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch039Lower j * hpThetaShiftOneBatch039Neg20WeightUpper j)
        (hpThetaJensenCellsBatch039Upper j * hpThetaShiftOneBatch039Neg20WeightUpper j) / 1600) ≤ (-152043553 / 2000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch039Lower, hpThetaJensenCellsBatch039Upper,
      hpThetaShiftOneBatch039Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (780 : ℝ) / 1600 = 39 / 80 by norm_num,
    show ((780 : ℝ) + 20) / 1600 = (39 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch039Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch039Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch039Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch039Neg20_integral_bounds
end HodgeProofHP
