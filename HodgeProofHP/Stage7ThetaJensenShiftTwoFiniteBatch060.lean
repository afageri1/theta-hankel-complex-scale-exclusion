/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch060

/-! Exact signed weight and batch integral certificates, batch 60 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch060Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-31177065239 / 62500000000 : ℝ)
  | 1 => (-252327293273 / 500000000000 : ℝ)
  | 2 => (-127633242349 / 250000000000 : ℝ)
  | 3 => (-129117164791 / 250000000000 : ℝ)
  | 4 => (-261231062923 / 500000000000 : ℝ)
  | 5 => (-528513842669 / 1000000000000 : ℝ)
  | 6 => (-534624286103 / 1000000000000 : ℝ)
  | 7 => (-540793935881 / 1000000000000 : ℝ)
  | 8 => (-547023275021 / 1000000000000 : ℝ)
  | 9 => (-6916409873 / 12500000000 : ℝ)
  | 10 => (-22386518799 / 40000000000 : ℝ)
  | 11 => (-566074308401 / 1000000000000 : ℝ)
  | 12 => (-11450946029 / 20000000000 : ℝ)
  | 13 => (-9048163263 / 15625000000 : ℝ)
  | 14 => (-11713605073 / 20000000000 : ℝ)
  | 15 => (-29617061121 / 50000000000 : ℝ)
  | 16 => (-119813173019 / 200000000000 : ℝ)
  | 17 => (-24234187803 / 40000000000 : ℝ)
  | 18 => (-306354114619 / 500000000000 : ℝ)
  | 19 => (-154906746987 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch060Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-493067877633 / 1000000000000 : ℝ)
  | 1 => (-498833043823 / 1000000000000 : ℝ)
  | 2 => (-100930917309 / 200000000000 : ℝ)
  | 3 => (-102106593879 / 200000000000 : ℝ)
  | 4 => (-516468659163 / 1000000000000 : ℝ)
  | 5 => (-104492425169 / 200000000000 : ℝ)
  | 6 => (-132128460667 / 250000000000 : ℝ)
  | 7 => (-267312143051 / 500000000000 : ℝ)
  | 8 => (-13519848397 / 25000000000 : ℝ)
  | 9 => (-27351163751 / 50000000000 : ℝ)
  | 10 => (-553312789839 / 1000000000000 : ℝ)
  | 11 => (-279831484987 / 500000000000 : ℝ)
  | 12 => (-1415185771 / 2500000000 : ℝ)
  | 13 => (-572547301449 / 1000000000000 : ℝ)
  | 14 => (-579082448831 / 1000000000000 : ℝ)
  | 15 => (-585680253649 / 1000000000000 : ℝ)
  | 16 => (-592341222419 / 1000000000000 : ℝ)
  | 17 => (-299532932547 / 500000000000 : ℝ)
  | 18 => (-302927347537 / 500000000000 : ℝ)
  | 19 => (-612708229237 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch060Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1200 : ℝ) + (j.val : ℝ)) / 1600)
      (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch060Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch060Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1200 : ℝ) + (j.val : ℝ)) / 1600)
    (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch060Neg100WeightLower j.val) (hpThetaShiftTwoBatch060Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch060Neg100WeightLower, hpThetaShiftTwoBatch060Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch060Neg100_integral_bounds :
    (-192424903 / 20000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-580738529 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch060Lower hpThetaJensenCellsBatch060Upper
    hpThetaShiftTwoBatch060Neg100WeightLower hpThetaShiftTwoBatch060Neg100WeightUpper hpThetaJensenCellsBatch060_bounds hpThetaShiftTwoBatch060Neg100_weight_bounds
  have hl : (-192424903 / 20000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch060Lower j * hpThetaShiftTwoBatch060Neg100WeightLower j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftTwoBatch060Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftTwoBatch060Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch060Lower j * hpThetaShiftTwoBatch060Neg100WeightUpper j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftTwoBatch060Neg100WeightUpper j) / 1600) ≤ (-580738529 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftTwoBatch060Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1200 : ℝ) / 1600 = 60 / 80 by norm_num,
    show ((1200 : ℝ) + 20) / 1600 = (60 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch060Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-19532436557 / 1000000000000 : ℝ)
  | 1 => (-10064820319 / 500000000000 : ℝ)
  | 2 => (-20735413453 / 1000000000000 : ℝ)
  | 3 => (-21349842659 / 1000000000000 : ℝ)
  | 4 => (-4394603321 / 200000000000 : ℝ)
  | 5 => (-22605024339 / 1000000000000 : ℝ)
  | 6 => (-5811488903 / 250000000000 : ℝ)
  | 7 => (-23895900879 / 1000000000000 : ℝ)
  | 8 => (-1534684457 / 62500000000 : ℝ)
  | 9 => (-3152899849 / 125000000000 : ℝ)
  | 10 => (-12950367963 / 500000000000 : ℝ)
  | 11 => (-13293828021 / 500000000000 : ℝ)
  | 12 => (-13642026599 / 500000000000 : ℝ)
  | 13 => (-13995011093 / 500000000000 : ℝ)
  | 14 => (-3588207317 / 125000000000 : ℝ)
  | 15 => (-14715529261 / 500000000000 : ℝ)
  | 16 => (-30166319161 / 1000000000000 : ℝ)
  | 17 => (-7727884557 / 250000000000 : ℝ)
  | 18 => (-3958351781 / 125000000000 : ℝ)
  | 19 => (-32432246513 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch060Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4735928561 / 250000000000 : ℝ)
  | 1 => (-4883109139 / 250000000000 : ℝ)
  | 2 => (-20129640637 / 1000000000000 : ℝ)
  | 3 => (-5183853363 / 250000000000 : ℝ)
  | 4 => (-10674921329 / 500000000000 : ℝ)
  | 5 => (-5493254151 / 250000000000 : ℝ)
  | 6 => (-11302512169 / 500000000000 : ℝ)
  | 7 => (-23245955611 / 1000000000000 : ℝ)
  | 8 => (-11947950439 / 500000000000 : ℝ)
  | 9 => (-24554951311 / 1000000000000 : ℝ)
  | 10 => (-25223198791 / 1000000000000 : ℝ)
  | 11 => (-1036029437 / 40000000000 : ℝ)
  | 12 => (-26587656041 / 1000000000000 : ℝ)
  | 13 => (-27284053197 / 1000000000000 : ℝ)
  | 14 => (-5598004437 / 200000000000 : ℝ)
  | 15 => (-5741131707 / 200000000000 : ℝ)
  | 16 => (-29431058521 / 1000000000000 : ℝ)
  | 17 => (-754157979 / 25000000000 : ℝ)
  | 18 => (-30911538227 / 1000000000000 : ℝ)
  | 19 => (-31666814247 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch060Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1200 : ℝ) + (j.val : ℝ)) / 1600)
      (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch060Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch060Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1200 : ℝ) + (j.val : ℝ)) / 1600)
    (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch060Neg65WeightLower j.val) (hpThetaShiftTwoBatch060Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch060Neg65WeightLower, hpThetaShiftTwoBatch060Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch060Neg65_integral_bounds :
    (-55064741 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-209481157 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch060Lower hpThetaJensenCellsBatch060Upper
    hpThetaShiftTwoBatch060Neg65WeightLower hpThetaShiftTwoBatch060Neg65WeightUpper hpThetaJensenCellsBatch060_bounds hpThetaShiftTwoBatch060Neg65_weight_bounds
  have hl : (-55064741 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch060Lower j * hpThetaShiftTwoBatch060Neg65WeightLower j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftTwoBatch060Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftTwoBatch060Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch060Lower j * hpThetaShiftTwoBatch060Neg65WeightUpper j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftTwoBatch060Neg65WeightUpper j) / 1600) ≤ (-209481157 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftTwoBatch060Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1200 : ℝ) / 1600 = 60 / 80 by norm_num,
    show ((1200 : ℝ) + 20) / 1600 = (60 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch060Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (18462066139 / 1000000000000 : ℝ)
  | 1 => (18547899191 / 1000000000000 : ℝ)
  | 2 => (18633239113 / 1000000000000 : ℝ)
  | 3 => (935903591 / 50000000000 : ℝ)
  | 4 => (18802383073 / 1000000000000 : ℝ)
  | 5 => (18886158473 / 1000000000000 : ℝ)
  | 6 => (2371172933 / 125000000000 : ℝ)
  | 7 => (19052043333 / 1000000000000 : ℝ)
  | 8 => (19134123203 / 1000000000000 : ℝ)
  | 9 => (19215608037 / 1000000000000 : ℝ)
  | 10 => (9648241317 / 500000000000 : ℝ)
  | 11 => (1937673163 / 100000000000 : ℝ)
  | 12 => (2432042437 / 125000000000 : ℝ)
  | 13 => (9767645267 / 500000000000 : ℝ)
  | 14 => (245169611 / 12500000000 : ℝ)
  | 15 => (9845579251 / 500000000000 : ℝ)
  | 16 => (4942010799 / 250000000000 : ℝ)
  | 17 => (19844206587 / 1000000000000 : ℝ)
  | 18 => (77811063 / 3906250000 : ℝ)
  | 19 => (19994303097 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch060Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2318487399 / 125000000000 : ℝ)
  | 1 => (9316619557 / 500000000000 : ℝ)
  | 2 => (18718071821 / 1000000000000 : ℝ)
  | 3 => (9401191537 / 500000000000 : ℝ)
  | 4 => (9443079237 / 500000000000 : ℝ)
  | 5 => (3793876693 / 200000000000 : ℝ)
  | 6 => (9526021667 / 500000000000 : ℝ)
  | 7 => (4783530801 / 250000000000 : ℝ)
  | 8 => (9607804019 / 500000000000 : ℝ)
  | 9 => (3859296527 / 200000000000 : ℝ)
  | 10 => (19376731631 / 1000000000000 : ℝ)
  | 11 => (19456339497 / 1000000000000 : ℝ)
  | 12 => (3907058107 / 200000000000 : ℝ)
  | 13 => (19613568881 / 1000000000000 : ℝ)
  | 14 => (19691158503 / 1000000000000 : ℝ)
  | 15 => (19768043197 / 1000000000000 : ℝ)
  | 16 => (4961051647 / 250000000000 : ℝ)
  | 17 => (19919632129 / 1000000000000 : ℝ)
  | 18 => (9997151549 / 500000000000 : ℝ)
  | 19 => (10034101299 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch060Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1200 : ℝ) + (j.val : ℝ)) / 1600)
      (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch060Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch060Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1200 : ℝ) + (j.val : ℝ)) / 1600)
    (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch060Neg45WeightLower j.val) (hpThetaShiftTwoBatch060Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch060Neg45WeightLower, hpThetaShiftTwoBatch060Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch060Neg45_integral_bounds :
    (65123543 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (334728941 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch060Lower hpThetaJensenCellsBatch060Upper
    hpThetaShiftTwoBatch060Neg45WeightLower hpThetaShiftTwoBatch060Neg45WeightUpper hpThetaJensenCellsBatch060_bounds hpThetaShiftTwoBatch060Neg45_weight_bounds
  have hl : (65123543 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch060Lower j * hpThetaShiftTwoBatch060Neg45WeightLower j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftTwoBatch060Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftTwoBatch060Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch060Lower j * hpThetaShiftTwoBatch060Neg45WeightUpper j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftTwoBatch060Neg45WeightUpper j) / 1600) ≤ (334728941 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftTwoBatch060Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1200 : ℝ) / 1600 = 60 / 80 by norm_num,
    show ((1200 : ℝ) + 20) / 1600 = (60 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch060Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2233398813 / 1000000000000 : ℝ)
  | 1 => (-2199064947 / 1000000000000 : ℝ)
  | 2 => (-432859987 / 200000000000 : ℝ)
  | 3 => (-532275383 / 250000000000 : ℝ)
  | 4 => (-2093467491 / 1000000000000 : ℝ)
  | 5 => (-2057395569 / 1000000000000 : ℝ)
  | 6 => (-2020883517 / 1000000000000 : ℝ)
  | 7 => (-198392909 / 100000000000 : ℝ)
  | 8 => (-1946530041 / 1000000000000 : ℝ)
  | 9 => (-1908684123 / 1000000000000 : ℝ)
  | 10 => (-58449659 / 31250000000 : ℝ)
  | 11 => (-1831642689 / 1000000000000 : ℝ)
  | 12 => (-44811067 / 25000000000 : ℝ)
  | 13 => (-876393407 / 500000000000 : ℝ)
  | 14 => (-1712672843 / 1000000000000 : ℝ)
  | 15 => (-836049261 / 500000000000 : ℝ)
  | 16 => (-407765401 / 250000000000 : ℝ)
  | 17 => (-317911969 / 200000000000 : ℝ)
  | 18 => (-1547591 / 1000000000 : ℝ)
  | 19 => (-60206113 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch060Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1099532473 / 500000000000 : ℝ)
  | 1 => (-1082149967 / 500000000000 : ℝ)
  | 2 => (-2129101531 / 1000000000000 : ℝ)
  | 3 => (-209346749 / 100000000000 : ℝ)
  | 4 => (-128587223 / 62500000000 : ℝ)
  | 5 => (-505220879 / 250000000000 : ℝ)
  | 6 => (-1983929089 / 1000000000000 : ℝ)
  | 7 => (-48663251 / 25000000000 : ℝ)
  | 8 => (-954342061 / 500000000000 : ℝ)
  | 9 => (-1870389087 / 1000000000000 : ℝ)
  | 10 => (-28619417 / 15625000000 : ℝ)
  | 11 => (-1792442679 / 1000000000000 : ℝ)
  | 12 => (-1752786813 / 1000000000000 : ℝ)
  | 13 => (-856336421 / 500000000000 : ℝ)
  | 14 => (-1672098521 / 1000000000000 : ℝ)
  | 15 => (-1631061603 / 1000000000000 : ℝ)
  | 16 => (-397389961 / 250000000000 : ℝ)
  | 17 => (-1547590999 / 1000000000000 : ℝ)
  | 18 => (-188144103 / 125000000000 : ℝ)
  | 19 => (-365560769 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch060Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1200 : ℝ) + (j.val : ℝ)) / 1600)
      (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch060Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch060Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1200 : ℝ) + (j.val : ℝ)) / 1600)
    (((1200 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch060Neg25WeightLower j.val) (hpThetaShiftTwoBatch060Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch060Neg25WeightLower, hpThetaShiftTwoBatch060Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch060Neg25_integral_bounds :
    (-32992349 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (60 / 80 : ℝ) ((60 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-31579659 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1200 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch060Lower hpThetaJensenCellsBatch060Upper
    hpThetaShiftTwoBatch060Neg25WeightLower hpThetaShiftTwoBatch060Neg25WeightUpper hpThetaJensenCellsBatch060_bounds hpThetaShiftTwoBatch060Neg25_weight_bounds
  have hl : (-32992349 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch060Lower j * hpThetaShiftTwoBatch060Neg25WeightLower j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftTwoBatch060Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftTwoBatch060Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch060Lower j * hpThetaShiftTwoBatch060Neg25WeightUpper j)
        (hpThetaJensenCellsBatch060Upper j * hpThetaShiftTwoBatch060Neg25WeightUpper j) / 1600) ≤ (-31579659 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch060Lower, hpThetaJensenCellsBatch060Upper,
      hpThetaShiftTwoBatch060Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1200 : ℝ) / 1600 = 60 / 80 by norm_num,
    show ((1200 : ℝ) + 20) / 1600 = (60 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch060Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch060Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch060Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch060Neg25_integral_bounds
end HodgeProofHP
