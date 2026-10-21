/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch004

/-! Exact signed weight and batch integral certificates, batch 4 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch004Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (548816499 / 500000000000 : ℝ)
  | 1 => (22428359 / 20000000000 : ℝ)
  | 2 => (71582013 / 62500000000 : ℝ)
  | 3 => (1169309261 / 1000000000000 : ℝ)
  | 4 => (1193402543 / 1000000000000 : ℝ)
  | 5 => (152198179 / 125000000000 : ℝ)
  | 6 => (1241851249 / 1000000000000 : ℝ)
  | 7 => (253238653 / 200000000000 : ℝ)
  | 8 => (1290604693 / 1000000000000 : ℝ)
  | 9 => (657539349 / 500000000000 : ℝ)
  | 10 => (167451049 / 125000000000 : ℝ)
  | 11 => (272837367 / 200000000000 : ℝ)
  | 12 => (2170011 / 1562500000 : ℝ)
  | 13 => (1413461969 / 1000000000000 : ℝ)
  | 14 => (719072269 / 500000000000 : ℝ)
  | 15 => (292569523 / 200000000000 : ℝ)
  | 16 => (743782011 / 500000000000 : ℝ)
  | 17 => (1512286537 / 1000000000000 : ℝ)
  | 18 => (1537007893 / 1000000000000 : ℝ)
  | 19 => (1561720779 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch004Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1121417951 / 1000000000000 : ℝ)
  | 1 => (1145312209 / 1000000000000 : ℝ)
  | 2 => (584654631 / 500000000000 : ℝ)
  | 3 => (74587659 / 62500000000 : ℝ)
  | 4 => (1217585433 / 1000000000000 : ℝ)
  | 5 => (993481 / 800000000 : ℝ)
  | 6 => (633096633 / 500000000000 : ℝ)
  | 7 => (645302347 / 500000000000 : ℝ)
  | 8 => (1315078699 / 1000000000000 : ℝ)
  | 9 => (1339608393 / 1000000000000 : ℝ)
  | 10 => (341046709 / 250000000000 : ℝ)
  | 11 => (1388807041 / 1000000000000 : ℝ)
  | 12 => (141346197 / 100000000000 : ℝ)
  | 13 => (1438144539 / 1000000000000 : ℝ)
  | 14 => (11428497 / 7812500000 : ℝ)
  | 15 => (1487564023 / 1000000000000 : ℝ)
  | 16 => (756143269 / 500000000000 : ℝ)
  | 17 => (768503947 / 500000000000 : ℝ)
  | 18 => (78086039 / 50000000000 : ℝ)
  | 19 => (317283569 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch004Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((80 : ℝ) + (j.val : ℝ)) / 1600)
      (((80 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch004Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch004Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((80 : ℝ) + (j.val : ℝ)) / 1600)
    (((80 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch004Neg100WeightLower j.val) (hpThetaShiftOneBatch004Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch004Neg100WeightLower, hpThetaShiftOneBatch004Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch004Neg100_integral_bounds :
    (5729371409 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (3686263241 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (80 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch004Lower hpThetaJensenCellsBatch004Upper
    hpThetaShiftOneBatch004Neg100WeightLower hpThetaShiftOneBatch004Neg100WeightUpper hpThetaJensenCellsBatch004_bounds hpThetaShiftOneBatch004Neg100_weight_bounds
  have hl : (5729371409 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch004Lower j * hpThetaShiftOneBatch004Neg100WeightLower j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftOneBatch004Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftOneBatch004Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch004Lower j * hpThetaShiftOneBatch004Neg100WeightUpper j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftOneBatch004Neg100WeightUpper j) / 1600) ≤ (3686263241 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftOneBatch004Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (80 : ℝ) / 1600 = 4 / 80 by norm_num,
    show ((80 : ℝ) + 20) / 1600 = (4 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch004Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (230016301 / 200000000000 : ℝ)
  | 1 => (1176479727 / 1000000000000 : ℝ)
  | 2 => (60154071 / 50000000000 : ℝ)
  | 3 => (1229882139 / 1000000000000 : ℝ)
  | 4 => (1256877393 / 1000000000000 : ℝ)
  | 5 => (1284062649 / 1000000000000 : ℝ)
  | 6 => (1311433327 / 1000000000000 : ℝ)
  | 7 => (1338984807 / 1000000000000 : ℝ)
  | 8 => (1366712423 / 1000000000000 : ℝ)
  | 9 => (1394611469 / 1000000000000 : ℝ)
  | 10 => (711338597 / 500000000000 : ℝ)
  | 11 => (725452403 / 500000000000 : ℝ)
  | 12 => (1479289473 / 1000000000000 : ℝ)
  | 13 => (1507826319 / 1000000000000 : ℝ)
  | 14 => (153651043 / 100000000000 : ℝ)
  | 15 => (31306737 / 20000000000 : ℝ)
  | 16 => (1594300583 / 1000000000000 : ℝ)
  | 17 => (811698297 / 500000000000 : ℝ)
  | 18 => (1652619809 / 1000000000000 : ℝ)
  | 19 => (840982557 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch004Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (73529983 / 62500000000 : ℝ)
  | 1 => (1203081421 / 1000000000000 : ℝ)
  | 2 => (61494107 / 50000000000 : ℝ)
  | 3 => (628438697 / 500000000000 : ℝ)
  | 4 => (25681253 / 20000000000 : ℝ)
  | 5 => (81964583 / 62500000000 : ℝ)
  | 6 => (167373101 / 125000000000 : ℝ)
  | 7 => (170839053 / 125000000000 : ℝ)
  | 8 => (139461147 / 100000000000 : ℝ)
  | 9 => (284535439 / 200000000000 : ℝ)
  | 10 => (1450904807 / 1000000000000 : ℝ)
  | 11 => (739644737 / 500000000000 : ℝ)
  | 12 => (18847829 / 12500000000 : ℝ)
  | 13 => (1536510431 / 1000000000000 : ℝ)
  | 14 => (1565336851 / 1000000000000 : ℝ)
  | 15 => (199287573 / 125000000000 : ℝ)
  | 16 => (324679319 / 200000000000 : ℝ)
  | 17 => (165261981 / 100000000000 : ℝ)
  | 18 => (336393023 / 200000000000 : ℝ)
  | 19 => (1711427359 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch004Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((80 : ℝ) + (j.val : ℝ)) / 1600)
      (((80 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch004Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch004Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((80 : ℝ) + (j.val : ℝ)) / 1600)
    (((80 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch004Neg65WeightLower j.val) (hpThetaShiftOneBatch004Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch004Neg65WeightLower, hpThetaShiftOneBatch004Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch004Neg65_integral_bounds :
    (7609826743 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (6276209757 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (80 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch004Lower hpThetaJensenCellsBatch004Upper
    hpThetaShiftOneBatch004Neg65WeightLower hpThetaShiftOneBatch004Neg65WeightUpper hpThetaJensenCellsBatch004_bounds hpThetaShiftOneBatch004Neg65_weight_bounds
  have hl : (7609826743 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch004Lower j * hpThetaShiftOneBatch004Neg65WeightLower j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftOneBatch004Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftOneBatch004Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch004Lower j * hpThetaShiftOneBatch004Neg65WeightUpper j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftOneBatch004Neg65WeightUpper j) / 1600) ≤ (6276209757 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftOneBatch004Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (80 : ℝ) / 1600 = 4 / 80 by norm_num,
    show ((80 : ℝ) + 20) / 1600 = (4 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch004Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1188123511 / 1000000000000 : ℝ)
  | 1 => (1216432949 / 1000000000000 : ℝ)
  | 2 => (1245015939 / 1000000000000 : ℝ)
  | 3 => (25477393 / 20000000000 : ℝ)
  | 4 => (65149561 / 50000000000 : ℝ)
  | 5 => (1332377757 / 1000000000000 : ℝ)
  | 6 => (681013169 / 500000000000 : ℝ)
  | 7 => (173991751 / 125000000000 : ℝ)
  | 8 => (284419557 / 200000000000 : ℝ)
  | 9 => (726257327 / 500000000000 : ℝ)
  | 10 => (148318157 / 100000000000 : ℝ)
  | 11 => (75704773 / 50000000000 : ℝ)
  | 12 => (77262661 / 50000000000 : ℝ)
  | 13 => (315330343 / 200000000000 : ℝ)
  | 14 => (201035973 / 125000000000 : ℝ)
  | 15 => (1640158233 / 1000000000000 : ℝ)
  | 16 => (1672259841 / 1000000000000 : ℝ)
  | 17 => (852294679 / 500000000000 : ℝ)
  | 18 => (108571469 / 62500000000 : ℝ)
  | 19 => (442479743 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch004Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (24328659 / 20000000000 : ℝ)
  | 1 => (62250797 / 50000000000 : ℝ)
  | 2 => (1273869651 / 1000000000000 : ℝ)
  | 3 => (1302991221 / 1000000000000 : ℝ)
  | 4 => (666188879 / 500000000000 : ℝ)
  | 5 => (1362026339 / 1000000000000 : ℝ)
  | 6 => (1391934009 / 1000000000000 : ℝ)
  | 7 => (711048893 / 500000000000 : ℝ)
  | 8 => (290502931 / 200000000000 : ℝ)
  | 9 => (1483181571 / 1000000000000 : ℝ)
  | 10 => (1514095461 / 1000000000000 : ℝ)
  | 11 => (1545253221 / 1000000000000 : ℝ)
  | 12 => (394162929 / 250000000000 : ℝ)
  | 13 => (321657557 / 200000000000 : ℝ)
  | 14 => (820079117 / 500000000000 : ℝ)
  | 15 => (836129921 / 500000000000 : ℝ)
  | 16 => (1704589359 / 1000000000000 : ℝ)
  | 17 => (347428701 / 200000000000 : ℝ)
  | 18 => (1769918973 / 1000000000000 : ℝ)
  | 19 => (901456213 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch004Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((80 : ℝ) + (j.val : ℝ)) / 1600)
      (((80 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch004Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch004Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((80 : ℝ) + (j.val : ℝ)) / 1600)
    (((80 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch004Neg40WeightLower j.val) (hpThetaShiftOneBatch004Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch004Neg40WeightLower, hpThetaShiftOneBatch004Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch004Neg40_integral_bounds :
    (1269820447 / 40000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (511869427 / 15625000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (80 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch004Lower hpThetaJensenCellsBatch004Upper
    hpThetaShiftOneBatch004Neg40WeightLower hpThetaShiftOneBatch004Neg40WeightUpper hpThetaJensenCellsBatch004_bounds hpThetaShiftOneBatch004Neg40_weight_bounds
  have hl : (1269820447 / 40000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch004Lower j * hpThetaShiftOneBatch004Neg40WeightLower j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftOneBatch004Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftOneBatch004Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch004Lower j * hpThetaShiftOneBatch004Neg40WeightUpper j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftOneBatch004Neg40WeightUpper j) / 1600) ≤ (511869427 / 15625000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftOneBatch004Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (80 : ℝ) / 1600 = 4 / 80 by norm_num,
    show ((80 : ℝ) + 20) / 1600 = (4 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch004Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1218906063 / 1000000000000 : ℝ)
  | 1 => (624385703 / 500000000000 : ℝ)
  | 2 => (159871009 / 125000000000 : ℝ)
  | 3 => (81843413 / 62500000000 : ℝ)
  | 4 => (167543693 / 125000000000 : ℝ)
  | 5 => (10715089 / 7812500000 : ℝ)
  | 6 => (175379831 / 125000000000 : ℝ)
  | 7 => (1434869791 / 1000000000000 : ℝ)
  | 8 => (733511641 / 500000000000 : ℝ)
  | 9 => (46859299 / 31250000000 : ℝ)
  | 10 => (766145539 / 500000000000 : ℝ)
  | 11 => (97837639 / 62500000000 : ℝ)
  | 12 => (1598829401 / 1000000000000 : ℝ)
  | 13 => (1632570989 / 1000000000000 : ℝ)
  | 14 => (33332507 / 20000000000 : ℝ)
  | 15 => (170099083 / 100000000000 : ℝ)
  | 16 => (10847911 / 6250000000 : ℝ)
  | 17 => (442662113 / 250000000000 : ℝ)
  | 18 => (1805937203 / 1000000000000 : ℝ)
  | 19 => (368306059 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch004Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1248771407 / 1000000000000 : ℝ)
  | 1 => (1278968073 / 1000000000000 : ℝ)
  | 2 => (1309494609 / 1000000000000 : ℝ)
  | 3 => (268069909 / 200000000000 : ℝ)
  | 4 => (1371531393 / 1000000000000 : ℝ)
  | 5 => (1403038649 / 1000000000000 : ℝ)
  | 6 => (44839681 / 31250000000 : ℝ)
  | 7 => (1467023283 / 1000000000000 : ℝ)
  | 8 => (1499497569 / 1000000000000 : ℝ)
  | 9 => (1532291079 / 1000000000000 : ℝ)
  | 10 => (62616089 / 40000000000 : ℝ)
  | 11 => (799414701 / 500000000000 : ℝ)
  | 12 => (163257099 / 100000000000 : ℝ)
  | 13 => (1666625351 / 1000000000000 : ℝ)
  | 14 => (1700990831 / 1000000000000 : ℝ)
  | 15 => (1735665761 / 1000000000000 : ℝ)
  | 16 => (1770648453 / 1000000000000 : ℝ)
  | 17 => (451484301 / 250000000000 : ℝ)
  | 18 => (230191287 / 125000000000 : ℝ)
  | 19 => (1877425993 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch004Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((80 : ℝ) + (j.val : ℝ)) / 1600)
      (((80 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch004Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch004Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((80 : ℝ) + (j.val : ℝ)) / 1600)
    (((80 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch004Neg20WeightLower j.val) (hpThetaShiftOneBatch004Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch004Neg20WeightLower, hpThetaShiftOneBatch004Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch004Neg20_integral_bounds :
    (4100762899 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (4 / 80 : ℝ) ((4 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (33879380679 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (80 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch004Lower hpThetaJensenCellsBatch004Upper
    hpThetaShiftOneBatch004Neg20WeightLower hpThetaShiftOneBatch004Neg20WeightUpper hpThetaJensenCellsBatch004_bounds hpThetaShiftOneBatch004Neg20_weight_bounds
  have hl : (4100762899 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch004Lower j * hpThetaShiftOneBatch004Neg20WeightLower j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftOneBatch004Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftOneBatch004Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch004Lower j * hpThetaShiftOneBatch004Neg20WeightUpper j)
        (hpThetaJensenCellsBatch004Upper j * hpThetaShiftOneBatch004Neg20WeightUpper j) / 1600) ≤ (33879380679 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch004Lower, hpThetaJensenCellsBatch004Upper,
      hpThetaShiftOneBatch004Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (80 : ℝ) / 1600 = 4 / 80 by norm_num,
    show ((80 : ℝ) + 20) / 1600 = (4 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch004Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch004Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch004Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch004Neg20_integral_bounds
end HodgeProofHP
