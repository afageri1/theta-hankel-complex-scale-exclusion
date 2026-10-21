/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch056

/-! Exact signed weight and batch integral certificates, batch 56 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch056Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1346065230381 / 125000000000 : ℝ)
  | 1 => (-339949791723 / 31250000000 : ℝ)
  | 2 => (-10989161984951 / 1000000000000 : ℝ)
  | 3 => (-11100833664753 / 1000000000000 : ℝ)
  | 4 => (-11213414277159 / 1000000000000 : ℝ)
  | 5 => (-11326909755261 / 1000000000000 : ℝ)
  | 6 => (-11441326062749 / 1000000000000 : ℝ)
  | 7 => (-11556669194031 / 1000000000000 : ℝ)
  | 8 => (-5836472587177 / 500000000000 : ℝ)
  | 9 => (-5895080029963 / 500000000000 : ℝ)
  | 10 => (-2977079984509 / 250000000000 : ℝ)
  | 11 => (-12027430927177 / 1000000000000 : ℝ)
  | 12 => (-12147499177171 / 1000000000000 : ℝ)
  | 13 => (-12268530869287 / 1000000000000 : ℝ)
  | 14 => (-774408263523 / 62500000000 : ℝ)
  | 15 => (-12513509462951 / 1000000000000 : ℝ)
  | 16 => (-6318734442697 / 500000000000 : ℝ)
  | 17 => (-12762416792001 / 1000000000000 : ℝ)
  | 18 => (-6444179761571 / 500000000000 : ℝ)
  | 19 => (-650765172569 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch056Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5329770833333 / 500000000000 : ℝ)
  | 1 => (-10768521843047 / 1000000000000 : ℝ)
  | 2 => (-2175678667027 / 200000000000 : ℝ)
  | 3 => (-219783239699 / 20000000000 : ℝ)
  | 4 => (-693802104047 / 62500000000 : ℝ)
  | 5 => (-5606707138579 / 500000000000 : ℝ)
  | 6 => (-566345487763 / 50000000000 : ℝ)
  | 7 => (-2860331515687 / 250000000000 : ℝ)
  | 8 => (-1155666919403 / 100000000000 : ℝ)
  | 9 => (-11672945174353 / 1000000000000 : ℝ)
  | 10 => (-471606402397 / 40000000000 : ℝ)
  | 11 => (-2381663987607 / 200000000000 : ℝ)
  | 12 => (-1503428865897 / 125000000000 : ℝ)
  | 13 => (-1214749917717 / 100000000000 : ℝ)
  | 14 => (-6134265434643 / 500000000000 : ℝ)
  | 15 => (-12390532216367 / 1000000000000 : ℝ)
  | 16 => (-250270189259 / 20000000000 : ℝ)
  | 17 => (-12637468885393 / 1000000000000 : ℝ)
  | 18 => (-1595302099 / 125000000 : ℝ)
  | 19 => (-12888359523141 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch056Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1120 : ℝ) + (j.val : ℝ)) / 1600)
      (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch056Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch056Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1120 : ℝ) + (j.val : ℝ)) / 1600)
    (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch056Neg100WeightLower j.val) (hpThetaShiftOneBatch056Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch056Neg100WeightLower, hpThetaShiftOneBatch056Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch056Neg100_integral_bounds :
    (-626910228807 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-607336232059 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch056Lower hpThetaJensenCellsBatch056Upper
    hpThetaShiftOneBatch056Neg100WeightLower hpThetaShiftOneBatch056Neg100WeightUpper hpThetaJensenCellsBatch056_bounds hpThetaShiftOneBatch056Neg100_weight_bounds
  have hl : (-626910228807 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch056Lower j * hpThetaShiftOneBatch056Neg100WeightLower j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftOneBatch056Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftOneBatch056Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch056Lower j * hpThetaShiftOneBatch056Neg100WeightUpper j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftOneBatch056Neg100WeightUpper j) / 1600) ≤ (-607336232059 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftOneBatch056Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1120 : ℝ) / 1600 = 56 / 80 by norm_num,
    show ((1120 : ℝ) + 20) / 1600 = (56 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch056Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-83478588661 / 125000000000 : ℝ)
  | 1 => (-170576848021 / 250000000000 : ℝ)
  | 2 => (-696949042267 / 1000000000000 : ℝ)
  | 3 => (-355877468549 / 500000000000 : ℝ)
  | 4 => (-726726361207 / 1000000000000 : ℝ)
  | 5 => (-5934916853 / 8000000000 : ℝ)
  | 6 => (-757170972817 / 1000000000000 : ℝ)
  | 7 => (-154529353343 / 200000000000 : ℝ)
  | 8 => (-98536662843 / 125000000000 : ℝ)
  | 9 => (-804111902857 / 1000000000000 : ℝ)
  | 10 => (-410051948283 / 500000000000 : ℝ)
  | 11 => (-52266913811 / 62500000000 : ℝ)
  | 12 => (-213153355203 / 250000000000 : ℝ)
  | 13 => (-173826729691 / 200000000000 : ℝ)
  | 14 => (-885832663973 / 1000000000000 : ℝ)
  | 15 => (-56419489697 / 62500000000 : ℝ)
  | 16 => (-91977253753 / 100000000000 : ℝ)
  | 17 => (-468508077213 / 500000000000 : ℝ)
  | 18 => (-477222038489 / 500000000000 : ℝ)
  | 19 => (-972057704169 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch056Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-326755861979 / 500000000000 : ℝ)
  | 1 => (-667828709287 / 1000000000000 : ℝ)
  | 2 => (-682307392083 / 1000000000000 : ℝ)
  | 3 => (-348474521133 / 500000000000 : ℝ)
  | 4 => (-711754937097 / 1000000000000 : ℝ)
  | 5 => (-363363180603 / 500000000000 : ℝ)
  | 6 => (-23183268957 / 31250000000 : ℝ)
  | 7 => (-47323185801 / 62500000000 : ℝ)
  | 8 => (-386323383357 / 500000000000 : ℝ)
  | 9 => (-788293302743 / 1000000000000 : ℝ)
  | 10 => (-100513987857 / 125000000000 : ℝ)
  | 11 => (-164020779313 / 200000000000 : ℝ)
  | 12 => (-33450824839 / 40000000000 : ℝ)
  | 13 => (-852613420811 / 1000000000000 : ℝ)
  | 14 => (-434566824227 / 500000000000 : ℝ)
  | 15 => (-221458165993 / 250000000000 : ℝ)
  | 16 => (-902711835151 / 1000000000000 : ℝ)
  | 17 => (-919772537529 / 1000000000000 : ℝ)
  | 18 => (-37480646177 / 40000000000 : ℝ)
  | 19 => (-954444076977 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch056Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1120 : ℝ) + (j.val : ℝ)) / 1600)
      (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch056Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch056Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1120 : ℝ) + (j.val : ℝ)) / 1600)
    (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch056Neg65WeightLower j.val) (hpThetaShiftOneBatch056Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch056Neg65WeightLower, hpThetaShiftOneBatch056Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch056Neg65_integral_bounds :
    (-1339973397 / 31250000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-1645352687 / 40000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch056Lower hpThetaJensenCellsBatch056Upper
    hpThetaShiftOneBatch056Neg65WeightLower hpThetaShiftOneBatch056Neg65WeightUpper hpThetaJensenCellsBatch056_bounds hpThetaShiftOneBatch056Neg65_weight_bounds
  have hl : (-1339973397 / 31250000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch056Lower j * hpThetaShiftOneBatch056Neg65WeightLower j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftOneBatch056Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftOneBatch056Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch056Lower j * hpThetaShiftOneBatch056Neg65WeightUpper j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftOneBatch056Neg65WeightUpper j) / 1600) ≤ (-1645352687 / 40000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftOneBatch056Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1120 : ℝ) / 1600 = 56 / 80 by norm_num,
    show ((1120 : ℝ) + 20) / 1600 = (56 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch056Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (353845333333 / 1000000000000 : ℝ)
  | 1 => (355227736523 / 1000000000000 : ℝ)
  | 2 => (178300951293 / 500000000000 : ℝ)
  | 3 => (89491916319 / 250000000000 : ℝ)
  | 4 => (89831214257 / 250000000000 : ℝ)
  | 5 => (180336654477 / 500000000000 : ℝ)
  | 6 => (72402570167 / 200000000000 : ℝ)
  | 7 => (90835827779 / 250000000000 : ℝ)
  | 8 => (364664516897 / 1000000000000 : ℝ)
  | 9 => (365976293927 / 1000000000000 : ℝ)
  | 10 => (1836392333 / 5000000000 : ℝ)
  | 11 => (46071357243 / 125000000000 : ℝ)
  | 12 => (369853289619 / 1000000000000 : ℝ)
  | 13 => (371125581907 / 1000000000000 : ℝ)
  | 14 => (186193776853 / 500000000000 : ℝ)
  | 15 => (14945560901 / 40000000000 : ℝ)
  | 16 => (14995192179 / 40000000000 : ℝ)
  | 17 => (188054857131 / 500000000000 : ℝ)
  | 18 => (75465713037 / 200000000000 : ℝ)
  | 19 => (378536169121 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch056Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (88806934131 / 250000000000 : ℝ)
  | 1 => (356601902587 / 1000000000000 : ℝ)
  | 2 => (357967665277 / 1000000000000 : ℝ)
  | 3 => (359324857029 / 1000000000000 : ℝ)
  | 4 => (72134661791 / 200000000000 : ℝ)
  | 5 => (90503212709 / 250000000000 : ℝ)
  | 6 => (363343311117 / 1000000000000 : ℝ)
  | 7 => (182332258449 / 500000000000 : ℝ)
  | 8 => (45747036741 / 125000000000 : ℝ)
  | 9 => (367278466601 / 1000000000000 : ℝ)
  | 10 => (73714171589 / 200000000000 : ℝ)
  | 11 => (18492664481 / 50000000000 : ℝ)
  | 12 => (92781395477 / 250000000000 : ℝ)
  | 13 => (372387553707 / 1000000000000 : ℝ)
  | 14 => (186819511263 / 500000000000 : ℝ)
  | 15 => (93719951119 / 250000000000 : ℝ)
  | 16 => (376109714263 / 1000000000000 : ℝ)
  | 17 => (188664282593 / 500000000000 : ℝ)
  | 18 => (189268084561 / 500000000000 : ℝ)
  | 19 => (23733271033 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch056Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1120 : ℝ) + (j.val : ℝ)) / 1600)
      (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch056Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch056Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1120 : ℝ) + (j.val : ℝ)) / 1600)
    (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch056Neg40WeightLower j.val) (hpThetaShiftOneBatch056Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch056Neg40WeightLower, hpThetaShiftOneBatch056Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch056Neg40_integral_bounds :
    (4750036089 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (2435808721 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch056Lower hpThetaJensenCellsBatch056Upper
    hpThetaShiftOneBatch056Neg40WeightLower hpThetaShiftOneBatch056Neg40WeightUpper hpThetaJensenCellsBatch056_bounds hpThetaShiftOneBatch056Neg40_weight_bounds
  have hl : (4750036089 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch056Lower j * hpThetaShiftOneBatch056Neg40WeightLower j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftOneBatch056Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftOneBatch056Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch056Lower j * hpThetaShiftOneBatch056Neg40WeightUpper j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftOneBatch056Neg40WeightUpper j) / 1600) ≤ (2435808721 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftOneBatch056Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1120 : ℝ) / 1600 = 56 / 80 by norm_num,
    show ((1120 : ℝ) + 20) / 1600 = (56 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch056Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-26762166667 / 500000000000 : ℝ)
  | 1 => (-26515064341 / 500000000000 : ℝ)
  | 2 => (-26265560931 / 500000000000 : ℝ)
  | 3 => (-5202729861 / 100000000000 : ℝ)
  | 4 => (-25759322353 / 500000000000 : ℝ)
  | 5 => (-12751286493 / 250000000000 : ℝ)
  | 6 => (-12621697069 / 250000000000 : ℝ)
  | 7 => (-12490889383 / 250000000000 : ℝ)
  | 8 => (-24717719849 / 500000000000 : ℝ)
  | 9 => (-24451210389 / 500000000000 : ℝ)
  | 10 => (-6045560853 / 125000000000 : ℝ)
  | 11 => (-373606437 / 7812500000 : ℝ)
  | 12 => (-2363690913 / 50000000000 : ℝ)
  | 13 => (-5840131999 / 125000000000 : ℝ)
  | 14 => (-46163323377 / 1000000000000 : ℝ)
  | 15 => (-4560060671 / 100000000000 : ℝ)
  | 16 => (-2814555771 / 62500000000 : ℝ)
  | 17 => (-44460166651 / 1000000000000 : ℝ)
  | 18 => (-21941208051 / 500000000000 : ℝ)
  | 19 => (-4329962719 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch056Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-53030128681 / 1000000000000 : ℝ)
  | 1 => (-52531121861 / 1000000000000 : ℝ)
  | 2 => (-52027298609 / 1000000000000 : ℝ)
  | 3 => (-10303728941 / 200000000000 : ℝ)
  | 4 => (-51005145971 / 1000000000000 : ℝ)
  | 5 => (-2019471531 / 40000000000 : ℝ)
  | 6 => (-49963557531 / 1000000000000 : ℝ)
  | 7 => (-49435439697 / 1000000000000 : ℝ)
  | 8 => (-48902420777 / 1000000000000 : ℝ)
  | 9 => (-48364486823 / 1000000000000 : ℝ)
  | 10 => (-9564324787 / 200000000000 : ℝ)
  | 11 => (-47273818259 / 1000000000000 : ℝ)
  | 12 => (-46721055991 / 1000000000000 : ℝ)
  | 13 => (-2885207711 / 62500000000 : ℝ)
  | 14 => (-45600606709 / 1000000000000 : ℝ)
  | 15 => (-9006578467 / 200000000000 : ℝ)
  | 16 => (-889203333 / 20000000000 : ℝ)
  | 17 => (-43882416101 / 1000000000000 : ℝ)
  | 18 => (-43299627189 / 1000000000000 : ℝ)
  | 19 => (-42711786467 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch056Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1120 : ℝ) + (j.val : ℝ)) / 1600)
      (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch056Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch056Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1120 : ℝ) + (j.val : ℝ)) / 1600)
    (((1120 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch056Neg20WeightLower j.val) (hpThetaShiftOneBatch056Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch056Neg20WeightLower, hpThetaShiftOneBatch056Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch056Neg20_integral_bounds :
    (-2589016459 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (56 / 80 : ℝ) ((56 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-1252712181 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1120 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch056Lower hpThetaJensenCellsBatch056Upper
    hpThetaShiftOneBatch056Neg20WeightLower hpThetaShiftOneBatch056Neg20WeightUpper hpThetaJensenCellsBatch056_bounds hpThetaShiftOneBatch056Neg20_weight_bounds
  have hl : (-2589016459 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch056Lower j * hpThetaShiftOneBatch056Neg20WeightLower j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftOneBatch056Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftOneBatch056Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch056Lower j * hpThetaShiftOneBatch056Neg20WeightUpper j)
        (hpThetaJensenCellsBatch056Upper j * hpThetaShiftOneBatch056Neg20WeightUpper j) / 1600) ≤ (-1252712181 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch056Lower, hpThetaJensenCellsBatch056Upper,
      hpThetaShiftOneBatch056Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1120 : ℝ) / 1600 = 56 / 80 by norm_num,
    show ((1120 : ℝ) + 20) / 1600 = (56 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch056Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch056Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch056Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch056Neg20_integral_bounds
end HodgeProofHP
