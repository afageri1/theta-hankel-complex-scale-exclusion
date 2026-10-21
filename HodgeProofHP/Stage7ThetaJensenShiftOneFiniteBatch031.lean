/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch031

/-! Exact signed weight and batch integral certificates, batch 31 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch031Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (11039655331 / 200000000000 : ℝ)
  | 1 => (56092631853 / 1000000000000 : ℝ)
  | 2 => (56991695757 / 1000000000000 : ℝ)
  | 3 => (7236926117 / 125000000000 : ℝ)
  | 4 => (58803710459 / 1000000000000 : ℝ)
  | 5 => (14929134469 / 250000000000 : ℝ)
  | 6 => (12126765441 / 200000000000 : ℝ)
  | 7 => (15388878229 / 250000000000 : ℝ)
  | 8 => (31240763957 / 500000000000 : ℝ)
  | 9 => (63411803521 / 1000000000000 : ℝ)
  | 10 => (8043283683 / 125000000000 : ℝ)
  | 11 => (13056970771 / 200000000000 : ℝ)
  | 12 => (8278435397 / 125000000000 : ℝ)
  | 13 => (67174082263 / 1000000000000 : ℝ)
  | 14 => (4257785893 / 62500000000 : ℝ)
  | 15 => (34539440371 / 500000000000 : ℝ)
  | 16 => (70036921419 / 1000000000000 : ℝ)
  | 17 => (70998614401 / 1000000000000 : ℝ)
  | 18 => (17990969009 / 250000000000 : ℝ)
  | 19 => (2917304837 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch031Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (28046315927 / 500000000000 : ℝ)
  | 1 => (28495847879 / 500000000000 : ℝ)
  | 2 => (57895408937 / 1000000000000 : ℝ)
  | 3 => (2940185523 / 50000000000 : ℝ)
  | 4 => (59716537877 / 1000000000000 : ℝ)
  | 5 => (30316913603 / 500000000000 : ℝ)
  | 6 => (61555512917 / 1000000000000 : ℝ)
  | 7 => (12496305583 / 200000000000 : ℝ)
  | 8 => (31705901761 / 500000000000 : ℝ)
  | 9 => (12869253893 / 200000000000 : ℝ)
  | 10 => (2040151683 / 31250000000 : ℝ)
  | 11 => (66227483177 / 1000000000000 : ℝ)
  | 12 => (8396760283 / 125000000000 : ℝ)
  | 13 => (68124574289 / 1000000000000 : ℝ)
  | 14 => (69078880743 / 1000000000000 : ℝ)
  | 15 => (3501846071 / 50000000000 : ℝ)
  | 16 => (35499307201 / 500000000000 : ℝ)
  | 17 => (71963876037 / 1000000000000 : ℝ)
  | 18 => (36466310463 / 500000000000 : ℝ)
  | 19 => (14780952381 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch031Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((620 : ℝ) + (j.val : ℝ)) / 1600)
      (((620 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch031Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch031Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((620 : ℝ) + (j.val : ℝ)) / 1600)
    (((620 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch031Neg100WeightLower j.val) (hpThetaShiftOneBatch031Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch031Neg100WeightLower, hpThetaShiftOneBatch031Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch031Neg100_integral_bounds :
    (14451077427 / 50000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (74379554089 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (620 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch031Lower hpThetaJensenCellsBatch031Upper
    hpThetaShiftOneBatch031Neg100WeightLower hpThetaShiftOneBatch031Neg100WeightUpper hpThetaJensenCellsBatch031_bounds hpThetaShiftOneBatch031Neg100_weight_bounds
  have hl : (14451077427 / 50000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch031Lower j * hpThetaShiftOneBatch031Neg100WeightLower j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftOneBatch031Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftOneBatch031Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch031Lower j * hpThetaShiftOneBatch031Neg100WeightUpper j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftOneBatch031Neg100WeightUpper j) / 1600) ≤ (74379554089 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftOneBatch031Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (620 : ℝ) / 1600 = 31 / 80 by norm_num,
    show ((620 : ℝ) + 20) / 1600 = (31 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch031Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8405047607 / 500000000000 : ℝ)
  | 1 => (-8270469691 / 500000000000 : ℝ)
  | 2 => (-16267002527 / 1000000000000 : ℝ)
  | 3 => (-319765177 / 20000000000 : ℝ)
  | 4 => (-3140936539 / 200000000000 : ℝ)
  | 5 => (-7708124273 / 500000000000 : ℝ)
  | 6 => (-3024586207 / 200000000000 : ℝ)
  | 7 => (-926544059 / 62500000000 : ℝ)
  | 8 => (-14521545207 / 1000000000000 : ℝ)
  | 9 => (-14213426917 / 1000000000000 : ℝ)
  | 10 => (-3475081331 / 250000000000 : ℝ)
  | 11 => (-3395553961 / 250000000000 : ℝ)
  | 12 => (-13259074059 / 1000000000000 : ℝ)
  | 13 => (-3232718931 / 250000000000 : ℝ)
  | 14 => (-6298798383 / 500000000000 : ℝ)
  | 15 => (-1225921329 / 100000000000 : ℝ)
  | 16 => (-744731349 / 62500000000 : ℝ)
  | 17 => (-289175953 / 25000000000 : ℝ)
  | 18 => (-280329989 / 25000000000 : ℝ)
  | 19 => (-10854162757 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch031Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-16540939381 / 1000000000000 : ℝ)
  | 1 => (-8133501263 / 500000000000 : ℝ)
  | 2 => (-15988258849 / 1000000000000 : ℝ)
  | 3 => (-7852341347 / 500000000000 : ℝ)
  | 4 => (-3083249709 / 200000000000 : ℝ)
  | 5 => (-7561465517 / 500000000000 : ℝ)
  | 6 => (-14824704943 / 1000000000000 : ℝ)
  | 7 => (-7260772603 / 500000000000 : ℝ)
  | 8 => (-3553356729 / 250000000000 : ℝ)
  | 9 => (-13900325323 / 1000000000000 : ℝ)
  | 10 => (-13582215843 / 1000000000000 : ℝ)
  | 11 => (-6629537029 / 500000000000 : ℝ)
  | 12 => (-12930875723 / 1000000000000 : ℝ)
  | 13 => (-2519519353 / 200000000000 : ℝ)
  | 14 => (-12259213289 / 1000000000000 : ℝ)
  | 15 => (-11915701583 / 1000000000000 : ℝ)
  | 16 => (-11567038119 / 1000000000000 : ℝ)
  | 17 => (-11213199559 / 1000000000000 : ℝ)
  | 18 => (-2713540689 / 250000000000 : ℝ)
  | 19 => (-10489904761 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch031Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((620 : ℝ) + (j.val : ℝ)) / 1600)
      (((620 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch031Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch031Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((620 : ℝ) + (j.val : ℝ)) / 1600)
    (((620 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch031Neg65WeightLower j.val) (hpThetaShiftOneBatch031Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch031Neg65WeightLower, hpThetaShiftOneBatch031Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch031Neg65_integral_bounds :
    (-4031869823 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-62158784923 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (620 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch031Lower hpThetaJensenCellsBatch031Upper
    hpThetaShiftOneBatch031Neg65WeightLower hpThetaShiftOneBatch031Neg65WeightUpper hpThetaJensenCellsBatch031_bounds hpThetaShiftOneBatch031Neg65_weight_bounds
  have hl : (-4031869823 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch031Lower j * hpThetaShiftOneBatch031Neg65WeightLower j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftOneBatch031Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftOneBatch031Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch031Lower j * hpThetaShiftOneBatch031Neg65WeightUpper j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftOneBatch031Neg65WeightUpper j) / 1600) ≤ (-62158784923 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftOneBatch031Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (620 : ℝ) / 1600 = 31 / 80 by norm_num,
    show ((620 : ℝ) + 20) / 1600 = (31 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch031Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8621499457 / 250000000000 : ℝ)
  | 1 => (-17318063107 / 500000000000 : ℝ)
  | 2 => (-34785118481 / 1000000000000 : ℝ)
  | 3 => (-34932956267 / 1000000000000 : ℝ)
  | 4 => (-17539810571 / 500000000000 : ℝ)
  | 5 => (-17612547301 / 500000000000 : ℝ)
  | 6 => (-35369358071 / 1000000000000 : ℝ)
  | 7 => (-7102478581 / 200000000000 : ℝ)
  | 8 => (-17827090193 / 500000000000 : ℝ)
  | 9 => (-35794701729 / 1000000000000 : ℝ)
  | 10 => (-17966969039 / 500000000000 : ℝ)
  | 11 => (-36071870507 / 1000000000000 : ℝ)
  | 12 => (-36208480021 / 1000000000000 : ℝ)
  | 13 => (-36343747559 / 1000000000000 : ℝ)
  | 14 => (-36477653989 / 1000000000000 : ℝ)
  | 15 => (-36610180113 / 1000000000000 : ℝ)
  | 16 => (-18370653333 / 500000000000 : ℝ)
  | 17 => (-18435507157 / 500000000000 : ℝ)
  | 18 => (-1849964183 / 50000000000 : ℝ)
  | 19 => (-37126095239 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch031Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4291843951 / 125000000000 : ℝ)
  | 1 => (-34485997827 / 1000000000000 : ℝ)
  | 2 => (-34636126213 / 1000000000000 : ℝ)
  | 3 => (-434813981 / 12500000000 : ℝ)
  | 4 => (-17466478133 / 500000000000 : ℝ)
  | 5 => (-35079621141 / 1000000000000 : ℝ)
  | 6 => (-35225094601 / 1000000000000 : ℝ)
  | 7 => (-3536935807 / 100000000000 : ℝ)
  | 8 => (-4439049113 / 125000000000 : ℝ)
  | 9 => (-7130836077 / 200000000000 : ℝ)
  | 10 => (-1118584429 / 31250000000 : ℝ)
  | 11 => (-35933938077 / 1000000000000 : ℝ)
  | 12 => (-18035935253 / 500000000000 : ℝ)
  | 13 => (-1810424001 / 50000000000 : ℝ)
  | 14 => (-18171873779 / 500000000000 : ℝ)
  | 15 => (-9119413497 / 250000000000 : ℝ)
  | 16 => (-2288136257 / 62500000000 : ℝ)
  | 17 => (-7348261333 / 200000000000 : ℝ)
  | 18 => (-36871014313 / 1000000000000 : ℝ)
  | 19 => (-36999283659 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch031Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((620 : ℝ) + (j.val : ℝ)) / 1600)
      (((620 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch031Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch031Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((620 : ℝ) + (j.val : ℝ)) / 1600)
    (((620 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch031Neg40WeightLower j.val) (hpThetaShiftOneBatch031Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch031Neg40WeightLower, hpThetaShiftOneBatch031Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch031Neg40_integral_bounds :
    (-3293469691 / 20000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-80840935449 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (620 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch031Lower hpThetaJensenCellsBatch031Upper
    hpThetaShiftOneBatch031Neg40WeightLower hpThetaShiftOneBatch031Neg40WeightUpper hpThetaJensenCellsBatch031_bounds hpThetaShiftOneBatch031Neg40_weight_bounds
  have hl : (-3293469691 / 20000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch031Lower j * hpThetaShiftOneBatch031Neg40WeightLower j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftOneBatch031Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftOneBatch031Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch031Lower j * hpThetaShiftOneBatch031Neg40WeightUpper j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftOneBatch031Neg40WeightUpper j) / 1600) ≤ (-80840935449 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftOneBatch031Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (620 : ℝ) / 1600 = 31 / 80 by norm_num,
    show ((620 : ℝ) + 20) / 1600 = (31 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch031Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-801340029 / 125000000000 : ℝ)
  | 1 => (-3300354609 / 500000000000 : ℝ)
  | 2 => (-271661307 / 40000000000 : ℝ)
  | 3 => (-6983188229 / 1000000000000 : ℝ)
  | 4 => (-7175673471 / 1000000000000 : ℝ)
  | 5 => (-3684492977 / 500000000000 : ℝ)
  | 6 => (-3781561597 / 500000000000 : ℝ)
  | 7 => (-7758082669 / 1000000000000 : ℝ)
  | 8 => (-7953861821 / 1000000000000 : ℝ)
  | 9 => (-1630091611 / 200000000000 : ℝ)
  | 10 => (-130435449 / 15625000000 : ℝ)
  | 11 => (-1709218239 / 200000000000 : ℝ)
  | 12 => (-4372561361 / 500000000000 : ℝ)
  | 13 => (-8944960573 / 1000000000000 : ℝ)
  | 14 => (-4572800981 / 500000000000 : ℝ)
  | 15 => (-9347044069 / 1000000000000 : ℝ)
  | 16 => (-9549284033 / 1000000000000 : ℝ)
  | 17 => (-9752318957 / 1000000000000 : ℝ)
  | 18 => (-4978072953 / 500000000000 : ℝ)
  | 19 => (-2032152381 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch031Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6221568053 / 1000000000000 : ℝ)
  | 1 => (-6410720231 / 1000000000000 : ℝ)
  | 2 => (-6600709217 / 1000000000000 : ℝ)
  | 3 => (-3395766337 / 500000000000 : ℝ)
  | 4 => (-1745797057 / 250000000000 : ℝ)
  | 5 => (-717567347 / 100000000000 : ℝ)
  | 6 => (-7368985953 / 1000000000000 : ℝ)
  | 7 => (-7563123193 / 1000000000000 : ℝ)
  | 8 => (-1939520667 / 250000000000 : ℝ)
  | 9 => (-397693091 / 50000000000 : ℝ)
  | 10 => (-4075229027 / 500000000000 : ℝ)
  | 11 => (-1669573747 / 200000000000 : ℝ)
  | 12 => (-4273045597 / 500000000000 : ℝ)
  | 13 => (-8745122721 / 1000000000000 : ℝ)
  | 14 => (-2236240143 / 250000000000 : ℝ)
  | 15 => (-9145601961 / 1000000000000 : ℝ)
  | 16 => (-2336761017 / 250000000000 : ℝ)
  | 17 => (-149207563 / 15625000000 : ℝ)
  | 18 => (-2438079739 / 250000000000 : ℝ)
  | 19 => (-1991229181 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch031Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((620 : ℝ) + (j.val : ℝ)) / 1600)
      (((620 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch031Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch031Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((620 : ℝ) + (j.val : ℝ)) / 1600)
    (((620 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch031Neg20WeightLower j.val) (hpThetaShiftOneBatch031Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch031Neg20WeightLower, hpThetaShiftOneBatch031Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch031Neg20_integral_bounds :
    (-18911352647 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (31 / 80 : ℝ) ((31 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-18194473357 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (620 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch031Lower hpThetaJensenCellsBatch031Upper
    hpThetaShiftOneBatch031Neg20WeightLower hpThetaShiftOneBatch031Neg20WeightUpper hpThetaJensenCellsBatch031_bounds hpThetaShiftOneBatch031Neg20_weight_bounds
  have hl : (-18911352647 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch031Lower j * hpThetaShiftOneBatch031Neg20WeightLower j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftOneBatch031Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftOneBatch031Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch031Lower j * hpThetaShiftOneBatch031Neg20WeightUpper j)
        (hpThetaJensenCellsBatch031Upper j * hpThetaShiftOneBatch031Neg20WeightUpper j) / 1600) ≤ (-18194473357 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch031Lower, hpThetaJensenCellsBatch031Upper,
      hpThetaShiftOneBatch031Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (620 : ℝ) / 1600 = 31 / 80 by norm_num,
    show ((620 : ℝ) + 20) / 1600 = (31 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch031Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch031Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch031Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch031Neg20_integral_bounds
end HodgeProofHP
