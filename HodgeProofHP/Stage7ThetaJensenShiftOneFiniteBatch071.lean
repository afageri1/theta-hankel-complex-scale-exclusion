/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch071

/-! Exact signed weight and batch integral certificates, batch 71 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch071Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-122876891710991 / 1000000000000 : ℝ)
  | 1 => (-61850777960037 / 500000000000 : ℝ)
  | 2 => (-124530901232441 / 1000000000000 : ℝ)
  | 3 => (-62682474876961 / 500000000000 : ℝ)
  | 4 => (-126203723675043 / 1000000000000 : ℝ)
  | 5 => (-127047245271283 / 1000000000000 : ℝ)
  | 6 => (-31973884225831 / 250000000000 : ℝ)
  | 7 => (-128748621017309 / 1000000000000 : ℝ)
  | 8 => (-64803260072547 / 500000000000 : ℝ)
  | 9 => (-26093851380901 / 200000000000 : ℝ)
  | 10 => (-26267370799919 / 200000000000 : ℝ)
  | 11 => (-132209334220899 / 1000000000000 : ℝ)
  | 12 => (-33271680111423 / 250000000000 : ℝ)
  | 13 => (-16746129454781 / 125000000000 : ℝ)
  | 14 => (-26971260570019 / 200000000000 : ℝ)
  | 15 => (-135748545220279 / 1000000000000 : ℝ)
  | 16 => (-136645785975619 / 1000000000000 : ℝ)
  | 17 => (-13754804843097 / 100000000000 : ℝ)
  | 18 => (-3461383899737 / 25000000000 : ℝ)
  | 19 => (-69683866071429 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch071Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-24411377316761 / 200000000000 : ℝ)
  | 1 => (-12287689171099 / 100000000000 : ℝ)
  | 2 => (-123701555920073 / 1000000000000 : ℝ)
  | 3 => (-3113272530811 / 25000000000 : ℝ)
  | 4 => (-125364949753921 / 1000000000000 : ℝ)
  | 5 => (-63101861837521 / 500000000000 : ℝ)
  | 6 => (-63523622635641 / 500000000000 : ℝ)
  | 7 => (-127895536903323 / 1000000000000 : ℝ)
  | 8 => (-32187155254327 / 250000000000 : ℝ)
  | 9 => (-129606520145093 / 1000000000000 : ℝ)
  | 10 => (-16308657113063 / 125000000000 : ℝ)
  | 11 => (-65668426999797 / 500000000000 : ℝ)
  | 12 => (-66104667110449 / 500000000000 : ℝ)
  | 13 => (-133086720445691 / 1000000000000 : ℝ)
  | 14 => (-133969035638247 / 1000000000000 : ℝ)
  | 15 => (-67428151425047 / 500000000000 : ℝ)
  | 16 => (-67874272610139 / 500000000000 : ℝ)
  | 17 => (-68322892987809 / 500000000000 : ℝ)
  | 18 => (-137548048430969 / 1000000000000 : ℝ)
  | 19 => (-138455355989479 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch071Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1420 : ℝ) + (j.val : ℝ)) / 1600)
      (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch071Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch071Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1420 : ℝ) + (j.val : ℝ)) / 1600)
    (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch071Neg100WeightLower j.val) (hpThetaShiftOneBatch071Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch071Neg100WeightLower, hpThetaShiftOneBatch071Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch071Neg100_integral_bounds :
    (-2979706511 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-920117511 / 20000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch071Lower hpThetaJensenCellsBatch071Upper
    hpThetaShiftOneBatch071Neg100WeightLower hpThetaShiftOneBatch071Neg100WeightUpper hpThetaJensenCellsBatch071_bounds hpThetaShiftOneBatch071Neg100_weight_bounds
  have hl : (-2979706511 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch071Lower j * hpThetaShiftOneBatch071Neg100WeightLower j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftOneBatch071Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftOneBatch071Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch071Lower j * hpThetaShiftOneBatch071Neg100WeightUpper j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftOneBatch071Neg100WeightUpper j) / 1600) ≤ (-920117511 / 20000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftOneBatch071Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1420 : ℝ) / 1600 = 71 / 80 by norm_num,
    show ((1420 : ℝ) + 20) / 1600 = (71 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch071Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-21155740182363 / 1000000000000 : ℝ)
  | 1 => (-21321526829627 / 1000000000000 : ℝ)
  | 2 => (-21488363194663 / 1000000000000 : ℝ)
  | 3 => (-433125092721 / 20000000000 : ℝ)
  | 4 => (-10912603267029 / 500000000000 : ℝ)
  | 5 => (-21995224290709 / 1000000000000 : ℝ)
  | 6 => (-443326266597 / 20000000000 : ℝ)
  | 7 => (-22338479097219 / 1000000000000 : ℝ)
  | 8 => (-22511727060509 / 1000000000000 : ℝ)
  | 9 => (-5671515677361 / 250000000000 : ℝ)
  | 10 => (-22861491555839 / 1000000000000 : ℝ)
  | 11 => (-2879752391709 / 125000000000 : ℝ)
  | 12 => (-23215650999153 / 1000000000000 : ℝ)
  | 13 => (-23394392730791 / 1000000000000 : ℝ)
  | 14 => (-11787124964731 / 500000000000 : ℝ)
  | 15 => (-23755228218481 / 1000000000000 : ℝ)
  | 16 => (-23937333243669 / 1000000000000 : ℝ)
  | 17 => (-24120570673419 / 1000000000000 : ℝ)
  | 18 => (-24304946198773 / 1000000000000 : ℝ)
  | 19 => (-24490465533483 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch071Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-20990997915911 / 1000000000000 : ℝ)
  | 1 => (-10577870091181 / 500000000000 : ℝ)
  | 2 => (-10660763414813 / 500000000000 : ℝ)
  | 3 => (-10744181597331 / 500000000000 : ℝ)
  | 4 => (-21656254636049 / 1000000000000 : ℝ)
  | 5 => (-21825206534057 / 1000000000000 : ℝ)
  | 6 => (-5498806072677 / 250000000000 : ℝ)
  | 7 => (-22166313329849 / 1000000000000 : ℝ)
  | 8 => (-11169239548609 / 500000000000 : ℝ)
  | 9 => (-5627931765127 / 250000000000 : ℝ)
  | 10 => (-22686062709443 / 1000000000000 : ℝ)
  | 11 => (-11430745777919 / 500000000000 : ℝ)
  | 12 => (-23038019133671 / 1000000000000 : ℝ)
  | 13 => (-1450978187447 / 62500000000 : ℝ)
  | 14 => (-2339439273079 / 100000000000 : ℝ)
  | 15 => (-23574249929461 / 1000000000000 : ℝ)
  | 16 => (-296940352731 / 12500000000 : ℝ)
  | 17 => (-5984333310917 / 250000000000 : ℝ)
  | 18 => (-12060285336709 / 500000000000 : ℝ)
  | 19 => (-6076236549693 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch071Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1420 : ℝ) + (j.val : ℝ)) / 1600)
      (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch071Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch071Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1420 : ℝ) + (j.val : ℝ)) / 1600)
    (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch071Neg65WeightLower j.val) (hpThetaShiftOneBatch071Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch071Neg65WeightLower, hpThetaShiftOneBatch071Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch071Neg65_integral_bounds :
    (-1657938469 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-1598154821 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch071Lower hpThetaJensenCellsBatch071Upper
    hpThetaShiftOneBatch071Neg65WeightLower hpThetaShiftOneBatch071Neg65WeightUpper hpThetaJensenCellsBatch071_bounds hpThetaShiftOneBatch071Neg65_weight_bounds
  have hl : (-1657938469 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch071Lower j * hpThetaShiftOneBatch071Neg65WeightLower j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftOneBatch071Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftOneBatch071Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch071Lower j * hpThetaShiftOneBatch071Neg65WeightUpper j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftOneBatch071Neg65WeightUpper j) / 1600) ≤ (-1598154821 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftOneBatch071Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1420 : ℝ) / 1600 = 71 / 80 by norm_num,
    show ((1420 : ℝ) + 20) / 1600 = (71 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch071Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-943480692009 / 1000000000000 : ℝ)
  | 1 => (-960649035249 / 1000000000000 : ℝ)
  | 2 => (-61123264469 / 62500000000 : ℝ)
  | 3 => (-995451245187 / 1000000000000 : ℝ)
  | 4 => (-1013087045123 / 1000000000000 : ℝ)
  | 5 => (-515440302279 / 500000000000 : ℝ)
  | 6 => (-131104112647 / 125000000000 : ℝ)
  | 7 => (-1066944917117 / 1000000000000 : ℝ)
  | 8 => (-217043527797 / 200000000000 : ℝ)
  | 9 => (-1103652057869 / 1000000000000 : ℝ)
  | 10 => (-280562292339 / 250000000000 : ℝ)
  | 11 => (-1141009973543 / 1000000000000 : ℝ)
  | 12 => (-72495967191 / 62500000000 : ℝ)
  | 13 => (-235805336613 / 200000000000 : ℝ)
  | 14 => (-37446394103 / 31250000000 : ℝ)
  | 15 => (-38053446189 / 31250000000 : ℝ)
  | 16 => (-38665772069 / 31250000000 : ℝ)
  | 17 => (-1257068923267 / 1000000000000 : ℝ)
  | 18 => (-1277003961331 / 1000000000000 : ℝ)
  | 19 => (-1297110857143 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch071Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5790414011 / 6250000000 : ℝ)
  | 1 => (-117935086501 / 125000000000 : ℝ)
  | 2 => (-60040564703 / 62500000000 : ℝ)
  | 3 => (-977972231503 / 1000000000000 : ℝ)
  | 4 => (-497725622593 / 500000000000 : ℝ)
  | 5 => (-506543522561 / 500000000000 : ℝ)
  | 6 => (-1030880604557 / 1000000000000 : ℝ)
  | 7 => (-41953316047 / 40000000000 : ℝ)
  | 8 => (-266736229279 / 250000000000 : ℝ)
  | 9 => (-135652204873 / 125000000000 : ℝ)
  | 10 => (-275913014467 / 250000000000 : ℝ)
  | 11 => (-224449833871 / 200000000000 : ℝ)
  | 12 => (-570504986771 / 500000000000 : ℝ)
  | 13 => (-231987095011 / 200000000000 : ℝ)
  | 14 => (-147378335383 / 125000000000 : ℝ)
  | 15 => (-239656922259 / 200000000000 : ℝ)
  | 16 => (-1217710278047 / 1000000000000 : ℝ)
  | 17 => (-1237304706207 / 1000000000000 : ℝ)
  | 18 => (-628534461633 / 500000000000 : ℝ)
  | 19 => (-127700396133 / 100000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch071Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1420 : ℝ) + (j.val : ℝ)) / 1600)
      (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch071Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch071Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1420 : ℝ) + (j.val : ℝ)) / 1600)
    (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch071Neg40WeightLower j.val) (hpThetaShiftOneBatch071Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch071Neg40WeightLower, hpThetaShiftOneBatch071Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch071Neg40_integral_bounds :
    (-403285577 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-192603853 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch071Lower hpThetaJensenCellsBatch071Upper
    hpThetaShiftOneBatch071Neg40WeightLower hpThetaShiftOneBatch071Neg40WeightUpper hpThetaJensenCellsBatch071_bounds hpThetaShiftOneBatch071Neg40_weight_bounds
  have hl : (-403285577 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch071Lower j * hpThetaShiftOneBatch071Neg40WeightLower j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftOneBatch071Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftOneBatch071Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch071Lower j * hpThetaShiftOneBatch071Neg40WeightUpper j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftOneBatch071Neg40WeightUpper j) / 1600) ≤ (-192603853 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftOneBatch071Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1420 : ℝ) / 1600 = 71 / 80 by norm_num,
    show ((1420 : ℝ) + 20) / 1600 = (71 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch071Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (69120292507 / 200000000000 : ℝ)
  | 1 => (173870891323 / 500000000000 : ℝ)
  | 2 => (349885797127 / 1000000000000 : ℝ)
  | 3 => (352033469179 / 1000000000000 : ℝ)
  | 4 => (44273095207 / 125000000000 : ℝ)
  | 5 => (44542454633 / 125000000000 : ℝ)
  | 6 => (358498057561 / 1000000000000 : ℝ)
  | 7 => (180329992477 / 500000000000 : ℝ)
  | 8 => (362825380697 / 1000000000000 : ℝ)
  | 9 => (36499420589 / 100000000000 : ℝ)
  | 10 => (367166421281 / 1000000000000 : ℝ)
  | 11 => (46167748407 / 125000000000 : ℝ)
  | 12 => (371520863847 / 1000000000000 : ℝ)
  | 13 => (14948120429 / 40000000000 : ℝ)
  | 14 => (93972096799 / 250000000000 : ℝ)
  | 15 => (378076952209 / 1000000000000 : ℝ)
  | 16 => (190134332171 / 500000000000 : ℝ)
  | 17 => (95615870453 / 250000000000 : ℝ)
  | 18 => (76932272493 / 200000000000 : ℝ)
  | 19 => (386862263777 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch071Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (347741782647 / 1000000000000 : ℝ)
  | 1 => (43735724641 / 125000000000 : ℝ)
  | 2 => (17601673459 / 50000000000 : ℝ)
  | 3 => (354184761657 / 1000000000000 : ℝ)
  | 4 => (71267927413 / 200000000000 : ℝ)
  | 5 => (179249028781 / 500000000000 : ℝ)
  | 6 => (72131996991 / 200000000000 : ℝ)
  | 7 => (181412690349 / 500000000000 : ℝ)
  | 8 => (364994205891 / 1000000000000 : ℝ)
  | 9 => (183583210641 / 500000000000 : ℝ)
  | 10 => (369341987257 / 1000000000000 : ℝ)
  | 11 => (46440107981 / 125000000000 : ℝ)
  | 12 => (186851505363 / 500000000000 : ℝ)
  | 13 => (375888387197 / 1000000000000 : ℝ)
  | 14 => (37807695221 / 100000000000 : ℝ)
  | 15 => (380268664343 / 1000000000000 : ℝ)
  | 16 => (382463481813 / 1000000000000 : ℝ)
  | 17 => (192330681233 / 500000000000 : ℝ)
  | 18 => (193431131889 / 500000000000 : ℝ)
  | 19 => (194533071429 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch071Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1420 : ℝ) + (j.val : ℝ)) / 1600)
      (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch071Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch071Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1420 : ℝ) + (j.val : ℝ)) / 1600)
    (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch071Neg20WeightLower j.val) (hpThetaShiftOneBatch071Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch071Neg20WeightLower, hpThetaShiftOneBatch071Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch071Neg20_integral_bounds :
    (64758329 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (134122619 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch071Lower hpThetaJensenCellsBatch071Upper
    hpThetaShiftOneBatch071Neg20WeightLower hpThetaShiftOneBatch071Neg20WeightUpper hpThetaJensenCellsBatch071_bounds hpThetaShiftOneBatch071Neg20_weight_bounds
  have hl : (64758329 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch071Lower j * hpThetaShiftOneBatch071Neg20WeightLower j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftOneBatch071Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftOneBatch071Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch071Lower j * hpThetaShiftOneBatch071Neg20WeightUpper j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftOneBatch071Neg20WeightUpper j) / 1600) ≤ (134122619 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftOneBatch071Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1420 : ℝ) / 1600 = 71 / 80 by norm_num,
    show ((1420 : ℝ) + 20) / 1600 = (71 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch071Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch071Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch071Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch071Neg20_integral_bounds
end HodgeProofHP
