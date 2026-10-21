/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch038

/-! Exact signed weight and batch integral certificates, batch 38 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch038Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (169047956103 / 1000000000000 : ℝ)
  | 1 => (10565977131 / 62500000000 : ℝ)
  | 2 => (42254650573 / 250000000000 : ℝ)
  | 3 => (3379073769 / 20000000000 : ℝ)
  | 4 => (21107551297 / 125000000000 : ℝ)
  | 5 => (168738280983 / 1000000000000 : ℝ)
  | 6 => (2634168879 / 15625000000 : ℝ)
  | 7 => (84202747611 / 500000000000 : ℝ)
  | 8 => (33638767983 / 200000000000 : ℝ)
  | 9 => (167951335339 / 1000000000000 : ℝ)
  | 10 => (83838734719 / 500000000000 : ℝ)
  | 11 => (8368586253 / 50000000000 : ℝ)
  | 12 => (83516789961 / 500000000000 : ℝ)
  | 13 => (166662506579 / 1000000000000 : ℝ)
  | 14 => (33251594477 / 200000000000 : ℝ)
  | 15 => (8290971973 / 50000000000 : ℝ)
  | 16 => (82673182327 / 500000000000 : ℝ)
  | 17 => (41209549879 / 250000000000 : ℝ)
  | 18 => (164294390253 / 1000000000000 : ℝ)
  | 19 => (81857188849 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch038Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (84532630599 / 500000000000 : ℝ)
  | 1 => (16906575961 / 100000000000 : ℝ)
  | 2 => (169055634097 / 1000000000000 : ℝ)
  | 3 => (169018602293 / 1000000000000 : ℝ)
  | 4 => (168953688451 / 1000000000000 : ℝ)
  | 5 => (168860410377 / 1000000000000 : ℝ)
  | 6 => (21092285123 / 125000000000 : ℝ)
  | 7 => (168586808257 / 1000000000000 : ℝ)
  | 8 => (168405495223 / 1000000000000 : ℝ)
  | 9 => (42048459979 / 250000000000 : ℝ)
  | 10 => (8397566767 / 50000000000 : ℝ)
  | 11 => (167677469439 / 1000000000000 : ℝ)
  | 12 => (167371725061 / 1000000000000 : ℝ)
  | 13 => (167033579923 / 1000000000000 : ℝ)
  | 14 => (8333125329 / 50000000000 : ℝ)
  | 15 => (83128986193 / 500000000000 : ℝ)
  | 16 => (165819439461 / 1000000000000 : ℝ)
  | 17 => (33069272931 / 200000000000 : ℝ)
  | 18 => (164838199517 / 1000000000000 : ℝ)
  | 19 => (82147195127 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch038Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((760 : ℝ) + (j.val : ℝ)) / 1600)
      (((760 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch038Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch038Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((760 : ℝ) + (j.val : ℝ)) / 1600)
    (((760 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch038Neg100WeightLower j.val) (hpThetaShiftOneBatch038Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch038Neg100WeightLower, hpThetaShiftOneBatch038Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch038Neg100_integral_bounds :
    (156715642829 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (31898431337 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (760 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch038Lower hpThetaJensenCellsBatch038Upper
    hpThetaShiftOneBatch038Neg100WeightLower hpThetaShiftOneBatch038Neg100WeightUpper hpThetaJensenCellsBatch038_bounds hpThetaShiftOneBatch038Neg100_weight_bounds
  have hl : (156715642829 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch038Lower j * hpThetaShiftOneBatch038Neg100WeightLower j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftOneBatch038Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftOneBatch038Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch038Lower j * hpThetaShiftOneBatch038Neg100WeightUpper j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftOneBatch038Neg100WeightUpper j) / 1600) ≤ (31898431337 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftOneBatch038Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (760 : ℝ) / 1600 = 38 / 80 by norm_num,
    show ((760 : ℝ) + 20) / 1600 = (38 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch038Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (75145224197 / 1000000000000 : ℝ)
  | 1 => (7620942299 / 100000000000 : ℝ)
  | 2 => (19319682041 / 250000000000 : ℝ)
  | 3 => (78353100551 / 1000000000000 : ℝ)
  | 4 => (992906251 / 12500000000 : ℝ)
  | 5 => (80516885777 / 1000000000000 : ℝ)
  | 6 => (81606215751 / 1000000000000 : ℝ)
  | 7 => (82700447187 / 1000000000000 : ℝ)
  | 8 => (83799536341 / 1000000000000 : ℝ)
  | 9 => (84903438529 / 1000000000000 : ℝ)
  | 10 => (86012108119 / 1000000000000 : ℝ)
  | 11 => (43562749263 / 500000000000 : ℝ)
  | 12 => (44121781099 / 500000000000 : ℝ)
  | 13 => (11170781327 / 125000000000 : ℝ)
  | 14 => (22623378569 / 250000000000 : ℝ)
  | 15 => (9162530269 / 100000000000 : ℝ)
  | 16 => (92761564371 / 1000000000000 : ℝ)
  | 17 => (93902246829 / 1000000000000 : ℝ)
  | 18 => (47523648279 / 500000000000 : ℝ)
  | 19 => (96196659033 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch038Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (76209422991 / 1000000000000 : ℝ)
  | 1 => (15455745633 / 200000000000 : ℝ)
  | 2 => (9794137569 / 125000000000 : ℝ)
  | 3 => (79432500081 / 1000000000000 : ℝ)
  | 4 => (40258442889 / 500000000000 : ℝ)
  | 5 => (10200776969 / 125000000000 : ℝ)
  | 6 => (20675111797 / 250000000000 : ℝ)
  | 7 => (41899768171 / 500000000000 : ℝ)
  | 8 => (8490343853 / 100000000000 : ℝ)
  | 9 => (2150302703 / 25000000000 : ℝ)
  | 10 => (87125498527 / 1000000000000 : ℝ)
  | 11 => (88243562199 / 1000000000000 : ℝ)
  | 12 => (89366250617 / 1000000000000 : ℝ)
  | 13 => (90493514277 / 1000000000000 : ℝ)
  | 14 => (91625302691 / 1000000000000 : ℝ)
  | 15 => (23190391093 / 250000000000 : ℝ)
  | 16 => (9390224683 / 100000000000 : ℝ)
  | 17 => (95047296559 / 1000000000000 : ℝ)
  | 18 => (48098329517 / 500000000000 : ℝ)
  | 19 => (48675139349 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch038Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((760 : ℝ) + (j.val : ℝ)) / 1600)
      (((760 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch038Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch038Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((760 : ℝ) + (j.val : ℝ)) / 1600)
    (((760 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch038Neg65WeightLower j.val) (hpThetaShiftOneBatch038Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch038Neg65WeightLower, hpThetaShiftOneBatch038Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch038Neg65_integral_bounds :
    (159697293019 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (164385191631 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (760 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch038Lower hpThetaJensenCellsBatch038Upper
    hpThetaShiftOneBatch038Neg65WeightLower hpThetaShiftOneBatch038Neg65WeightUpper hpThetaJensenCellsBatch038_bounds hpThetaShiftOneBatch038Neg65_weight_bounds
  have hl : (159697293019 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch038Lower j * hpThetaShiftOneBatch038Neg65WeightLower j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftOneBatch038Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftOneBatch038Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch038Lower j * hpThetaShiftOneBatch038Neg65WeightUpper j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftOneBatch038Neg65WeightUpper j) / 1600) ≤ (164385191631 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftOneBatch038Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (760 : ℝ) / 1600 = 38 / 80 by norm_num,
    show ((760 : ℝ) + 20) / 1600 = (38 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch038Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8886188269 / 250000000000 : ℝ)
  | 1 => (-35337212797 / 1000000000000 : ℝ)
  | 2 => (-17562772457 / 500000000000 : ℝ)
  | 3 => (-34909727289 / 1000000000000 : ℝ)
  | 4 => (-34689737827 / 1000000000000 : ℝ)
  | 5 => (-4308194309 / 125000000000 : ℝ)
  | 6 => (-17118577607 / 500000000000 : ℝ)
  | 7 => (-34004518087 / 1000000000000 : ℝ)
  | 8 => (-3376762117 / 100000000000 : ℝ)
  | 9 => (-1047701331 / 31250000000 : ℝ)
  | 10 => (-33280960527 / 1000000000000 : ℝ)
  | 11 => (-16515576601 / 500000000000 : ℝ)
  | 12 => (-16388499447 / 500000000000 : ℝ)
  | 13 => (-6503695187 / 200000000000 : ℝ)
  | 14 => (-32255562709 / 1000000000000 : ℝ)
  | 15 => (-31988237657 / 1000000000000 : ℝ)
  | 16 => (-31716479277 / 1000000000000 : ℝ)
  | 17 => (-251522129 / 8000000000 : ℝ)
  | 18 => (-1557978841 / 50000000000 : ℝ)
  | 19 => (-15437195019 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch038Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8834303199 / 250000000000 : ℝ)
  | 1 => (-35125544913 / 1000000000000 : ℝ)
  | 2 => (-4363715911 / 125000000000 : ℝ)
  | 3 => (-17344868913 / 500000000000 : ℝ)
  | 4 => (-34465554471 / 1000000000000 : ℝ)
  | 5 => (-34237155213 / 1000000000000 : ℝ)
  | 6 => (-17002259043 / 500000000000 : ℝ)
  | 7 => (-33767621169 / 1000000000000 : ℝ)
  | 8 => (-33526442591 / 1000000000000 : ℝ)
  | 9 => (-16640480263 / 500000000000 : ℝ)
  | 10 => (-33031153201 / 1000000000000 : ℝ)
  | 11 => (-32776998893 / 1000000000000 : ℝ)
  | 12 => (-16259237967 / 500000000000 : ℝ)
  | 13 => (-8063890677 / 250000000000 : ℝ)
  | 14 => (-3998529707 / 125000000000 : ℝ)
  | 15 => (-7929119819 / 250000000000 : ℝ)
  | 16 => (-7860066531 / 250000000000 : ℝ)
  | 17 => (-31159576819 / 1000000000000 : ℝ)
  | 18 => (-30874390037 / 1000000000000 : ℝ)
  | 19 => (-764617113 / 25000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch038Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((760 : ℝ) + (j.val : ℝ)) / 1600)
      (((760 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch038Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch038Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((760 : ℝ) + (j.val : ℝ)) / 1600)
    (((760 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch038Neg40WeightLower j.val) (hpThetaShiftOneBatch038Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch038Neg40WeightLower, hpThetaShiftOneBatch038Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch038Neg40_integral_bounds :
    (-63544510257 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-2482932507 / 40000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (760 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch038Lower hpThetaJensenCellsBatch038Upper
    hpThetaShiftOneBatch038Neg40WeightLower hpThetaShiftOneBatch038Neg40WeightUpper hpThetaJensenCellsBatch038_bounds hpThetaShiftOneBatch038Neg40_weight_bounds
  have hl : (-63544510257 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch038Lower j * hpThetaShiftOneBatch038Neg40WeightLower j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftOneBatch038Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftOneBatch038Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch038Lower j * hpThetaShiftOneBatch038Neg40WeightUpper j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftOneBatch038Neg40WeightUpper j) / 1600) ≤ (-2482932507 / 40000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftOneBatch038Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (760 : ℝ) / 1600 = 38 / 80 by norm_num,
    show ((760 : ℝ) + 20) / 1600 = (38 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch038Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-39468965773 / 1000000000000 : ℝ)
  | 1 => (-39735046739 / 1000000000000 : ℝ)
  | 2 => (-20000619909 / 500000000000 : ℝ)
  | 3 => (-40267536867 / 1000000000000 : ℝ)
  | 4 => (-1266685303 / 31250000000 : ℝ)
  | 5 => (-40800410073 / 1000000000000 : ℝ)
  | 6 => (-41066969723 / 1000000000000 : ℝ)
  | 7 => (-41333600327 / 1000000000000 : ℝ)
  | 8 => (-20800146761 / 500000000000 : ℝ)
  | 9 => (-20933520451 / 500000000000 : ℝ)
  | 10 => (-21066917009 / 500000000000 : ℝ)
  | 11 => (-42400664377 / 1000000000000 : ℝ)
  | 12 => (-42667523443 / 1000000000000 : ℝ)
  | 13 => (-10733600659 / 250000000000 : ℝ)
  | 14 => (-21600646667 / 500000000000 : ℝ)
  | 15 => (-43468186869 / 1000000000000 : ℝ)
  | 16 => (-43735074531 / 1000000000000 : ℝ)
  | 17 => (-44001947569 / 1000000000000 : ℝ)
  | 18 => (-172924989 / 3906250000 : ℝ)
  | 19 => (-22267807269 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch038Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-39203005023 / 1000000000000 : ℝ)
  | 1 => (-9867241443 / 250000000000 : ℝ)
  | 2 => (-19867523369 / 500000000000 : ℝ)
  | 3 => (-40001239817 / 1000000000000 : ℝ)
  | 4 => (-20133768433 / 500000000000 : ℝ)
  | 5 => (-8106785939 / 200000000000 : ℝ)
  | 6 => (-5100051259 / 125000000000 : ℝ)
  | 7 => (-20533484861 / 500000000000 : ℝ)
  | 8 => (-20666800163 / 500000000000 : ℝ)
  | 9 => (-41600293521 / 1000000000000 : ℝ)
  | 10 => (-41867040901 / 1000000000000 : ℝ)
  | 11 => (-42133834017 / 1000000000000 : ℝ)
  | 12 => (-5300083047 / 125000000000 : ℝ)
  | 13 => (-21333761721 / 500000000000 : ℝ)
  | 14 => (-8586880527 / 200000000000 : ℝ)
  | 15 => (-43201293333 / 1000000000000 : ℝ)
  | 16 => (-10867046717 / 250000000000 : ℝ)
  | 17 => (-4373507453 / 100000000000 : ℝ)
  | 18 => (-2750121723 / 62500000000 : ℝ)
  | 19 => (-44268797183 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch038Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((760 : ℝ) + (j.val : ℝ)) / 1600)
      (((760 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch038Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch038Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((760 : ℝ) + (j.val : ℝ)) / 1600)
    (((760 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch038Neg20WeightLower j.val) (hpThetaShiftOneBatch038Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch038Neg20WeightLower, hpThetaShiftOneBatch038Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch038Neg20_integral_bounds :
    (-79808408301 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (38 / 80 : ℝ) ((38 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-78041801313 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (760 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch038Lower hpThetaJensenCellsBatch038Upper
    hpThetaShiftOneBatch038Neg20WeightLower hpThetaShiftOneBatch038Neg20WeightUpper hpThetaJensenCellsBatch038_bounds hpThetaShiftOneBatch038Neg20_weight_bounds
  have hl : (-79808408301 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch038Lower j * hpThetaShiftOneBatch038Neg20WeightLower j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftOneBatch038Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftOneBatch038Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch038Lower j * hpThetaShiftOneBatch038Neg20WeightUpper j)
        (hpThetaJensenCellsBatch038Upper j * hpThetaShiftOneBatch038Neg20WeightUpper j) / 1600) ≤ (-78041801313 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch038Lower, hpThetaJensenCellsBatch038Upper,
      hpThetaShiftOneBatch038Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (760 : ℝ) / 1600 = 38 / 80 by norm_num,
    show ((760 : ℝ) + 20) / 1600 = (38 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch038Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch038Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch038Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch038Neg20_integral_bounds
end HodgeProofHP
