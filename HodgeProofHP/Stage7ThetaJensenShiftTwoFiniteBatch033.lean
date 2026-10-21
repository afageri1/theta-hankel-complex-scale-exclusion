/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch033

/-! Exact signed weight and batch integral certificates, batch 33 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch033Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (348824991 / 1000000000000 : ℝ)
  | 1 => (36154329 / 100000000000 : ℝ)
  | 2 => (374430421 / 1000000000000 : ℝ)
  | 3 => (3027243 / 7812500000 : ℝ)
  | 4 => (200357019 / 500000000000 : ℝ)
  | 5 => (41411191 / 100000000000 : ℝ)
  | 6 => (85536277 / 200000000000 : ℝ)
  | 7 => (220711557 / 500000000000 : ℝ)
  | 8 => (455337727 / 1000000000000 : ℝ)
  | 9 => (117356459 / 250000000000 : ℝ)
  | 10 => (483688033 / 1000000000000 : ℝ)
  | 11 => (498124893 / 1000000000000 : ℝ)
  | 12 => (512736969 / 1000000000000 : ℝ)
  | 13 => (527524791 / 1000000000000 : ℝ)
  | 14 => (67811109 / 125000000000 : ℝ)
  | 15 => (278814851 / 500000000000 : ℝ)
  | 16 => (572947749 / 1000000000000 : ℝ)
  | 17 => (588443457 / 1000000000000 : ℝ)
  | 18 => (2359833 / 3906250000 : ℝ)
  | 19 => (619969523 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch033Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (361543291 / 1000000000000 : ℝ)
  | 1 => (187215211 / 500000000000 : ℝ)
  | 2 => (77497421 / 200000000000 : ℝ)
  | 3 => (400714039 / 1000000000000 : ℝ)
  | 4 => (414111911 / 1000000000000 : ℝ)
  | 5 => (213840693 / 500000000000 : ℝ)
  | 6 => (88284623 / 200000000000 : ℝ)
  | 7 => (1778663 / 3906250000 : ℝ)
  | 8 => (469425837 / 1000000000000 : ℝ)
  | 9 => (241844017 / 500000000000 : ℝ)
  | 10 => (249062447 / 500000000000 : ℝ)
  | 11 => (51273697 / 100000000000 : ℝ)
  | 12 => (65940599 / 125000000000 : ℝ)
  | 13 => (542488873 / 1000000000000 : ℝ)
  | 14 => (557629703 / 1000000000000 : ℝ)
  | 15 => (2291791 / 4000000000 : ℝ)
  | 16 => (294221729 / 500000000000 : ℝ)
  | 17 => (604117249 / 1000000000000 : ℝ)
  | 18 => (154992381 / 250000000000 : ℝ)
  | 19 => (39750041 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch033Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((660 : ℝ) + (j.val : ℝ)) / 1600)
      (((660 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch033Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch033Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((660 : ℝ) + (j.val : ℝ)) / 1600)
    (((660 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch033Neg100WeightLower j.val) (hpThetaShiftTwoBatch033Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch033Neg100WeightLower, hpThetaShiftTwoBatch033Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch033Neg100_integral_bounds :
    (343836491 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (449337717 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (660 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch033Lower hpThetaJensenCellsBatch033Upper
    hpThetaShiftTwoBatch033Neg100WeightLower hpThetaShiftTwoBatch033Neg100WeightUpper hpThetaJensenCellsBatch033_bounds hpThetaShiftTwoBatch033Neg100_weight_bounds
  have hl : (343836491 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch033Lower j * hpThetaShiftTwoBatch033Neg100WeightLower j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftTwoBatch033Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftTwoBatch033Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch033Lower j * hpThetaShiftTwoBatch033Neg100WeightUpper j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftTwoBatch033Neg100WeightUpper j) / 1600) ≤ (449337717 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftTwoBatch033Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (660 : ℝ) / 1600 = 33 / 80 by norm_num,
    show ((660 : ℝ) + 20) / 1600 = (33 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch033Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-564809573 / 1000000000000 : ℝ)
  | 1 => (-282919577 / 500000000000 : ℝ)
  | 2 => (-283403079 / 500000000000 : ℝ)
  | 3 => (-567709563 / 1000000000000 : ℝ)
  | 4 => (-568548337 / 1000000000000 : ℝ)
  | 5 => (-569321443 / 1000000000000 : ℝ)
  | 6 => (-285013919 / 500000000000 : ℝ)
  | 7 => (-57066647 / 100000000000 : ℝ)
  | 8 => (-571236283 / 1000000000000 : ℝ)
  | 9 => (-285868107 / 500000000000 : ℝ)
  | 10 => (-572165191 / 1000000000000 : ℝ)
  | 11 => (-28626107 / 50000000000 : ℝ)
  | 12 => (-71600747 / 125000000000 : ℝ)
  | 13 => (-573015611 / 1000000000000 : ℝ)
  | 14 => (-143287487 / 250000000000 : ℝ)
  | 15 => (-573207887 / 1000000000000 : ℝ)
  | 16 => (-71651389 / 125000000000 : ℝ)
  | 17 => (-573188317 / 1000000000000 : ℝ)
  | 18 => (-286545063 / 500000000000 : ℝ)
  | 19 => (-572912191 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch033Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-563718433 / 1000000000000 : ℝ)
  | 1 => (-141202393 / 250000000000 : ℝ)
  | 2 => (-565839153 / 1000000000000 : ℝ)
  | 3 => (-566806157 / 1000000000000 : ℝ)
  | 4 => (-283854781 / 500000000000 : ℝ)
  | 5 => (-35534271 / 62500000000 : ℝ)
  | 6 => (-284660721 / 500000000000 : ℝ)
  | 7 => (-570027837 / 1000000000000 : ℝ)
  | 8 => (-570666469 / 1000000000000 : ℝ)
  | 9 => (-285618141 / 500000000000 : ℝ)
  | 10 => (-571736213 / 1000000000000 : ℝ)
  | 11 => (-57216519 / 100000000000 : ℝ)
  | 12 => (-572522139 / 1000000000000 : ℝ)
  | 13 => (-22912239 / 40000000000 : ℝ)
  | 14 => (-57301561 / 100000000000 : ℝ)
  | 15 => (-573149947 / 1000000000000 : ℝ)
  | 16 => (-143297079 / 250000000000 : ℝ)
  | 17 => (-4584721 / 8000000000 : ℝ)
  | 18 => (-57291219 / 100000000000 : ℝ)
  | 19 => (-114530677 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch033Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((660 : ℝ) + (j.val : ℝ)) / 1600)
      (((660 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch033Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch033Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((660 : ℝ) + (j.val : ℝ)) / 1600)
    (((660 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch033Neg65WeightLower j.val) (hpThetaShiftTwoBatch033Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch033Neg65WeightLower, hpThetaShiftTwoBatch033Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch033Neg65_integral_bounds :
    (-417876747 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-1028373643 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (660 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch033Lower hpThetaJensenCellsBatch033Upper
    hpThetaShiftTwoBatch033Neg65WeightLower hpThetaShiftTwoBatch033Neg65WeightUpper hpThetaJensenCellsBatch033_bounds hpThetaShiftTwoBatch033Neg65_weight_bounds
  have hl : (-417876747 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch033Lower j * hpThetaShiftTwoBatch033Neg65WeightLower j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftTwoBatch033Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftTwoBatch033Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch033Lower j * hpThetaShiftTwoBatch033Neg65WeightUpper j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftTwoBatch033Neg65WeightUpper j) / 1600) ≤ (-1028373643 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftTwoBatch033Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (660 : ℝ) / 1600 = 33 / 80 by norm_num,
    show ((660 : ℝ) + 20) / 1600 = (33 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch033Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-266843281 / 500000000000 : ℝ)
  | 1 => (-421281 / 781250000 : ℝ)
  | 2 => (-272403213 / 500000000000 : ℝ)
  | 3 => (-275193217 / 500000000000 : ℝ)
  | 4 => (-555979331 / 1000000000000 : ℝ)
  | 5 => (-280792369 / 500000000000 : ℝ)
  | 6 => (-567202273 / 1000000000000 : ℝ)
  | 7 => (-286415773 / 500000000000 : ℝ)
  | 8 => (-578472163 / 1000000000000 : ℝ)
  | 9 => (-292061863 / 500000000000 : ℝ)
  | 10 => (-147446457 / 250000000000 : ℝ)
  | 11 => (-595458059 / 1000000000000 : ℝ)
  | 12 => (-150285001 / 250000000000 : ℝ)
  | 13 => (-15170781 / 25000000000 : ℝ)
  | 14 => (-612531341 / 1000000000000 : ℝ)
  | 15 => (-309119937 / 500000000000 : ℝ)
  | 16 => (-623956401 / 1000000000000 : ℝ)
  | 17 => (-629680477 / 1000000000000 : ℝ)
  | 18 => (-317705827 / 500000000000 : ℝ)
  | 19 => (-160287369 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch033Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-264073717 / 500000000000 : ℝ)
  | 1 => (-533686561 / 1000000000000 : ℝ)
  | 2 => (-539239679 / 1000000000000 : ℝ)
  | 3 => (-21792257 / 40000000000 : ℝ)
  | 4 => (-550386433 / 1000000000000 : ℝ)
  | 5 => (-55597933 / 100000000000 : ℝ)
  | 6 => (-561584737 / 1000000000000 : ℝ)
  | 7 => (-17725071 / 31250000000 : ℝ)
  | 8 => (-114566309 / 200000000000 : ℝ)
  | 9 => (-289236081 / 500000000000 : ℝ)
  | 10 => (-23364949 / 40000000000 : ℝ)
  | 11 => (-589785827 / 1000000000000 : ℝ)
  | 12 => (-297729029 / 500000000000 : ℝ)
  | 13 => (-601140003 / 1000000000000 : ℝ)
  | 14 => (-606831239 / 1000000000000 : ℝ)
  | 15 => (-30626567 / 50000000000 : ℝ)
  | 16 => (-618239873 / 1000000000000 : ℝ)
  | 17 => (-1559891 / 2500000000 : ℝ)
  | 18 => (-157420119 / 250000000000 : ℝ)
  | 19 => (-635411653 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch033Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((660 : ℝ) + (j.val : ℝ)) / 1600)
      (((660 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch033Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch033Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((660 : ℝ) + (j.val : ℝ)) / 1600)
    (((660 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch033Neg45WeightLower j.val) (hpThetaShiftTwoBatch033Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch033Neg45WeightLower, hpThetaShiftTwoBatch033Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch033Neg45_integral_bounds :
    (-268172547 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-261673959 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (660 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch033Lower hpThetaJensenCellsBatch033Upper
    hpThetaShiftTwoBatch033Neg45WeightLower hpThetaShiftTwoBatch033Neg45WeightUpper hpThetaJensenCellsBatch033_bounds hpThetaShiftTwoBatch033Neg45_weight_bounds
  have hl : (-268172547 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch033Lower j * hpThetaShiftTwoBatch033Neg45WeightLower j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftTwoBatch033Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftTwoBatch033Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch033Lower j * hpThetaShiftTwoBatch033Neg45WeightUpper j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftTwoBatch033Neg45WeightUpper j) / 1600) ≤ (-261673959 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftTwoBatch033Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (660 : ℝ) / 1600 = 33 / 80 by norm_num,
    show ((660 : ℝ) + 20) / 1600 = (33 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch033Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (24047667 / 125000000000 : ℝ)
  | 1 => (23646881 / 125000000000 : ℝ)
  | 2 => (18592787 / 100000000000 : ℝ)
  | 3 => (45659907 / 250000000000 : ℝ)
  | 4 => (179310151 / 1000000000000 : ℝ)
  | 5 => (175939267 / 1000000000000 : ℝ)
  | 6 => (86263403 / 500000000000 : ℝ)
  | 7 => (169072599 / 1000000000000 : ℝ)
  | 8 => (41394119 / 250000000000 : ℝ)
  | 9 => (162038271 / 1000000000000 : ℝ)
  | 10 => (19807227 / 125000000000 : ℝ)
  | 11 => (77417473 / 500000000000 : ℝ)
  | 12 => (30233899 / 200000000000 : ℝ)
  | 13 => (1474613 / 10000000000 : ℝ)
  | 14 => (71855099 / 500000000000 : ℝ)
  | 15 => (139916027 / 1000000000000 : ℝ)
  | 16 => (136078627 / 1000000000000 : ℝ)
  | 17 => (33049459 / 250000000000 : ℝ)
  | 18 => (128273497 / 1000000000000 : ℝ)
  | 19 => (124305451 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch033Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (48886727 / 250000000000 : ℝ)
  | 1 => (192381337 / 1000000000000 : ℝ)
  | 2 => (189175049 / 1000000000000 : ℝ)
  | 3 => (185927871 / 1000000000000 : ℝ)
  | 4 => (182639629 / 1000000000000 : ℝ)
  | 5 => (22413769 / 125000000000 : ℝ)
  | 6 => (43984817 / 250000000000 : ℝ)
  | 7 => (172526807 / 1000000000000 : ℝ)
  | 8 => (845363 / 5000000000 : ℝ)
  | 9 => (165576477 / 1000000000000 : ℝ)
  | 10 => (316481 / 1953125000 : ℝ)
  | 11 => (158457817 / 1000000000000 : ℝ)
  | 12 => (154834947 / 1000000000000 : ℝ)
  | 13 => (18896187 / 125000000000 : ℝ)
  | 14 => (147461301 / 1000000000000 : ℝ)
  | 15 => (143710199 / 1000000000000 : ℝ)
  | 16 => (34979007 / 250000000000 : ℝ)
  | 17 => (34019657 / 250000000000 : ℝ)
  | 18 => (132197837 / 1000000000000 : ℝ)
  | 19 => (64136749 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch033Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((660 : ℝ) + (j.val : ℝ)) / 1600)
      (((660 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch033Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch033Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((660 : ℝ) + (j.val : ℝ)) / 1600)
    (((660 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch033Neg25WeightLower j.val) (hpThetaShiftTwoBatch033Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch033Neg25WeightLower, hpThetaShiftTwoBatch033Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch033Neg25_integral_bounds :
    (144513907 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (33 / 80 : ℝ) ((33 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (599705217 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (660 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch033Lower hpThetaJensenCellsBatch033Upper
    hpThetaShiftTwoBatch033Neg25WeightLower hpThetaShiftTwoBatch033Neg25WeightUpper hpThetaJensenCellsBatch033_bounds hpThetaShiftTwoBatch033Neg25_weight_bounds
  have hl : (144513907 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch033Lower j * hpThetaShiftTwoBatch033Neg25WeightLower j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftTwoBatch033Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftTwoBatch033Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch033Lower j * hpThetaShiftTwoBatch033Neg25WeightUpper j)
        (hpThetaJensenCellsBatch033Upper j * hpThetaShiftTwoBatch033Neg25WeightUpper j) / 1600) ≤ (599705217 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch033Lower, hpThetaJensenCellsBatch033Upper,
      hpThetaShiftTwoBatch033Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (660 : ℝ) / 1600 = 33 / 80 by norm_num,
    show ((660 : ℝ) + 20) / 1600 = (33 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch033Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch033Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch033Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch033Neg25_integral_bounds
end HodgeProofHP
