/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch015

/-! Exact signed weight and batch integral certificates, batch 15 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch015Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3469387113 / 1000000000000 : ℝ)
  | 1 => (-1786087747 / 500000000000 : ℝ)
  | 2 => (-3675618499 / 1000000000000 : ℝ)
  | 3 => (-1889853061 / 500000000000 : ℝ)
  | 4 => (-77688563 / 20000000000 : ℝ)
  | 5 => (-797954833 / 200000000000 : ℝ)
  | 6 => (-2047866773 / 500000000000 : ℝ)
  | 7 => (-4202295461 / 1000000000000 : ℝ)
  | 8 => (-4309448873 / 1000000000000 : ℝ)
  | 9 => (-4417182539 / 1000000000000 : ℝ)
  | 10 => (-4525485003 / 1000000000000 : ℝ)
  | 11 => (-926868921 / 200000000000 : ℝ)
  | 12 => (-148242171 / 31250000000 : ℝ)
  | 13 => (-4853687523 / 1000000000000 : ℝ)
  | 14 => (-2482073233 / 500000000000 : ℝ)
  | 15 => (-5075113797 / 1000000000000 : ℝ)
  | 16 => (-5186576801 / 1000000000000 : ℝ)
  | 17 => (-662315319 / 125000000000 : ℝ)
  | 18 => (-541093791 / 100000000000 : ℝ)
  | 19 => (-1380952381 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch015Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1683631579 / 500000000000 : ℝ)
  | 1 => (-433673389 / 125000000000 : ℝ)
  | 2 => (-3572175493 / 1000000000000 : ℝ)
  | 3 => (-1837809249 / 500000000000 : ℝ)
  | 4 => (-3779706121 / 1000000000000 : ℝ)
  | 5 => (-3884428149 / 1000000000000 : ℝ)
  | 6 => (-997443541 / 250000000000 : ℝ)
  | 7 => (-819146709 / 200000000000 : ℝ)
  | 8 => (-210114773 / 50000000000 : ℝ)
  | 9 => (-538681109 / 125000000000 : ℝ)
  | 10 => (-2208591269 / 500000000000 : ℝ)
  | 11 => (-2262742501 / 500000000000 : ℝ)
  | 12 => (-1158586151 / 250000000000 : ℝ)
  | 13 => (-4743749471 / 1000000000000 : ℝ)
  | 14 => (-2426843761 / 500000000000 : ℝ)
  | 15 => (-992829293 / 200000000000 : ℝ)
  | 16 => (-1268778449 / 250000000000 : ℝ)
  | 17 => (-6483221 / 1250000000 : ℝ)
  | 18 => (-5298522551 / 1000000000000 : ℝ)
  | 19 => (-5410937909 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch015Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((300 : ℝ) + (j.val : ℝ)) / 1600)
      (((300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch015Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch015Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((300 : ℝ) + (j.val : ℝ)) / 1600)
    (((300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch015Neg100WeightLower j.val) (hpThetaShiftOneBatch015Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch015Neg100WeightLower, hpThetaShiftOneBatch015Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch015Neg100_integral_bounds :
    (-70201892567 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-33851968729 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch015Lower hpThetaJensenCellsBatch015Upper
    hpThetaShiftOneBatch015Neg100WeightLower hpThetaShiftOneBatch015Neg100WeightUpper hpThetaJensenCellsBatch015_bounds hpThetaShiftOneBatch015Neg100_weight_bounds
  have hl : (-70201892567 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch015Lower j * hpThetaShiftOneBatch015Neg100WeightLower j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftOneBatch015Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftOneBatch015Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch015Lower j * hpThetaShiftOneBatch015Neg100WeightUpper j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftOneBatch015Neg100WeightUpper j) / 1600) ≤ (-33851968729 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftOneBatch015Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (300 : ℝ) / 1600 = 15 / 80 by norm_num,
    show ((300 : ℝ) + 20) / 1600 = (15 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch015Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (441924513 / 250000000000 : ℝ)
  | 1 => (1700856887 / 1000000000000 : ℝ)
  | 2 => (408275497 / 250000000000 : ℝ)
  | 3 => (62577321 / 40000000000 : ℝ)
  | 4 => (1494849767 / 1000000000000 : ℝ)
  | 5 => (1424352073 / 1000000000000 : ℝ)
  | 6 => (1352939903 / 1000000000000 : ℝ)
  | 7 => (128061331 / 100000000000 : ℝ)
  | 8 => (1207372447 / 1000000000000 : ℝ)
  | 9 => (566608781 / 500000000000 : ℝ)
  | 10 => (211629801 / 200000000000 : ℝ)
  | 11 => (491083611 / 500000000000 : ℝ)
  | 12 => (452636381 / 500000000000 : ℝ)
  | 13 => (827466271 / 1000000000000 : ℝ)
  | 14 => (1497497 / 2000000000 : ℝ)
  | 15 => (334560149 / 500000000000 : ℝ)
  | 16 => (29429131 / 50000000000 : ℝ)
  | 17 => (253568261 / 500000000000 : ℝ)
  | 18 => (424783163 / 1000000000000 : ℝ)
  | 19 => (341523809 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch015Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (366725181 / 200000000000 : ℝ)
  | 1 => (1767698053 / 1000000000000 : ℝ)
  | 2 => (212607111 / 125000000000 : ℝ)
  | 3 => (1633101989 / 1000000000000 : ℝ)
  | 4 => (782216513 / 500000000000 : ℝ)
  | 5 => (186856221 / 125000000000 : ℝ)
  | 6 => (712176037 / 500000000000 : ℝ)
  | 7 => (10569843 / 7812500000 : ℝ)
  | 8 => (1280613311 / 1000000000000 : ℝ)
  | 9 => (37730389 / 31250000000 : ℝ)
  | 10 => (1133217563 / 1000000000000 : ℝ)
  | 11 => (529074503 / 500000000000 : ℝ)
  | 12 => (982167223 / 1000000000000 : ℝ)
  | 13 => (905272763 / 1000000000000 : ℝ)
  | 14 => (25858321 / 31250000000 : ℝ)
  | 15 => (748748501 / 1000000000000 : ℝ)
  | 16 => (669120299 / 1000000000000 : ℝ)
  | 17 => (588582621 / 1000000000000 : ℝ)
  | 18 => (507136523 / 1000000000000 : ℝ)
  | 19 => (106195791 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch015Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((300 : ℝ) + (j.val : ℝ)) / 1600)
      (((300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch015Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch015Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((300 : ℝ) + (j.val : ℝ)) / 1600)
    (((300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch015Neg65WeightLower j.val) (hpThetaShiftOneBatch015Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch015Neg65WeightLower, hpThetaShiftOneBatch015Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch015Neg65_integral_bounds :
    (842795407 / 50000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (9113128659 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch015Lower hpThetaJensenCellsBatch015Upper
    hpThetaShiftOneBatch015Neg65WeightLower hpThetaShiftOneBatch015Neg65WeightUpper hpThetaJensenCellsBatch015_bounds hpThetaShiftOneBatch015Neg65_weight_bounds
  have hl : (842795407 / 50000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch015Lower j * hpThetaShiftOneBatch015Neg65WeightLower j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftOneBatch015Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftOneBatch015Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch015Lower j * hpThetaShiftOneBatch015Neg65WeightUpper j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftOneBatch015Neg65WeightUpper j) / 1600) ≤ (9113128659 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftOneBatch015Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (300 : ℝ) / 1600 = 15 / 80 by norm_num,
    show ((300 : ℝ) + 20) / 1600 = (15 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch015Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (137672547 / 20000000000 : ℝ)
  | 1 => (686815361 / 100000000000 : ℝ)
  | 2 => (3425978891 / 500000000000 : ℝ)
  | 3 => (427189747 / 62500000000 : ℝ)
  | 4 => (1704346059 / 250000000000 : ℝ)
  | 5 => (3399499391 / 500000000000 : ℝ)
  | 6 => (3389937883 / 500000000000 : ℝ)
  | 7 => (1352002279 / 200000000000 : ℝ)
  | 8 => (1684850477 / 250000000000 : ℝ)
  | 9 => (3359021787 / 500000000000 : ℝ)
  | 10 => (1339186539 / 200000000000 : ℝ)
  | 11 => (1334613121 / 200000000000 : ℝ)
  | 12 => (664943867 / 100000000000 : ℝ)
  | 13 => (207032759 / 31250000000 : ℝ)
  | 14 => (1649972723 / 250000000000 : ℝ)
  | 15 => (1643490737 / 250000000000 : ℝ)
  | 16 => (1309452191 / 200000000000 : ℝ)
  | 17 => (3259890723 / 500000000000 : ℝ)
  | 18 => (649152099 / 100000000000 : ℝ)
  | 19 => (646247619 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch015Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1379676589 / 200000000000 : ℝ)
  | 1 => (6883627351 / 1000000000000 : ℝ)
  | 2 => (6868153611 / 1000000000000 : ℝ)
  | 3 => (6851957783 / 1000000000000 : ℝ)
  | 4 => (6835035953 / 1000000000000 : ℝ)
  | 5 => (6817384237 / 1000000000000 : ℝ)
  | 6 => (6798998783 / 1000000000000 : ℝ)
  | 7 => (6779875767 / 1000000000000 : ℝ)
  | 8 => (1690002849 / 250000000000 : ℝ)
  | 9 => (6739401909 / 1000000000000 : ℝ)
  | 10 => (268721743 / 40000000000 : ℝ)
  | 11 => (836991587 / 125000000000 : ℝ)
  | 12 => (3336532803 / 500000000000 : ℝ)
  | 13 => (6649438671 / 1000000000000 : ℝ)
  | 14 => (6625048289 / 1000000000000 : ℝ)
  | 15 => (6599890893 / 1000000000000 : ℝ)
  | 16 => (6573962949 / 1000000000000 : ℝ)
  | 17 => (1636815239 / 250000000000 : ℝ)
  | 18 => (6519781447 / 1000000000000 : ℝ)
  | 19 => (6491520991 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch015Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((300 : ℝ) + (j.val : ℝ)) / 1600)
      (((300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch015Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch015Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((300 : ℝ) + (j.val : ℝ)) / 1600)
    (((300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch015Neg40WeightLower j.val) (hpThetaShiftOneBatch015Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch015Neg40WeightLower, hpThetaShiftOneBatch015Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch015Neg40_integral_bounds :
    (6492566599 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (105458359689 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch015Lower hpThetaJensenCellsBatch015Upper
    hpThetaShiftOneBatch015Neg40WeightLower hpThetaShiftOneBatch015Neg40WeightUpper hpThetaJensenCellsBatch015_bounds hpThetaShiftOneBatch015Neg40_weight_bounds
  have hl : (6492566599 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch015Lower j * hpThetaShiftOneBatch015Neg40WeightLower j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftOneBatch015Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftOneBatch015Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch015Lower j * hpThetaShiftOneBatch015Neg40WeightUpper j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftOneBatch015Neg40WeightUpper j) / 1600) ≤ (105458359689 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftOneBatch015Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (300 : ℝ) / 1600 = 15 / 80 by norm_num,
    show ((300 : ℝ) + 20) / 1600 = (15 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch015Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2365111799 / 200000000000 : ℝ)
  | 1 => (11868698283 / 1000000000000 : ℝ)
  | 2 => (5955770441 / 500000000000 : ℝ)
  | 3 => (5977041569 / 500000000000 : ℝ)
  | 4 => (11996321399 / 1000000000000 : ℝ)
  | 5 => (1203825201 / 100000000000 : ℝ)
  | 6 => (12079871317 / 1000000000000 : ℝ)
  | 7 => (12121175669 / 1000000000000 : ℝ)
  | 8 => (12162161409 / 1000000000000 : ℝ)
  | 9 => (12202824887 / 1000000000000 : ℝ)
  | 10 => (765197653 / 62500000000 : ℝ)
  | 11 => (12283170441 / 1000000000000 : ℝ)
  | 12 => (12322845213 / 1000000000000 : ℝ)
  | 13 => (12362183113 / 1000000000000 : ℝ)
  | 14 => (3100295123 / 250000000000 : ℝ)
  | 15 => (124398337 / 10000000000 : ℝ)
  | 16 => (779883693 / 62500000000 : ℝ)
  | 17 => (1251609301 / 100000000000 : ℝ)
  | 18 => (12553691819 / 1000000000000 : ℝ)
  | 19 => (12590931871 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch015Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2967174571 / 250000000000 : ℝ)
  | 1 => (11911540883 / 1000000000000 : ℝ)
  | 2 => (11954083139 / 1000000000000 : ℝ)
  | 3 => (59981607 / 5000000000 : ℝ)
  | 4 => (12038252011 / 1000000000000 : ℝ)
  | 5 => (6039935659 / 500000000000 : ℝ)
  | 6 => (1212117567 / 100000000000 : ℝ)
  | 7 => (1216216141 / 100000000000 : ℝ)
  | 8 => (1525353111 / 125000000000 : ℝ)
  | 9 => (12243162449 / 1000000000000 : ℝ)
  | 10 => (6141585221 / 500000000000 : ℝ)
  | 11 => (6161422607 / 500000000000 : ℝ)
  | 12 => (6181091557 / 500000000000 : ℝ)
  | 13 => (12401180493 / 1000000000000 : ℝ)
  | 14 => (12439833701 / 1000000000000 : ℝ)
  | 15 => (12478139089 / 1000000000000 : ℝ)
  | 16 => (12516093011 / 1000000000000 : ℝ)
  | 17 => (627684591 / 50000000000 : ℝ)
  | 18 => (393466621 / 31250000000 : ℝ)
  | 19 => (3156952381 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch015Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((300 : ℝ) + (j.val : ℝ)) / 1600)
      (((300 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch015Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch015Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((300 : ℝ) + (j.val : ℝ)) / 1600)
    (((300 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch015Neg20WeightLower j.val) (hpThetaShiftOneBatch015Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch015Neg20WeightLower, hpThetaShiftOneBatch015Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch015Neg20_integral_bounds :
    (9474233439 / 50000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (15 / 80 : ℝ) ((15 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (12023106273 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (300 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch015Lower hpThetaJensenCellsBatch015Upper
    hpThetaShiftOneBatch015Neg20WeightLower hpThetaShiftOneBatch015Neg20WeightUpper hpThetaJensenCellsBatch015_bounds hpThetaShiftOneBatch015Neg20_weight_bounds
  have hl : (9474233439 / 50000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch015Lower j * hpThetaShiftOneBatch015Neg20WeightLower j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftOneBatch015Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftOneBatch015Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch015Lower j * hpThetaShiftOneBatch015Neg20WeightUpper j)
        (hpThetaJensenCellsBatch015Upper j * hpThetaShiftOneBatch015Neg20WeightUpper j) / 1600) ≤ (12023106273 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch015Lower, hpThetaJensenCellsBatch015Upper,
      hpThetaShiftOneBatch015Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (300 : ℝ) / 1600 = 15 / 80 by norm_num,
    show ((300 : ℝ) + 20) / 1600 = (15 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch015Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch015Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch015Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch015Neg20_integral_bounds
end HodgeProofHP
