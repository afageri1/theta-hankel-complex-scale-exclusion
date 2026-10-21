/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch073

/-! Exact signed weight and batch integral certificates, batch 73 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch073Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2918073977 / 15625000000 : ℝ)
  | 1 => (-188629812691 / 1000000000000 : ℝ)
  | 2 => (-190519595589 / 1000000000000 : ℝ)
  | 3 => (-192426215187 / 1000000000000 : ℝ)
  | 4 => (-97174902181 / 500000000000 : ℝ)
  | 5 => (-49072624229 / 250000000000 : ℝ)
  | 6 => (-9912421379 / 50000000000 : ℝ)
  | 7 => (-100111866009 / 500000000000 : ℝ)
  | 8 => (-12638534177 / 62500000000 : ℝ)
  | 9 => (-51056752393 / 250000000000 : ℝ)
  | 10 => (-103127629369 / 500000000000 : ℝ)
  | 11 => (-104150716893 / 500000000000 : ℝ)
  | 12 => (-105182837567 / 500000000000 : ℝ)
  | 13 => (-21244812417 / 100000000000 : ℝ)
  | 14 => (-26818615407 / 125000000000 : ℝ)
  | 15 => (-216668215731 / 1000000000000 : ℝ)
  | 16 => (-109403072961 / 500000000000 : ℝ)
  | 17 => (-220962859149 / 1000000000000 : ℝ)
  | 18 => (-111569250863 / 500000000000 : ℝ)
  | 19 => (-225333220973 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch073Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-46225057513 / 250000000000 : ℝ)
  | 1 => (-186756734527 / 1000000000000 : ℝ)
  | 2 => (-18862981269 / 100000000000 : ℝ)
  | 3 => (-47629898897 / 250000000000 : ℝ)
  | 4 => (-96213107593 / 500000000000 : ℝ)
  | 5 => (-194349804361 / 1000000000000 : ℝ)
  | 6 => (-39258099383 / 200000000000 : ℝ)
  | 7 => (-198248427579 / 1000000000000 : ℝ)
  | 8 => (-200223732017 / 1000000000000 : ℝ)
  | 9 => (-202216546831 / 1000000000000 : ℝ)
  | 10 => (-204227009571 / 1000000000000 : ℝ)
  | 11 => (-206255258737 / 1000000000000 : ℝ)
  | 12 => (-41660286757 / 200000000000 : ℝ)
  | 13 => (-210365675133 / 1000000000000 : ℝ)
  | 14 => (-212448124169 / 1000000000000 : ℝ)
  | 15 => (-42909784651 / 200000000000 : ℝ)
  | 16 => (-21666821573 / 100000000000 : ℝ)
  | 17 => (-218806145921 / 1000000000000 : ℝ)
  | 18 => (-55240714787 / 250000000000 : ℝ)
  | 19 => (-8925540069 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch073Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1460 : ℝ) + (j.val : ℝ)) / 1600)
      (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch073Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch073Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1460 : ℝ) + (j.val : ℝ)) / 1600)
    (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch073Neg100WeightLower j.val) (hpThetaShiftThreeBatch073Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch073Neg100WeightLower, hpThetaShiftThreeBatch073Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch073Neg100_integral_bounds :
    (-32077933 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-6163383 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch073Lower hpThetaJensenCellsBatch073Upper
    hpThetaShiftThreeBatch073Neg100WeightLower hpThetaShiftThreeBatch073Neg100WeightUpper hpThetaJensenCellsBatch073_bounds hpThetaShiftThreeBatch073Neg100_weight_bounds
  have hl : (-32077933 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch073Lower j * hpThetaShiftThreeBatch073Neg100WeightLower j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftThreeBatch073Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftThreeBatch073Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch073Lower j * hpThetaShiftThreeBatch073Neg100WeightUpper j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftThreeBatch073Neg100WeightUpper j) / 1600) ≤ (-6163383 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftThreeBatch073Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1460 : ℝ) / 1600 = 73 / 80 by norm_num,
    show ((1460 : ℝ) + 20) / 1600 = (73 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch073Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4115693753 / 125000000000 : ℝ)
  | 1 => (-33320579561 / 1000000000000 : ℝ)
  | 2 => (-4214951773 / 125000000000 : ℝ)
  | 3 => (-533167011 / 15625000000 : ℝ)
  | 4 => (-2158114887 / 62500000000 : ℝ)
  | 5 => (-1747054899 / 50000000000 : ℝ)
  | 6 => (-7071300733 / 200000000000 : ℝ)
  | 7 => (-35776091109 / 1000000000000 : ℝ)
  | 8 => (-904997411 / 25000000000 : ℝ)
  | 9 => (-18313978027 / 500000000000 : ℝ)
  | 10 => (-37060306621 / 1000000000000 : ℝ)
  | 11 => (-18748492539 / 500000000000 : ℝ)
  | 12 => (-237112679 / 6250000000 : ℝ)
  | 13 => (-7676694959 / 200000000000 : ℝ)
  | 14 => (-3883336131 / 100000000000 : ℝ)
  | 15 => (-39287726229 / 1000000000000 : ℝ)
  | 16 => (-993665197 / 25000000000 : ℝ)
  | 17 => (-4021004487 / 100000000000 : ℝ)
  | 18 => (-40678076093 / 1000000000000 : ℝ)
  | 19 => (-41150740727 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch073Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-32534491021 / 1000000000000 : ℝ)
  | 1 => (-32925550023 / 1000000000000 : ℝ)
  | 2 => (-833014489 / 25000000000 : ℝ)
  | 3 => (-33719614183 / 1000000000000 : ℝ)
  | 4 => (-34122688703 / 1000000000000 : ℝ)
  | 5 => (-34529838191 / 1000000000000 : ℝ)
  | 6 => (-34941097979 / 1000000000000 : ℝ)
  | 7 => (-2209781479 / 62500000000 : ℝ)
  | 8 => (-8944022777 / 250000000000 : ℝ)
  | 9 => (-36199896439 / 1000000000000 : ℝ)
  | 10 => (-36627956053 / 1000000000000 : ℝ)
  | 11 => (-1853015331 / 50000000000 : ℝ)
  | 12 => (-37496985077 / 1000000000000 : ℝ)
  | 13 => (-37938028639 / 1000000000000 : ℝ)
  | 14 => (-19191737397 / 500000000000 : ℝ)
  | 15 => (-38833361309 / 1000000000000 : ℝ)
  | 16 => (-9821931557 / 250000000000 : ℝ)
  | 17 => (-39746607879 / 1000000000000 : ℝ)
  | 18 => (-40210044869 / 1000000000000 : ℝ)
  | 19 => (-10169519023 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch073Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1460 : ℝ) + (j.val : ℝ)) / 1600)
      (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch073Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch073Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1460 : ℝ) + (j.val : ℝ)) / 1600)
    (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch073Neg70WeightLower j.val) (hpThetaShiftThreeBatch073Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch073Neg70WeightLower, hpThetaShiftThreeBatch073Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch073Neg70_integral_bounds :
    (-719207 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-2758591 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch073Lower hpThetaJensenCellsBatch073Upper
    hpThetaShiftThreeBatch073Neg70WeightLower hpThetaShiftThreeBatch073Neg70WeightUpper hpThetaJensenCellsBatch073_bounds hpThetaShiftThreeBatch073Neg70_weight_bounds
  have hl : (-719207 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch073Lower j * hpThetaShiftThreeBatch073Neg70WeightLower j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftThreeBatch073Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftThreeBatch073Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch073Lower j * hpThetaShiftThreeBatch073Neg70WeightUpper j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftThreeBatch073Neg70WeightUpper j) / 1600) ≤ (-2758591 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftThreeBatch073Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1460 : ℝ) / 1600 = 73 / 80 by norm_num,
    show ((1460 : ℝ) + 20) / 1600 = (73 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch073Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (925836173 / 1000000000000 : ℝ)
  | 1 => (908917479 / 1000000000000 : ℝ)
  | 2 => (55725641 / 62500000000 : ℝ)
  | 3 => (873909647 / 1000000000000 : ℝ)
  | 4 => (855810753 / 1000000000000 : ℝ)
  | 5 => (209327157 / 250000000000 : ℝ)
  | 6 => (818398279 / 1000000000000 : ℝ)
  | 7 => (79907467 / 100000000000 : ℝ)
  | 8 => (779332717 / 1000000000000 : ℝ)
  | 9 => (94895911 / 125000000000 : ℝ)
  | 10 => (369286603 / 500000000000 : ℝ)
  | 11 => (358772623 / 500000000000 : ℝ)
  | 12 => (348039067 / 500000000000 : ℝ)
  | 13 => (13483331 / 20000000000 : ℝ)
  | 14 => (162951281 / 250000000000 : ℝ)
  | 15 => (314494219 / 500000000000 : ℝ)
  | 16 => (605711023 / 1000000000000 : ℝ)
  | 17 => (581967363 / 1000000000000 : ℝ)
  | 18 => (557751891 / 1000000000000 : ℝ)
  | 19 => (533058989 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch073Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (942371149 / 1000000000000 : ℝ)
  | 1 => (462918087 / 500000000000 : ℝ)
  | 2 => (22722937 / 25000000000 : ℝ)
  | 3 => (891610257 / 1000000000000 : ℝ)
  | 4 => (54619353 / 62500000000 : ℝ)
  | 5 => (427905377 / 500000000000 : ℝ)
  | 6 => (837308629 / 1000000000000 : ℝ)
  | 7 => (20459957 / 25000000000 : ℝ)
  | 8 => (799074671 / 1000000000000 : ℝ)
  | 9 => (389666359 / 500000000000 : ℝ)
  | 10 => (759167289 / 1000000000000 : ℝ)
  | 11 => (738573207 / 1000000000000 : ℝ)
  | 12 => (717545247 / 1000000000000 : ℝ)
  | 13 => (139215627 / 200000000000 : ℝ)
  | 14 => (674166551 / 1000000000000 : ℝ)
  | 15 => (5214441 / 8000000000 : ℝ)
  | 16 => (628988439 / 1000000000000 : ℝ)
  | 17 => (37856939 / 62500000000 : ℝ)
  | 18 => (145491841 / 250000000000 : ℝ)
  | 19 => (139437973 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch073Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1460 : ℝ) + (j.val : ℝ)) / 1600)
      (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch073Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch073Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1460 : ℝ) + (j.val : ℝ)) / 1600)
    (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch073Neg45WeightLower j.val) (hpThetaShiftThreeBatch073Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch073Neg45WeightLower, hpThetaShiftThreeBatch073Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch073Neg45_integral_bounds :
    (28847 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (30523 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch073Lower hpThetaJensenCellsBatch073Upper
    hpThetaShiftThreeBatch073Neg45WeightLower hpThetaShiftThreeBatch073Neg45WeightUpper hpThetaJensenCellsBatch073_bounds hpThetaShiftThreeBatch073Neg45_weight_bounds
  have hl : (28847 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch073Lower j * hpThetaShiftThreeBatch073Neg45WeightLower j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftThreeBatch073Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftThreeBatch073Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch073Lower j * hpThetaShiftThreeBatch073Neg45WeightUpper j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftThreeBatch073Neg45WeightUpper j) / 1600) ≤ (30523 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftThreeBatch073Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1460 : ℝ) / 1600 = 73 / 80 by norm_num,
    show ((1460 : ℝ) + 20) / 1600 = (73 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch073Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (68237719 / 200000000000 : ℝ)
  | 1 => (43631603 / 125000000000 : ℝ)
  | 2 => (356984397 / 1000000000000 : ℝ)
  | 3 => (182491801 / 500000000000 : ℝ)
  | 4 => (46631341 / 125000000000 : ℝ)
  | 5 => (381186063 / 1000000000000 : ℝ)
  | 6 => (48673737 / 125000000000 : ℝ)
  | 7 => (198831257 / 500000000000 : ℝ)
  | 8 => (203002101 / 500000000000 : ℝ)
  | 9 => (25900953 / 62500000000 : ℝ)
  | 10 => (6607749 / 15625000000 : ℝ)
  | 11 => (431446551 / 1000000000000 : ℝ)
  | 12 => (440067377 / 1000000000000 : ℝ)
  | 13 => (448758697 / 1000000000000 : ℝ)
  | 14 => (457520793 / 1000000000000 : ℝ)
  | 15 => (116588487 / 250000000000 : ℝ)
  | 16 => (237629221 / 500000000000 : ℝ)
  | 17 => (242117277 / 500000000000 : ℝ)
  | 18 => (98656513 / 200000000000 : ℝ)
  | 19 => (502402753 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch073Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (13962113 / 40000000000 : ℝ)
  | 1 => (178492199 / 500000000000 : ℝ)
  | 2 => (364983603 / 1000000000000 : ℝ)
  | 3 => (373050729 / 1000000000000 : ℝ)
  | 4 => (23824129 / 62500000000 : ℝ)
  | 5 => (389389897 / 1000000000000 : ℝ)
  | 6 => (79532503 / 200000000000 : ℝ)
  | 7 => (406004203 / 1000000000000 : ℝ)
  | 8 => (414415249 / 1000000000000 : ℝ)
  | 9 => (422895937 / 1000000000000 : ℝ)
  | 10 => (53930819 / 125000000000 : ℝ)
  | 11 => (220033689 / 500000000000 : ℝ)
  | 12 => (224379349 / 500000000000 : ℝ)
  | 13 => (228760397 / 500000000000 : ℝ)
  | 14 => (466353949 / 1000000000000 : ℝ)
  | 15 => (475258443 / 1000000000000 : ℝ)
  | 16 => (96846911 / 200000000000 : ℝ)
  | 17 => (246641283 / 500000000000 : ℝ)
  | 18 => (251201377 / 500000000000 : ℝ)
  | 19 => (102319079 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch073Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1460 : ℝ) + (j.val : ℝ)) / 1600)
      (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch073Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch073Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1460 : ℝ) + (j.val : ℝ)) / 1600)
    (((1460 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch073Neg25WeightLower j.val) (hpThetaShiftThreeBatch073Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch073Neg25WeightLower, hpThetaShiftThreeBatch073Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch073Neg25_integral_bounds :
    (15773 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (73 / 80 : ℝ) ((73 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (66361 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1460 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch073Lower hpThetaJensenCellsBatch073Upper
    hpThetaShiftThreeBatch073Neg25WeightLower hpThetaShiftThreeBatch073Neg25WeightUpper hpThetaJensenCellsBatch073_bounds hpThetaShiftThreeBatch073Neg25_weight_bounds
  have hl : (15773 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch073Lower j * hpThetaShiftThreeBatch073Neg25WeightLower j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftThreeBatch073Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftThreeBatch073Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch073Lower j * hpThetaShiftThreeBatch073Neg25WeightUpper j)
        (hpThetaJensenCellsBatch073Upper j * hpThetaShiftThreeBatch073Neg25WeightUpper j) / 1600) ≤ (66361 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch073Lower, hpThetaJensenCellsBatch073Upper,
      hpThetaShiftThreeBatch073Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1460 : ℝ) / 1600 = 73 / 80 by norm_num,
    show ((1460 : ℝ) + 20) / 1600 = (73 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch073Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch073Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch073Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch073Neg25_integral_bounds
end HodgeProofHP
