/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch079

/-! Exact signed weight and batch integral certificates, batch 79 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch079Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-165811509262679 / 500000000000 : ℝ)
  | 1 => (-333541721254569 / 1000000000000 : ℝ)
  | 2 => (-335469904388801 / 1000000000000 : ℝ)
  | 3 => (-84351901800521 / 250000000000 : ℝ)
  | 4 => (-3393548691013 / 10000000000 : ℝ)
  | 5 => (-17065586481327 / 50000000000 : ℝ)
  | 6 => (-171639114225727 / 500000000000 : ℝ)
  | 7 => (-34525440538361 / 100000000000 : ℝ)
  | 8 => (-86810075091211 / 250000000000 : ℝ)
  | 9 => (-2728405886497 / 7812500000 : ℝ)
  | 10 => (-351241404915371 / 1000000000000 : ℝ)
  | 11 => (-353256695042891 / 1000000000000 : ℝ)
  | 12 => (-355281864336653 / 1000000000000 : ℝ)
  | 13 => (-44664619176899 / 125000000000 : ℝ)
  | 14 => (-179681001516727 / 500000000000 : ℝ)
  | 15 => (-361417054083159 / 1000000000000 : ℝ)
  | 16 => (-181741073796581 / 500000000000 : ℝ)
  | 17 => (-365557324729811 / 1000000000000 : ℝ)
  | 18 => (-183821313398657 / 500000000000 : ℝ)
  | 19 => (-23108630952381 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch079Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-164856878529821 / 500000000000 : ℝ)
  | 1 => (-331623018525357 / 1000000000000 : ℝ)
  | 2 => (-41692715156821 / 125000000000 : ℝ)
  | 3 => (-209668690243 / 625000000 : ℝ)
  | 4 => (-337407607202083 / 1000000000000 : ℝ)
  | 5 => (-339354869101299 / 1000000000000 : ℝ)
  | 6 => (-341311729626539 / 1000000000000 : ℝ)
  | 7 => (-343278228451453 / 1000000000000 : ℝ)
  | 8 => (-345254405383609 / 1000000000000 : ℝ)
  | 9 => (-347240300364843 / 1000000000000 : ℝ)
  | 10 => (-69847190694323 / 200000000000 : ℝ)
  | 11 => (-35124140491537 / 100000000000 : ℝ)
  | 12 => (-35325669504289 / 100000000000 : ℝ)
  | 13 => (-88820466084163 / 250000000000 : ℝ)
  | 14 => (-357316953415191 / 1000000000000 : ℝ)
  | 15 => (-359362003033453 / 1000000000000 : ℝ)
  | 16 => (-180708527041579 / 500000000000 : ℝ)
  | 17 => (-363482147593161 / 1000000000000 : ℝ)
  | 18 => (-36555732472981 / 100000000000 : ℝ)
  | 19 => (-367642626797313 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch079Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1580 : ℝ) + (j.val : ℝ)) / 1600)
      (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch079Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch079Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1580 : ℝ) + (j.val : ℝ)) / 1600)
    (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch079Neg100WeightLower j.val) (hpThetaShiftOneBatch079Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch079Neg100WeightLower, hpThetaShiftOneBatch079Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch079Neg100_integral_bounds :
    (-128187703 / 40000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-3078920253 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch079Lower hpThetaJensenCellsBatch079Upper
    hpThetaShiftOneBatch079Neg100WeightLower hpThetaShiftOneBatch079Neg100WeightUpper hpThetaJensenCellsBatch079_bounds hpThetaShiftOneBatch079Neg100_weight_bounds
  have hl : (-128187703 / 40000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch079Lower j * hpThetaShiftOneBatch079Neg100WeightLower j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftOneBatch079Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftOneBatch079Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch079Lower j * hpThetaShiftOneBatch079Neg100WeightUpper j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftOneBatch079Neg100WeightUpper j) / 1600) ≤ (-3078920253 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftOneBatch079Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1580 : ℝ) / 1600 = 79 / 80 by norm_num,
    show ((1580 : ℝ) + 20) / 1600 = (79 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch079Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-65252644242477 / 1000000000000 : ℝ)
  | 1 => (-16417743754439 / 250000000000 : ℝ)
  | 2 => (-33045769005999 / 500000000000 : ℝ)
  | 3 => (-33257171508649 / 500000000000 : ℝ)
  | 4 => (-66939399860287 / 1000000000000 : ℝ)
  | 5 => (-33683359201109 / 500000000000 : ℝ)
  | 6 => (-16949077134767 / 250000000000 : ℝ)
  | 7 => (-34114090100813 / 500000000000 : ℝ)
  | 8 => (-13732468671119 / 200000000000 : ℝ)
  | 9 => (-69098808001681 / 1000000000000 : ℝ)
  | 10 => (-69537584175691 / 1000000000000 : ℝ)
  | 11 => (-6997868194863 / 100000000000 : ℝ)
  | 12 => (-70422111426793 / 1000000000000 : ℝ)
  | 13 => (-70867882751863 / 1000000000000 : ℝ)
  | 14 => (-71316006101009 / 1000000000000 : ℝ)
  | 15 => (-71766491686979 / 1000000000000 : ℝ)
  | 16 => (-18054837439549 / 250000000000 : ℝ)
  | 17 => (-72674590598859 / 1000000000000 : ℝ)
  | 18 => (-18283056132259 / 250000000000 : ℝ)
  | 19 => (-36796130952381 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch079Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-129673071857 / 2000000000 : ℝ)
  | 1 => (-16313161060619 / 250000000000 : ℝ)
  | 2 => (-13134195003551 / 200000000000 : ℝ)
  | 3 => (-66091538011997 / 1000000000000 : ℝ)
  | 4 => (-66514343017297 / 1000000000000 : ℝ)
  | 5 => (-33469699930143 / 500000000000 : ℝ)
  | 6 => (-67366718402217 / 1000000000000 : ℝ)
  | 7 => (-67796308539067 / 1000000000000 : ℝ)
  | 8 => (-545825441613 / 8000000000 : ℝ)
  | 9 => (-34331171677797 / 500000000000 : ℝ)
  | 10 => (-863735100021 / 12500000000 : ℝ)
  | 11 => (-6953758417569 / 100000000000 : ℝ)
  | 12 => (-69978681948629 / 1000000000000 : ℝ)
  | 13 => (-8802763928349 / 125000000000 : ℝ)
  | 14 => (-35433941375931 / 500000000000 : ℝ)
  | 15 => (-4457250381313 / 62500000000 : ℝ)
  | 16 => (-35883245843489 / 500000000000 : ℝ)
  | 17 => (-14443869951639 / 200000000000 : ℝ)
  | 18 => (-36337295299429 / 500000000000 : ℝ)
  | 19 => (-14626444905807 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch079Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1580 : ℝ) + (j.val : ℝ)) / 1600)
      (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch079Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch079Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1580 : ℝ) + (j.val : ℝ)) / 1600)
    (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch079Neg65WeightLower j.val) (hpThetaShiftOneBatch079Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch079Neg65WeightLower, hpThetaShiftOneBatch079Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch079Neg65_integral_bounds :
    (-633992481 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-608741041 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch079Lower hpThetaJensenCellsBatch079Upper
    hpThetaShiftOneBatch079Neg65WeightLower hpThetaShiftOneBatch079Neg65WeightUpper hpThetaJensenCellsBatch079_bounds hpThetaShiftOneBatch079Neg65_weight_bounds
  have hl : (-633992481 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch079Lower j * hpThetaShiftOneBatch079Neg65WeightLower j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftOneBatch079Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftOneBatch079Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch079Lower j * hpThetaShiftOneBatch079Neg65WeightUpper j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftOneBatch079Neg65WeightUpper j) / 1600) ≤ (-608741041 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftOneBatch079Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1580 : ℝ) / 1600 = 79 / 80 by norm_num,
    show ((1580 : ℝ) + 20) / 1600 = (79 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch079Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-6435004318867 / 1000000000000 : ℝ)
  | 1 => (-3246293584933 / 500000000000 : ℝ)
  | 2 => (-204704565293 / 31250000000 : ℝ)
  | 3 => (-660888295931 / 100000000000 : ℝ)
  | 4 => (-6667599668823 / 1000000000000 : ℝ)
  | 5 => (-3363349057167 / 500000000000 : ℝ)
  | 6 => (-135723603991 / 20000000000 : ℝ)
  | 7 => (-171151195887 / 25000000000 : ℝ)
  | 8 => (-3453151470231 / 500000000000 : ℝ)
  | 9 => (-3483473720091 / 500000000000 : ℝ)
  | 10 => (-3513991633847 / 500000000000 : ℝ)
  | 11 => (-1417882472689 / 200000000000 : ℝ)
  | 12 => (-1787809168823 / 250000000000 : ℝ)
  | 13 => (-1803364539631 / 250000000000 : ℝ)
  | 14 => (-454754923493 / 62500000000 : ℝ)
  | 15 => (-3669550248801 / 500000000000 : ℝ)
  | 16 => (-3701262650693 / 500000000000 : ℝ)
  | 17 => (-298654206899 / 40000000000 : ℝ)
  | 18 => (-7530592103647 / 1000000000000 : ℝ)
  | 19 => (-7595238095239 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch079Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3188897830843 / 500000000000 : ℝ)
  | 1 => (-3217502159433 / 500000000000 : ℝ)
  | 2 => (-1298517433973 / 200000000000 : ℝ)
  | 3 => (-10480873743 / 1600000000 : ℝ)
  | 4 => (-6608882959309 / 1000000000000 : ℝ)
  | 5 => (-3333799834411 / 500000000000 : ℝ)
  | 6 => (-6726698114333 / 1000000000000 : ℝ)
  | 7 => (-6786180199549 / 1000000000000 : ℝ)
  | 8 => (-6846047835479 / 1000000000000 : ℝ)
  | 9 => (-6906302940461 / 1000000000000 : ℝ)
  | 10 => (-6966947440181 / 1000000000000 : ℝ)
  | 11 => (-7027983267693 / 1000000000000 : ℝ)
  | 12 => (-1772353090861 / 250000000000 : ℝ)
  | 13 => (-7151236675291 / 1000000000000 : ℝ)
  | 14 => (-7213458158523 / 1000000000000 : ℝ)
  | 15 => (-7276078775887 / 1000000000000 : ℝ)
  | 16 => (-7339100497601 / 1000000000000 : ℝ)
  | 17 => (-1480505060277 / 200000000000 : ℝ)
  | 18 => (-3733177586237 / 500000000000 : ℝ)
  | 19 => (-3765296051823 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch079Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1580 : ℝ) + (j.val : ℝ)) / 1600)
      (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch079Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch079Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1580 : ℝ) + (j.val : ℝ)) / 1600)
    (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch079Neg40WeightLower j.val) (hpThetaShiftOneBatch079Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch079Neg40WeightLower, hpThetaShiftOneBatch079Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch079Neg40_integral_bounds :
    (-6389277 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-306001 / 5000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch079Lower hpThetaJensenCellsBatch079Upper
    hpThetaShiftOneBatch079Neg40WeightLower hpThetaShiftOneBatch079Neg40WeightUpper hpThetaJensenCellsBatch079_bounds hpThetaShiftOneBatch079Neg40_weight_bounds
  have hl : (-6389277 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch079Lower j * hpThetaShiftOneBatch079Neg40WeightLower j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftOneBatch079Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftOneBatch079Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch079Lower j * hpThetaShiftOneBatch079Neg40WeightUpper j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftOneBatch079Neg40WeightUpper j) / 1600) ≤ (-306001 / 5000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftOneBatch079Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1580 : ℝ) / 1600 = 79 / 80 by norm_num,
    show ((1580 : ℝ) + 20) / 1600 = (79 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch079Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (174986310351 / 250000000000 : ℝ)
  | 1 => (175483230477 / 250000000000 : ℝ)
  | 2 => (703912866611 / 1000000000000 : ℝ)
  | 3 => (705884960919 / 1000000000000 : ℝ)
  | 4 => (707849089591 / 1000000000000 : ℝ)
  | 5 => (22181410523 / 31250000000 : ℝ)
  | 6 => (71175298581 / 100000000000 : ℝ)
  | 7 => (356846259807 / 500000000000 : ℝ)
  | 8 => (715623620293 / 1000000000000 : ℝ)
  | 9 => (717546169331 / 1000000000000 : ℝ)
  | 10 => (719460047551 / 1000000000000 : ℝ)
  | 11 => (90170641889 / 125000000000 : ℝ)
  | 12 => (723261311507 / 1000000000000 : ℝ)
  | 13 => (725148455559 / 1000000000000 : ℝ)
  | 14 => (45439152839 / 62500000000 : ℝ)
  | 15 => (728895158579 / 1000000000000 : ℝ)
  | 16 => (73075447183 / 100000000000 : ℝ)
  | 17 => (366302130651 / 500000000000 : ℝ)
  | 18 => (367222201221 / 500000000000 : ℝ)
  | 19 => (368137385007 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch079Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (701932921909 / 1000000000000 : ℝ)
  | 1 => (175978216653 / 250000000000 : ℝ)
  | 2 => (17647124023 / 25000000000 : ℝ)
  | 3 => (88481136199 / 125000000000 : ℝ)
  | 4 => (709805136737 / 1000000000000 : ℝ)
  | 5 => (711752985811 / 1000000000000 : ℝ)
  | 6 => (142738503923 / 200000000000 : ℝ)
  | 7 => (357811810147 / 500000000000 : ℝ)
  | 8 => (179386542333 / 250000000000 : ℝ)
  | 9 => (11241563243 / 15625000000 : ℝ)
  | 10 => (721365135113 / 1000000000000 : ℝ)
  | 11 => (180815327877 / 250000000000 : ℝ)
  | 12 => (18128711389 / 25000000000 : ℝ)
  | 13 => (29081057817 / 40000000000 : ℝ)
  | 14 => (36444757929 / 50000000000 : ℝ)
  | 15 => (730754471831 / 1000000000000 : ℝ)
  | 16 => (732604261303 / 1000000000000 : ℝ)
  | 17 => (734444402443 / 1000000000000 : ℝ)
  | 18 => (147254954003 / 200000000000 : ℝ)
  | 19 => (46130952381 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch079Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1580 : ℝ) + (j.val : ℝ)) / 1600)
      (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch079Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch079Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1580 : ℝ) + (j.val : ℝ)) / 1600)
    (((1580 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch079Neg20WeightLower j.val) (hpThetaShiftOneBatch079Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch079Neg20WeightLower, hpThetaShiftOneBatch079Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch079Neg20_integral_bounds :
    (198907 / 31250000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (79 / 80 : ℝ) ((79 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (3302371 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1580 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch079Lower hpThetaJensenCellsBatch079Upper
    hpThetaShiftOneBatch079Neg20WeightLower hpThetaShiftOneBatch079Neg20WeightUpper hpThetaJensenCellsBatch079_bounds hpThetaShiftOneBatch079Neg20_weight_bounds
  have hl : (198907 / 31250000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch079Lower j * hpThetaShiftOneBatch079Neg20WeightLower j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftOneBatch079Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftOneBatch079Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch079Lower j * hpThetaShiftOneBatch079Neg20WeightUpper j)
        (hpThetaJensenCellsBatch079Upper j * hpThetaShiftOneBatch079Neg20WeightUpper j) / 1600) ≤ (3302371 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch079Lower, hpThetaJensenCellsBatch079Upper,
      hpThetaShiftOneBatch079Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1580 : ℝ) / 1600 = 79 / 80 by norm_num,
    show ((1580 : ℝ) + 20) / 1600 = (79 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch079Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch079Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch079Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch079Neg20_integral_bounds
end HodgeProofHP
