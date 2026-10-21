/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch044

/-! Exact signed weight and batch integral certificates, batch 44 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch044Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-208655332989 / 1000000000000 : ℝ)
  | 1 => (-217030326663 / 1000000000000 : ℝ)
  | 2 => (-112767689407 / 500000000000 : ℝ)
  | 3 => (-58542958453 / 250000000000 : ℝ)
  | 4 => (-30367630761 / 125000000000 : ℝ)
  | 5 => (-251844380193 / 1000000000000 : ℝ)
  | 6 => (-260883210849 / 1000000000000 : ℝ)
  | 7 => (-263729417 / 976562500 : ℝ)
  | 8 => (-8730403497 / 31250000000 : ℝ)
  | 9 => (-288826583111 / 1000000000000 : ℝ)
  | 10 => (-74605338149 / 250000000000 : ℝ)
  | 11 => (-154079323389 / 500000000000 : ℝ)
  | 12 => (-318039902583 / 1000000000000 : ℝ)
  | 13 => (-328066567501 / 1000000000000 : ℝ)
  | 14 => (-8456002491 / 25000000000 : ℝ)
  | 15 => (-348561967787 / 1000000000000 : ℝ)
  | 16 => (-179516825731 / 500000000000 : ℝ)
  | 17 => (-14786265639 / 40000000000 : ℝ)
  | 18 => (-380432437487 / 1000000000000 : ℝ)
  | 19 => (-48920319133 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch044Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-20040906343 / 100000000000 : ℝ)
  | 1 => (-52163833247 / 250000000000 : ℝ)
  | 2 => (-108515163331 / 500000000000 : ℝ)
  | 3 => (-225535378813 / 1000000000000 : ℝ)
  | 4 => (-234171833811 / 1000000000000 : ℝ)
  | 5 => (-242941046087 / 1000000000000 : ℝ)
  | 6 => (-7870136881 / 31250000000 : ℝ)
  | 7 => (-8152600339 / 31250000000 : ℝ)
  | 8 => (-270058923007 / 1000000000000 : ℝ)
  | 9 => (-279372911903 / 1000000000000 : ℝ)
  | 10 => (-28882658311 / 100000000000 : ℝ)
  | 11 => (-59684270519 / 200000000000 : ℝ)
  | 12 => (-308158646777 / 1000000000000 : ℝ)
  | 13 => (-159019951291 / 500000000000 : ℝ)
  | 14 => (-131226627 / 400000000 : ℝ)
  | 15 => (-338240099639 / 1000000000000 : ℝ)
  | 16 => (-174280983893 / 500000000000 : ℝ)
  | 17 => (-359033651461 / 1000000000000 : ℝ)
  | 18 => (-184828320487 / 500000000000 : ℝ)
  | 19 => (-190216218743 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch044Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((880 : ℝ) + (j.val : ℝ)) / 1600)
      (((880 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch044Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch044Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((880 : ℝ) + (j.val : ℝ)) / 1600)
    (((880 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch044Neg100WeightLower j.val) (hpThetaShiftOneBatch044Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch044Neg100WeightLower, hpThetaShiftOneBatch044Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch044Neg100_integral_bounds :
    (-213199433463 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-50669785707 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (880 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch044Lower hpThetaJensenCellsBatch044Upper
    hpThetaShiftOneBatch044Neg100WeightLower hpThetaShiftOneBatch044Neg100WeightUpper hpThetaJensenCellsBatch044_bounds hpThetaShiftOneBatch044Neg100_weight_bounds
  have hl : (-213199433463 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch044Lower j * hpThetaShiftOneBatch044Neg100WeightLower j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftOneBatch044Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftOneBatch044Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch044Lower j * hpThetaShiftOneBatch044Neg100WeightUpper j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftOneBatch044Neg100WeightUpper j) / 1600) ≤ (-50669785707 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftOneBatch044Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (880 : ℝ) / 1600 = 44 / 80 by norm_num,
    show ((880 : ℝ) + 20) / 1600 = (44 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch044Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (219265347967 / 1000000000000 : ℝ)
  | 1 => (110168629019 / 500000000000 : ℝ)
  | 2 => (221400587167 / 1000000000000 : ℝ)
  | 3 => (22245511973 / 100000000000 : ℝ)
  | 4 => (13968789871 / 62500000000 : ℝ)
  | 5 => (28067115227 / 125000000000 : ℝ)
  | 6 => (28195468651 / 125000000000 : ℝ)
  | 7 => (113290447871 / 500000000000 : ℝ)
  | 8 => (56897033707 / 250000000000 : ℝ)
  | 9 => (228585237643 / 1000000000000 : ℝ)
  | 10 => (229571973113 / 1000000000000 : ℝ)
  | 11 => (1801157093 / 7812500000 : ℝ)
  | 12 => (115756703203 / 500000000000 : ℝ)
  | 13 => (232467630717 / 1000000000000 : ℝ)
  | 14 => (46682108127 / 200000000000 : ℝ)
  | 15 => (117170946817 / 500000000000 : ℝ)
  | 16 => (11763072243 / 50000000000 : ℝ)
  | 17 => (23616894711 / 100000000000 : ℝ)
  | 18 => (118532075411 / 500000000000 : ℝ)
  | 19 => (47589360811 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch044Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (220337258039 / 1000000000000 : ℝ)
  | 1 => (6918768349 / 31250000000 : ℝ)
  | 2 => (222455119731 / 1000000000000 : ℝ)
  | 3 => (223500637937 / 1000000000000 : ℝ)
  | 4 => (224536921817 / 1000000000000 : ℝ)
  | 5 => (225563749209 / 1000000000000 : ℝ)
  | 6 => (226580895743 / 1000000000000 : ℝ)
  | 7 => (227588134829 / 1000000000000 : ℝ)
  | 8 => (57146309411 / 250000000000 : ℝ)
  | 9 => (114785986557 / 500000000000 : ℝ)
  | 10 => (46109621581 / 200000000000 : ℝ)
  | 11 => (231513406407 / 1000000000000 : ℝ)
  | 12 => (116233815359 / 500000000000 : ℝ)
  | 13 => (58352635159 / 250000000000 : ℝ)
  | 14 => (46868378727 / 200000000000 : ℝ)
  | 15 => (235261444861 / 1000000000000 : ℝ)
  | 16 => (236168947111 / 1000000000000 : ℝ)
  | 17 => (237064150823 / 1000000000000 : ℝ)
  | 18 => (29743350507 / 125000000000 : ℝ)
  | 19 => (238816652483 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch044Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((880 : ℝ) + (j.val : ℝ)) / 1600)
      (((880 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch044Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch044Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((880 : ℝ) + (j.val : ℝ)) / 1600)
    (((880 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch044Neg65WeightLower j.val) (hpThetaShiftOneBatch044Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch044Neg65WeightLower, hpThetaShiftOneBatch044Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch044Neg65_integral_bounds :
    (163372815161 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (16699071933 / 100000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (880 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch044Lower hpThetaJensenCellsBatch044Upper
    hpThetaShiftOneBatch044Neg65WeightLower hpThetaShiftOneBatch044Neg65WeightUpper hpThetaJensenCellsBatch044_bounds hpThetaShiftOneBatch044Neg65_weight_bounds
  have hl : (163372815161 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch044Lower j * hpThetaShiftOneBatch044Neg65WeightLower j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftOneBatch044Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftOneBatch044Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch044Lower j * hpThetaShiftOneBatch044Neg65WeightUpper j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftOneBatch044Neg65WeightUpper j) / 1600) ≤ (16699071933 / 100000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftOneBatch044Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (880 : ℝ) / 1600 = 44 / 80 by norm_num,
    show ((880 : ℝ) + 20) / 1600 = (44 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch044Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1221334747 / 50000000000 : ℝ)
  | 1 => (12631739237 / 500000000000 : ℝ)
  | 2 => (6526576153 / 250000000000 : ℝ)
  | 3 => (1347758921 / 50000000000 : ℝ)
  | 4 => (13905052347 / 500000000000 : ℝ)
  | 5 => (7167771989 / 250000000000 : ℝ)
  | 6 => (7384533113 / 250000000000 : ℝ)
  | 7 => (608224843 / 20000000000 : ℝ)
  | 8 => (31290420737 / 1000000000000 : ℝ)
  | 9 => (32175671617 / 1000000000000 : ℝ)
  | 10 => (6613399581 / 200000000000 : ℝ)
  | 11 => (3396440243 / 100000000000 : ℝ)
  | 12 => (2179242983 / 62500000000 : ℝ)
  | 13 => (894436401 / 25000000000 : ℝ)
  | 14 => (3669310931 / 100000000000 : ℝ)
  | 15 => (7522969837 / 200000000000 : ℝ)
  | 16 => (7708535401 / 200000000000 : ℝ)
  | 17 => (39476593809 / 1000000000000 : ℝ)
  | 18 => (10104150081 / 250000000000 : ℝ)
  | 19 => (41362696971 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch044Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1010539139 / 40000000000 : ℝ)
  | 1 => (26106304613 / 1000000000000 : ℝ)
  | 2 => (26955178421 / 1000000000000 : ℝ)
  | 3 => (5562020939 / 200000000000 : ℝ)
  | 4 => (28671087957 / 1000000000000 : ℝ)
  | 5 => (29538132453 / 1000000000000 : ℝ)
  | 6 => (30411242151 / 1000000000000 : ℝ)
  | 7 => (15645210369 / 500000000000 : ℝ)
  | 8 => (16087835809 / 500000000000 : ℝ)
  | 9 => (16533498953 / 500000000000 : ℝ)
  | 10 => (33964402431 / 1000000000000 : ℝ)
  | 11 => (34867887729 / 1000000000000 : ℝ)
  | 12 => (35777456041 / 1000000000000 : ℝ)
  | 13 => (36693109311 / 1000000000000 : ℝ)
  | 14 => (18807424593 / 500000000000 : ℝ)
  | 15 => (19271338503 / 500000000000 : ℝ)
  | 16 => (3947659381 / 100000000000 : ℝ)
  | 17 => (1616664013 / 40000000000 : ℝ)
  | 18 => (10340674243 / 250000000000 : ℝ)
  | 19 => (21157441927 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch044Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((880 : ℝ) + (j.val : ℝ)) / 1600)
      (((880 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch044Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch044Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((880 : ℝ) + (j.val : ℝ)) / 1600)
    (((880 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch044Neg40WeightLower j.val) (hpThetaShiftOneBatch044Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch044Neg40WeightLower, hpThetaShiftOneBatch044Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch044Neg40_integral_bounds :
    (5798782639 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (3032125609 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (880 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch044Lower hpThetaJensenCellsBatch044Upper
    hpThetaShiftOneBatch044Neg40WeightLower hpThetaShiftOneBatch044Neg40WeightUpper hpThetaJensenCellsBatch044_bounds hpThetaShiftOneBatch044Neg40_weight_bounds
  have hl : (5798782639 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch044Lower j * hpThetaShiftOneBatch044Neg40WeightLower j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftOneBatch044Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftOneBatch044Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch044Lower j * hpThetaShiftOneBatch044Neg40WeightUpper j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftOneBatch044Neg40WeightUpper j) / 1600) ≤ (3032125609 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftOneBatch044Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (880 : ℝ) / 1600 = 44 / 80 by norm_num,
    show ((880 : ℝ) + 20) / 1600 = (44 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch044Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-69558680633 / 1000000000000 : ℝ)
  | 1 => (-34884029999 / 500000000000 : ℝ)
  | 2 => (-34988136289 / 500000000000 : ℝ)
  | 3 => (-70183305313 / 1000000000000 : ℝ)
  | 4 => (-17597286277 / 250000000000 : ℝ)
  | 5 => (-4412111177 / 62500000000 : ℝ)
  | 6 => (-35398596659 / 500000000000 : ℝ)
  | 7 => (-17749843841 / 250000000000 : ℝ)
  | 8 => (-71200311733 / 1000000000000 : ℝ)
  | 9 => (-71399989153 / 1000000000000 : ℝ)
  | 10 => (-14319678863 / 200000000000 : ℝ)
  | 11 => (-71795513879 / 1000000000000 : ℝ)
  | 12 => (-71991334467 / 1000000000000 : ℝ)
  | 13 => (-18046460667 / 250000000000 : ℝ)
  | 14 => (-36189512519 / 500000000000 : ℝ)
  | 15 => (-14514173619 / 200000000000 : ℝ)
  | 16 => (-36380679163 / 500000000000 : ℝ)
  | 17 => (-9118810273 / 125000000000 : ℝ)
  | 18 => (-73138226087 / 1000000000000 : ℝ)
  | 19 => (-3666228821 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch044Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-69348147507 / 1000000000000 : ℝ)
  | 1 => (-8694835079 / 125000000000 : ℝ)
  | 2 => (-69768059997 / 1000000000000 : ℝ)
  | 3 => (-69976272577 / 1000000000000 : ℝ)
  | 4 => (-2193228291 / 31250000000 : ℝ)
  | 5 => (-70389145107 / 1000000000000 : ℝ)
  | 6 => (-70593778831 / 1000000000000 : ℝ)
  | 7 => (-70797193317 / 1000000000000 : ℝ)
  | 8 => (-70999375363 / 1000000000000 : ℝ)
  | 9 => (-17800077933 / 250000000000 : ℝ)
  | 10 => (-2231249661 / 31250000000 : ℝ)
  | 11 => (-35799197157 / 500000000000 : ℝ)
  | 12 => (-35897756939 / 500000000000 : ℝ)
  | 13 => (-35995667233 / 500000000000 : ℝ)
  | 14 => (-72185842667 / 1000000000000 : ℝ)
  | 15 => (-72379025037 / 1000000000000 : ℝ)
  | 16 => (-36285434047 / 500000000000 : ℝ)
  | 17 => (-2910454333 / 40000000000 : ℝ)
  | 18 => (-72950482183 / 1000000000000 : ℝ)
  | 19 => (-36569113043 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch044Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((880 : ℝ) + (j.val : ℝ)) / 1600)
      (((880 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch044Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch044Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((880 : ℝ) + (j.val : ℝ)) / 1600)
    (((880 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch044Neg20WeightLower j.val) (hpThetaShiftOneBatch044Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch044Neg20WeightLower, hpThetaShiftOneBatch044Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch044Neg20_integral_bounds :
    (-6493164597 / 125000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (44 / 80 : ℝ) ((44 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-25447798753 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (880 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch044Lower hpThetaJensenCellsBatch044Upper
    hpThetaShiftOneBatch044Neg20WeightLower hpThetaShiftOneBatch044Neg20WeightUpper hpThetaJensenCellsBatch044_bounds hpThetaShiftOneBatch044Neg20_weight_bounds
  have hl : (-6493164597 / 125000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch044Lower j * hpThetaShiftOneBatch044Neg20WeightLower j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftOneBatch044Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftOneBatch044Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch044Lower j * hpThetaShiftOneBatch044Neg20WeightUpper j)
        (hpThetaJensenCellsBatch044Upper j * hpThetaShiftOneBatch044Neg20WeightUpper j) / 1600) ≤ (-25447798753 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch044Lower, hpThetaJensenCellsBatch044Upper,
      hpThetaShiftOneBatch044Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (880 : ℝ) / 1600 = 44 / 80 by norm_num,
    show ((880 : ℝ) + 20) / 1600 = (44 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch044Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch044Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch044Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch044Neg20_integral_bounds
end HodgeProofHP
