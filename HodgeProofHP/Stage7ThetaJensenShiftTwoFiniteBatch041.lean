/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch041

/-! Exact signed weight and batch integral certificates, batch 41 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch041Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (4098833639 / 1000000000000 : ℝ)
  | 1 => (824050497 / 200000000000 : ℝ)
  | 2 => (82825719 / 20000000000 : ℝ)
  | 3 => (2080960981 / 500000000000 : ℝ)
  | 4 => (522768533 / 125000000000 : ℝ)
  | 5 => (4201952411 / 1000000000000 : ℝ)
  | 6 => (1055330443 / 250000000000 : ℝ)
  | 7 => (2120121761 / 500000000000 : ℝ)
  | 8 => (4258704647 / 1000000000000 : ℝ)
  | 9 => (855338387 / 200000000000 : ℝ)
  | 10 => (4294191981 / 1000000000000 : ℝ)
  | 11 => (2155595589 / 500000000000 : ℝ)
  | 12 => (4327675721 / 1000000000000 : ℝ)
  | 13 => (4343631599 / 1000000000000 : ℝ)
  | 14 => (21795223 / 5000000000 : ℝ)
  | 15 => (2186950151 / 500000000000 : ℝ)
  | 16 => (2194092037 / 500000000000 : ℝ)
  | 17 => (176075243 / 40000000000 : ℝ)
  | 18 => (4414976251 / 1000000000000 : ℝ)
  | 19 => (442745433 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch041Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2060126243 / 500000000000 : ℝ)
  | 1 => (4141285951 / 1000000000000 : ℝ)
  | 2 => (4161921963 / 1000000000000 : ℝ)
  | 3 => (836429653 / 200000000000 : ℝ)
  | 4 => (1050488103 / 250000000000 : ℝ)
  | 5 => (4221321773 / 1000000000000 : ℝ)
  | 6 => (4240243523 / 1000000000000 : ℝ)
  | 7 => (532338081 / 125000000000 : ℝ)
  | 8 => (133646623 / 31250000000 : ℝ)
  | 9 => (2147095991 / 500000000000 : ℝ)
  | 10 => (4311191179 / 1000000000000 : ℝ)
  | 11 => (2163837861 / 500000000000 : ℝ)
  | 12 => (10859079 / 2500000000 : ℝ)
  | 13 => (4359044601 / 1000000000000 : ℝ)
  | 14 => (4373900303 / 1000000000000 : ℝ)
  | 15 => (175527363 / 40000000000 : ℝ)
  | 16 => (1100470269 / 250000000000 : ℝ)
  | 17 => (1103744063 / 250000000000 : ℝ)
  | 18 => (4427454331 / 1000000000000 : ℝ)
  | 19 => (277456239 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch041Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((820 : ℝ) + (j.val : ℝ)) / 1600)
      (((820 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch041Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch041Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((820 : ℝ) + (j.val : ℝ)) / 1600)
    (((820 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch041Neg100WeightLower j.val) (hpThetaShiftTwoBatch041Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch041Neg100WeightLower, hpThetaShiftTwoBatch041Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch041Neg100_integral_bounds :
    (5071260027 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (5177791171 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (820 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch041Lower hpThetaJensenCellsBatch041Upper
    hpThetaShiftTwoBatch041Neg100WeightLower hpThetaShiftTwoBatch041Neg100WeightUpper hpThetaJensenCellsBatch041_bounds hpThetaShiftTwoBatch041Neg100_weight_bounds
  have hl : (5071260027 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch041Lower j * hpThetaShiftTwoBatch041Neg100WeightLower j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftTwoBatch041Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftTwoBatch041Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch041Lower j * hpThetaShiftTwoBatch041Neg100WeightUpper j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftTwoBatch041Neg100WeightUpper j) / 1600) ≤ (5177791171 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftTwoBatch041Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (820 : ℝ) / 1600 = 41 / 80 by norm_num,
    show ((820 : ℝ) + 20) / 1600 = (41 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch041Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (107363973 / 125000000000 : ℝ)
  | 1 => (176701199 / 200000000000 : ℝ)
  | 2 => (454180479 / 500000000000 : ℝ)
  | 3 => (466738773 / 500000000000 : ℝ)
  | 4 => (119857077 / 125000000000 : ℝ)
  | 5 => (15382797 / 15625000000 : ℝ)
  | 6 => (202081109 / 200000000000 : ℝ)
  | 7 => (129572129 / 125000000000 : ℝ)
  | 8 => (1063014253 / 1000000000000 : ℝ)
  | 9 => (1089717977 / 1000000000000 : ℝ)
  | 10 => (139586119 / 125000000000 : ℝ)
  | 11 => (571963953 / 500000000000 : ℝ)
  | 12 => (23428711 / 20000000000 : ℝ)
  | 13 => (1199212571 / 1000000000000 : ℝ)
  | 14 => (1227259639 / 1000000000000 : ℝ)
  | 15 => (627788701 / 500000000000 : ℝ)
  | 16 => (256833297 / 200000000000 : ℝ)
  | 17 => (1313027493 / 1000000000000 : ℝ)
  | 18 => (1342161009 / 1000000000000 : ℝ)
  | 19 => (685783797 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch041Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (220876499 / 250000000000 : ℝ)
  | 1 => (908360959 / 1000000000000 : ℝ)
  | 2 => (933477547 / 1000000000000 : ℝ)
  | 3 => (958856617 / 1000000000000 : ℝ)
  | 4 => (984499009 / 1000000000000 : ℝ)
  | 5 => (505202773 / 500000000000 : ℝ)
  | 6 => (1036577033 / 1000000000000 : ℝ)
  | 7 => (531507127 / 500000000000 : ℝ)
  | 8 => (544858989 / 500000000000 : ℝ)
  | 9 => (1116688953 / 1000000000000 : ℝ)
  | 10 => (1143927907 / 1000000000000 : ℝ)
  | 11 => (1171435551 / 1000000000000 : ℝ)
  | 12 => (299803143 / 250000000000 : ℝ)
  | 13 => (30681491 / 25000000000 : ℝ)
  | 14 => (1255577403 / 1000000000000 : ℝ)
  | 15 => (642083243 / 500000000000 : ℝ)
  | 16 => (656513747 / 500000000000 : ℝ)
  | 17 => (134216101 / 100000000000 : ℝ)
  | 18 => (274313519 / 200000000000 : ℝ)
  | 19 => (700623893 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch041Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((820 : ℝ) + (j.val : ℝ)) / 1600)
      (((820 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch041Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch041Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((820 : ℝ) + (j.val : ℝ)) / 1600)
    (((820 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch041Neg65WeightLower j.val) (hpThetaShiftTwoBatch041Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch041Neg65WeightLower, hpThetaShiftTwoBatch041Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch041Neg65_integral_bounds :
    (1306115227 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (1360875147 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (820 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch041Lower hpThetaJensenCellsBatch041Upper
    hpThetaShiftTwoBatch041Neg65WeightLower hpThetaShiftTwoBatch041Neg65WeightUpper hpThetaJensenCellsBatch041_bounds hpThetaShiftTwoBatch041Neg65_weight_bounds
  have hl : (1306115227 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch041Lower j * hpThetaShiftTwoBatch041Neg65WeightLower j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftTwoBatch041Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftTwoBatch041Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch041Lower j * hpThetaShiftTwoBatch041Neg65WeightUpper j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftTwoBatch041Neg65WeightUpper j) / 1600) ≤ (1360875147 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftTwoBatch041Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (820 : ℝ) / 1600 = 41 / 80 by norm_num,
    show ((820 : ℝ) + 20) / 1600 = (41 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch041Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1192919377 / 1000000000000 : ℝ)
  | 1 => (-298001999 / 250000000000 : ℝ)
  | 2 => (-1190973013 / 1000000000000 : ℝ)
  | 3 => (-1189813037 / 1000000000000 : ℝ)
  | 4 => (-1188526671 / 1000000000000 : ℝ)
  | 5 => (-18548633 / 15625000000 : ℝ)
  | 6 => (-23711383 / 20000000000 : ℝ)
  | 7 => (-118389517 / 100000000000 : ℝ)
  | 8 => (-1182089153 / 1000000000000 : ℝ)
  | 9 => (-118014967 / 100000000000 : ℝ)
  | 10 => (-1178075291 / 1000000000000 : ℝ)
  | 11 => (-1175864577 / 1000000000000 : ℝ)
  | 12 => (-293379021 / 250000000000 : ℝ)
  | 13 => (-292757091 / 250000000000 : ℝ)
  | 14 => (-1168399961 / 1000000000000 : ℝ)
  | 15 => (-145703677 / 125000000000 : ℝ)
  | 16 => (-581357631 / 500000000000 : ℝ)
  | 17 => (-1159656029 / 1000000000000 : ℝ)
  | 18 => (-1156450241 / 1000000000000 : ℝ)
  | 19 => (-576548207 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch041Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-238401599 / 200000000000 : ℝ)
  | 1 => (-297743253 / 250000000000 : ℝ)
  | 2 => (-297453259 / 250000000000 : ℝ)
  | 3 => (-118852667 / 100000000000 : ℝ)
  | 4 => (-1187112511 / 1000000000000 : ℝ)
  | 5 => (-1185569149 / 1000000000000 : ℝ)
  | 6 => (-1183895169 / 1000000000000 : ℝ)
  | 7 => (-18470143 / 15625000000 : ℝ)
  | 8 => (-1180149669 / 1000000000000 : ℝ)
  | 9 => (-117807529 / 100000000000 : ℝ)
  | 10 => (-4593221 / 3906250000 : ℝ)
  | 11 => (-1173516083 / 1000000000000 : ℝ)
  | 12 => (-1171028363 / 1000000000000 : ℝ)
  | 13 => (-29209999 / 25000000000 : ℝ)
  | 14 => (-233125883 / 200000000000 : ℝ)
  | 15 => (-1162715261 / 1000000000000 : ℝ)
  | 16 => (-289914007 / 250000000000 : ℝ)
  | 17 => (-3613907 / 3125000000 : ℝ)
  | 18 => (-1153096413 / 1000000000000 : ℝ)
  | 19 => (-574796531 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch041Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((820 : ℝ) + (j.val : ℝ)) / 1600)
      (((820 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch041Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch041Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((820 : ℝ) + (j.val : ℝ)) / 1600)
    (((820 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch041Neg45WeightLower j.val) (hpThetaShiftTwoBatch041Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch041Neg45WeightLower, hpThetaShiftTwoBatch041Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch041Neg45_integral_bounds :
    (-11102779 / 7812500000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-1394980801 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (820 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch041Lower hpThetaJensenCellsBatch041Upper
    hpThetaShiftTwoBatch041Neg45WeightLower hpThetaShiftTwoBatch041Neg45WeightUpper hpThetaJensenCellsBatch041_bounds hpThetaShiftTwoBatch041Neg45_weight_bounds
  have hl : (-11102779 / 7812500000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch041Lower j * hpThetaShiftTwoBatch041Neg45WeightLower j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftTwoBatch041Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftTwoBatch041Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch041Lower j * hpThetaShiftTwoBatch041Neg45WeightUpper j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftTwoBatch041Neg45WeightUpper j) / 1600) ≤ (-1394980801 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftTwoBatch041Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (820 : ℝ) / 1600 = 41 / 80 by norm_num,
    show ((820 : ℝ) + 20) / 1600 = (41 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch041Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-460554197 / 500000000000 : ℝ)
  | 1 => (-1820421 / 1953125000 : ℝ)
  | 2 => (-943049097 / 1000000000000 : ℝ)
  | 3 => (-23852221 / 25000000000 : ℝ)
  | 4 => (-965174589 / 1000000000000 : ℝ)
  | 5 => (-244076537 / 250000000000 : ℝ)
  | 6 => (-197496663 / 200000000000 : ℝ)
  | 7 => (-998705887 / 1000000000000 : ℝ)
  | 8 => (-126246707 / 125000000000 : ℝ)
  | 9 => (-127660801 / 125000000000 : ℝ)
  | 10 => (-1032643929 / 1000000000000 : ℝ)
  | 11 => (-522022999 / 500000000000 : ℝ)
  | 12 => (-105549239 / 100000000000 : ℝ)
  | 13 => (-266745719 / 250000000000 : ℝ)
  | 14 => (-43140689 / 40000000000 : ℝ)
  | 15 => (-1362619 / 1250000000 : ℝ)
  | 16 => (-1101716559 / 1000000000000 : ℝ)
  | 17 => (-1113381059 / 1000000000000 : ℝ)
  | 18 => (-17579507 / 15625000000 : ℝ)
  | 19 => (-45473539 / 40000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch041Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-910207807 / 1000000000000 : ℝ)
  | 1 => (-921108393 / 1000000000000 : ℝ)
  | 2 => (-932055551 / 1000000000000 : ℝ)
  | 3 => (-117881137 / 125000000000 : ℝ)
  | 4 => (-954088839 / 1000000000000 : ℝ)
  | 5 => (-241293647 / 250000000000 : ℝ)
  | 6 => (-976306147 / 1000000000000 : ℝ)
  | 7 => (-493741657 / 500000000000 : ℝ)
  | 8 => (-499352943 / 500000000000 : ℝ)
  | 9 => (-201994731 / 200000000000 : ℝ)
  | 10 => (-1021286407 / 1000000000000 : ℝ)
  | 11 => (-129080491 / 125000000000 : ℝ)
  | 12 => (-1044045997 / 1000000000000 : ℝ)
  | 13 => (-1055492389 / 1000000000000 : ℝ)
  | 14 => (-8535863 / 8000000000 : ℝ)
  | 15 => (-134814653 / 125000000000 : ℝ)
  | 16 => (-1090095199 / 1000000000000 : ℝ)
  | 17 => (-550858279 / 500000000000 : ℝ)
  | 18 => (-556690529 / 500000000000 : ℝ)
  | 19 => (-1125088447 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch041Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((820 : ℝ) + (j.val : ℝ)) / 1600)
      (((820 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch041Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch041Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((820 : ℝ) + (j.val : ℝ)) / 1600)
    (((820 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch041Neg25WeightLower j.val) (hpThetaShiftTwoBatch041Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch041Neg25WeightLower, hpThetaShiftTwoBatch041Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch041Neg25_integral_bounds :
    (-1236788273 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (41 / 80 : ℝ) ((41 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-601383389 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (820 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch041Lower hpThetaJensenCellsBatch041Upper
    hpThetaShiftTwoBatch041Neg25WeightLower hpThetaShiftTwoBatch041Neg25WeightUpper hpThetaJensenCellsBatch041_bounds hpThetaShiftTwoBatch041Neg25_weight_bounds
  have hl : (-1236788273 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch041Lower j * hpThetaShiftTwoBatch041Neg25WeightLower j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftTwoBatch041Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftTwoBatch041Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch041Lower j * hpThetaShiftTwoBatch041Neg25WeightUpper j)
        (hpThetaJensenCellsBatch041Upper j * hpThetaShiftTwoBatch041Neg25WeightUpper j) / 1600) ≤ (-601383389 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch041Lower, hpThetaJensenCellsBatch041Upper,
      hpThetaShiftTwoBatch041Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (820 : ℝ) / 1600 = 41 / 80 by norm_num,
    show ((820 : ℝ) + 20) / 1600 = (41 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch041Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch041Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch041Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch041Neg25_integral_bounds
end HodgeProofHP
