/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeBernstein
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch078

/-! Exact signed weight and batch integral certificates, batch 78 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftThreeBatch078Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-482142347901 / 1000000000000 : ℝ)
  | 1 => (-243255764227 / 500000000000 : ℝ)
  | 2 => (-490916171337 / 1000000000000 : ℝ)
  | 3 => (-19814261317 / 40000000000 : ℝ)
  | 4 => (-499832871227 / 1000000000000 : ℝ)
  | 5 => (-504345445903 / 1000000000000 : ℝ)
  | 6 => (-508894518267 / 1000000000000 : ℝ)
  | 7 => (-5134803513 / 10000000000 : ℝ)
  | 8 => (-103620641931 / 200000000000 : ℝ)
  | 9 => (-522763359673 / 1000000000000 : ℝ)
  | 10 => (-105492213877 / 200000000000 : ℝ)
  | 11 => (-532196608527 / 1000000000000 : ℝ)
  | 12 => (-536970248547 / 1000000000000 : ℝ)
  | 13 => (-270891131307 / 500000000000 : ℝ)
  | 14 => (-136658231407 / 250000000000 : ℝ)
  | 15 => (-551522514233 / 1000000000000 : ℝ)
  | 16 => (-556451306819 / 1000000000000 : ℝ)
  | 17 => (-561419583541 / 1000000000000 : ℝ)
  | 18 => (-566427626321 / 1000000000000 : ℝ)
  | 19 => (-285737859431 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch078Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-477808374933 / 1000000000000 : ℝ)
  | 1 => (-4821423479 / 10000000000 : ℝ)
  | 2 => (-486511528453 / 1000000000000 : ℝ)
  | 3 => (-61364521417 / 125000000000 : ℝ)
  | 4 => (-123839133231 / 250000000000 : ℝ)
  | 5 => (-249916435613 / 500000000000 : ℝ)
  | 6 => (-252172722951 / 500000000000 : ℝ)
  | 7 => (-254447259133 / 500000000000 : ℝ)
  | 8 => (-513480351299 / 1000000000000 : ℝ)
  | 9 => (-259051604827 / 500000000000 : ℝ)
  | 10 => (-65345419959 / 125000000000 : ℝ)
  | 11 => (-65932633673 / 125000000000 : ℝ)
  | 12 => (-266098304263 / 500000000000 : ℝ)
  | 13 => (-268485124273 / 500000000000 : ℝ)
  | 14 => (-541782262613 / 1000000000000 : ℝ)
  | 15 => (-546632925627 / 1000000000000 : ℝ)
  | 16 => (-68940314279 / 125000000000 : ℝ)
  | 17 => (-278225653409 / 500000000000 : ℝ)
  | 18 => (-28070979177 / 50000000000 : ℝ)
  | 19 => (-7080345329 / 12500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch078Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1560 : ℝ) + (j.val : ℝ)) / 1600)
      (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch078Neg100WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-100) u ∧
      hpThetaJensenShiftThreeWeight (-100) u ≤ hpThetaShiftThreeBatch078Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-100) (((1560 : ℝ) + (j.val : ℝ)) / 1600)
    (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch078Neg100WeightLower j.val) (hpThetaShiftThreeBatch078Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch078Neg100WeightLower, hpThetaShiftThreeBatch078Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch078Neg100_integral_bounds :
    (-1592621 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-100) u) ≤ (-953969 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-100) (1560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch078Lower hpThetaJensenCellsBatch078Upper
    hpThetaShiftThreeBatch078Neg100WeightLower hpThetaShiftThreeBatch078Neg100WeightUpper hpThetaJensenCellsBatch078_bounds hpThetaShiftThreeBatch078Neg100_weight_bounds
  have hl : (-1592621 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch078Lower j * hpThetaShiftThreeBatch078Neg100WeightLower j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftThreeBatch078Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftThreeBatch078Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch078Lower j * hpThetaShiftThreeBatch078Neg100WeightUpper j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftThreeBatch078Neg100WeightUpper j) / 1600) ≤ (-953969 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftThreeBatch078Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1560 : ℝ) / 1600 = 78 / 80 by norm_num,
    show ((1560 : ℝ) + 20) / 1600 = (78 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch078Neg70WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-24759968257 / 250000000000 : ℝ)
  | 1 => (-20011413703 / 200000000000 : ℝ)
  | 2 => (-101083346467 / 1000000000000 : ℝ)
  | 3 => (-51059388801 / 500000000000 : ℝ)
  | 4 => (-25790858279 / 250000000000 : ℝ)
  | 5 => (-6513586543 / 62500000000 : ℝ)
  | 6 => (-105280704481 / 1000000000000 : ℝ)
  | 7 => (-53176732573 / 500000000000 : ℝ)
  | 8 => (-107435739823 / 1000000000000 : ℝ)
  | 9 => (-54263801073 / 500000000000 : ℝ)
  | 10 => (-21925825249 / 200000000000 : ℝ)
  | 11 => (-27685096687 / 250000000000 : ℝ)
  | 12 => (-55930729393 / 500000000000 : ℝ)
  | 13 => (-112992417993 / 1000000000000 : ℝ)
  | 14 => (-114133340513 / 1000000000000 : ℝ)
  | 15 => (-115284302997 / 1000000000000 : ℝ)
  | 16 => (-58222691307 / 500000000000 : ℝ)
  | 17 => (-23523331409 / 200000000000 : ℝ)
  | 18 => (-59399102247 / 500000000000 : ℝ)
  | 19 => (-29997525921 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch078Neg70WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-49015844881 / 500000000000 : ℝ)
  | 1 => (-99039873027 / 1000000000000 : ℝ)
  | 2 => (-50028534257 / 500000000000 : ℝ)
  | 3 => (-50541673233 / 500000000000 : ℝ)
  | 4 => (-102118777601 / 1000000000000 : ℝ)
  | 5 => (-20632686623 / 200000000000 : ℝ)
  | 6 => (-104217384687 / 1000000000000 : ℝ)
  | 7 => (-658004403 / 6250000000 : ℝ)
  | 8 => (-21270693029 / 200000000000 : ℝ)
  | 9 => (-53717869911 / 500000000000 : ℝ)
  | 10 => (-21705520429 / 200000000000 : ℝ)
  | 11 => (-27407281561 / 250000000000 : ℝ)
  | 12 => (-110740386747 / 1000000000000 : ℝ)
  | 13 => (-22372291757 / 200000000000 : ℝ)
  | 14 => (-14124052249 / 125000000000 : ℝ)
  | 15 => (-3566666891 / 31250000000 : ℝ)
  | 16 => (-28821075749 / 250000000000 : ℝ)
  | 17 => (-116445382613 / 1000000000000 : ℝ)
  | 18 => (-29404164261 / 250000000000 : ℝ)
  | 19 => (-118798204493 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch078Neg70_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1560 : ℝ) + (j.val : ℝ)) / 1600)
      (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch078Neg70WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-70) u ∧
      hpThetaJensenShiftThreeWeight (-70) u ≤ hpThetaShiftThreeBatch078Neg70WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-70) (((1560 : ℝ) + (j.val : ℝ)) / 1600)
    (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch078Neg70WeightLower j.val) (hpThetaShiftThreeBatch078Neg70WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch078Neg70WeightLower, hpThetaShiftThreeBatch078Neg70WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch078Neg70_integral_bounds :
    (-1653011 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ∧
    (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-70) u) ≤ (-197799 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-70) (1560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch078Lower hpThetaJensenCellsBatch078Upper
    hpThetaShiftThreeBatch078Neg70WeightLower hpThetaShiftThreeBatch078Neg70WeightUpper hpThetaJensenCellsBatch078_bounds hpThetaShiftThreeBatch078Neg70_weight_bounds
  have hl : (-1653011 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch078Lower j * hpThetaShiftThreeBatch078Neg70WeightLower j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftThreeBatch078Neg70WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftThreeBatch078Neg70WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch078Lower j * hpThetaShiftThreeBatch078Neg70WeightUpper j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftThreeBatch078Neg70WeightUpper j) / 1600) ≤ (-197799 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftThreeBatch078Neg70WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1560 : ℝ) / 1600 = 78 / 80 by norm_num,
    show ((1560 : ℝ) + 20) / 1600 = (78 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch078Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-735728987 / 200000000000 : ℝ)
  | 1 => (-753440811 / 200000000000 : ℝ)
  | 2 => (-3856922711 / 1000000000000 : ℝ)
  | 3 => (-986953069 / 250000000000 : ℝ)
  | 4 => (-4039884211 / 1000000000000 : ℝ)
  | 5 => (-4133150073 / 1000000000000 : ℝ)
  | 6 => (-33028293 / 7812500000 : ℝ)
  | 7 => (-2161655121 / 500000000000 : ℝ)
  | 8 => (-1105057029 / 250000000000 : ℝ)
  | 9 => (-4518387047 / 1000000000000 : ℝ)
  | 10 => (-1154449763 / 250000000000 : ℝ)
  | 11 => (-4718476239 / 1000000000000 : ℝ)
  | 12 => (-4820430813 / 1000000000000 : ℝ)
  | 13 => (-4923675073 / 1000000000000 : ℝ)
  | 14 => (-628527677 / 125000000000 : ℝ)
  | 15 => (-2567041167 / 500000000000 : ℝ)
  | 16 => (-327579401 / 62500000000 : ℝ)
  | 17 => (-106995967 / 20000000000 : ℝ)
  | 18 => (-2729839461 / 500000000000 : ℝ)
  | 19 => (-696365627 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch078Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-718246813 / 200000000000 : ℝ)
  | 1 => (-1839322467 / 500000000000 : ℝ)
  | 2 => (-1883602027 / 500000000000 : ℝ)
  | 3 => (-385692271 / 100000000000 : ℝ)
  | 4 => (-157912491 / 40000000000 : ℝ)
  | 5 => (-403988421 / 100000000000 : ℝ)
  | 6 => (-516643759 / 125000000000 : ℝ)
  | 7 => (-4227621503 / 1000000000000 : ℝ)
  | 8 => (-4323310241 / 1000000000000 : ℝ)
  | 9 => (-884045623 / 200000000000 : ℝ)
  | 10 => (-2259193523 / 500000000000 : ℝ)
  | 11 => (-4617799051 / 1000000000000 : ℝ)
  | 12 => (-2359238119 / 500000000000 : ℝ)
  | 13 => (-1205107703 / 250000000000 : ℝ)
  | 14 => (-76932423 / 15625000000 : ℝ)
  | 15 => (-1005644283 / 200000000000 : ℝ)
  | 16 => (-5134082333 / 1000000000000 : ℝ)
  | 17 => (-1048254083 / 200000000000 : ℝ)
  | 18 => (-5349798349 / 1000000000000 : ℝ)
  | 19 => (-5459678921 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch078Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1560 : ℝ) + (j.val : ℝ)) / 1600)
      (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch078Neg45WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-45) u ∧
      hpThetaJensenShiftThreeWeight (-45) u ≤ hpThetaShiftThreeBatch078Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-45) (((1560 : ℝ) + (j.val : ℝ)) / 1600)
    (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch078Neg45WeightLower j.val) (hpThetaShiftThreeBatch078Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch078Neg45WeightLower, hpThetaShiftThreeBatch078Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch078Neg45_integral_bounds :
    (-68769 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-45) u) ≤ (-65053 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-45) (1560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch078Lower hpThetaJensenCellsBatch078Upper
    hpThetaShiftThreeBatch078Neg45WeightLower hpThetaShiftThreeBatch078Neg45WeightUpper hpThetaJensenCellsBatch078_bounds hpThetaShiftThreeBatch078Neg45_weight_bounds
  have hl : (-68769 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch078Lower j * hpThetaShiftThreeBatch078Neg45WeightLower j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftThreeBatch078Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftThreeBatch078Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch078Lower j * hpThetaShiftThreeBatch078Neg45WeightUpper j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftThreeBatch078Neg45WeightUpper j) / 1600) ≤ (-65053 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftThreeBatch078Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1560 : ℝ) / 1600 = 78 / 80 by norm_num,
    show ((1560 : ℝ) + 20) / 1600 = (78 + 1) / 80 by norm_num] using hb

def hpThetaShiftThreeBatch078Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (1503861229 / 1000000000000 : ℝ)
  | 1 => (1519708837 / 1000000000000 : ℝ)
  | 2 => (767822937 / 500000000000 : ℝ)
  | 3 => (775836219 / 500000000000 : ℝ)
  | 4 => (78389431 / 50000000000 : ℝ)
  | 5 => (1583994509 / 1000000000000 : ℝ)
  | 6 => (1600290191 / 1000000000000 : ℝ)
  | 7 => (808337873 / 500000000000 : ℝ)
  | 8 => (1633151251 / 1000000000000 : ℝ)
  | 9 => (1649716779 / 1000000000000 : ℝ)
  | 10 => (1666372399 / 1000000000000 : ℝ)
  | 11 => (67324727 / 40000000000 : ℝ)
  | 12 => (212494271 / 125000000000 : ℝ)
  | 13 => (343376087 / 200000000000 : ℝ)
  | 14 => (866948513 / 500000000000 : ℝ)
  | 15 => (1751003989 / 1000000000000 : ℝ)
  | 16 => (1768201369 / 1000000000000 : ℝ)
  | 17 => (892744601 / 500000000000 : ℝ)
  | 18 => (450716881 / 250000000000 : ℝ)
  | 19 => (455084091 / 250000000000 : ℝ)
  | _ => 0

def hpThetaShiftThreeBatch078Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (759854419 / 500000000000 : ℝ)
  | 1 => (12285167 / 8000000000 : ℝ)
  | 2 => (1551672439 / 1000000000000 : ℝ)
  | 3 => (1567788621 / 1000000000000 : ℝ)
  | 4 => (158399451 / 100000000000 : ℝ)
  | 5 => (100018137 / 62500000000 : ℝ)
  | 6 => (1616675747 / 1000000000000 : ℝ)
  | 7 => (408287813 / 250000000000 : ℝ)
  | 8 => (82485839 / 50000000000 : ℝ)
  | 9 => (4165931 / 2500000000 : ℝ)
  | 10 => (52597443 / 31250000000 : ℝ)
  | 11 => (1699954169 / 1000000000000 : ℝ)
  | 12 => (429220109 / 250000000000 : ℝ)
  | 13 => (1733897027 / 1000000000000 : ℝ)
  | 14 => (175100399 / 100000000000 : ℝ)
  | 15 => (176820137 / 100000000000 : ℝ)
  | 16 => (1785489203 / 1000000000000 : ℝ)
  | 17 => (72114701 / 40000000000 : ℝ)
  | 18 => (364067273 / 200000000000 : ℝ)
  | 19 => (459473937 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
-- Check thirteen exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftThreeBatch078Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1560 : ℝ) + (j.val : ℝ)) / 1600)
      (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftThreeBatch078Neg25WeightLower j.val ≤ hpThetaJensenShiftThreeWeight (-25) u ∧
      hpThetaJensenShiftThreeWeight (-25) u ≤ hpThetaShiftThreeBatch078Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftThreeWeight_bounds_of_coefficients
    (-25) (((1560 : ℝ) + (j.val : ℝ)) / 1600)
    (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftThreeBatch078Neg25WeightLower j.val) (hpThetaShiftThreeBatch078Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftThreeBernsteinCoefficient, hpThetaShiftThreeBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftThreeBatch078Neg25WeightLower, hpThetaShiftThreeBatch078Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftThreeBatch078Neg25_integral_bounds :
    (6071 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight (-25) u) ≤ (25367 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftThree_batchIntegral_of_bounds (-25) (1560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch078Lower hpThetaJensenCellsBatch078Upper
    hpThetaShiftThreeBatch078Neg25WeightLower hpThetaShiftThreeBatch078Neg25WeightUpper hpThetaJensenCellsBatch078_bounds hpThetaShiftThreeBatch078Neg25_weight_bounds
  have hl : (6071 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch078Lower j * hpThetaShiftThreeBatch078Neg25WeightLower j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftThreeBatch078Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftThreeBatch078Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch078Lower j * hpThetaShiftThreeBatch078Neg25WeightUpper j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftThreeBatch078Neg25WeightUpper j) / 1600) ≤ (25367 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftThreeBatch078Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1560 : ℝ) / 1600 = 78 / 80 by norm_num,
    show ((1560 : ℝ) + 20) / 1600 = (78 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftThreeBatch078Neg100_integral_bounds
#print axioms hpThetaShiftThreeBatch078Neg70_integral_bounds
#print axioms hpThetaShiftThreeBatch078Neg45_integral_bounds
#print axioms hpThetaShiftThreeBatch078Neg25_integral_bounds
end HodgeProofHP
