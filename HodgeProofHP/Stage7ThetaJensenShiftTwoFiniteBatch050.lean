/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch050

/-! Exact signed weight and batch integral certificates, batch 50 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch050Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-21814488371 / 1000000000000 : ℝ)
  | 1 => (-11175698427 / 500000000000 : ℝ)
  | 2 => (-22896598999 / 1000000000000 : ℝ)
  | 3 => (-5862547857 / 250000000000 : ℝ)
  | 4 => (-12006135827 / 500000000000 : ℝ)
  | 5 => (-4916587617 / 200000000000 : ℝ)
  | 6 => (-1572643127 / 62500000000 : ℝ)
  | 7 => (-12875213859 / 500000000000 : ℝ)
  | 8 => (-26347452279 / 1000000000000 : ℝ)
  | 9 => (-13476732889 / 500000000000 : ℝ)
  | 10 => (-6892142801 / 250000000000 : ℝ)
  | 11 => (-14096436243 / 500000000000 : ℝ)
  | 12 => (-5765294899 / 200000000000 : ℝ)
  | 13 => (-7367370763 / 250000000000 : ℝ)
  | 14 => (-6024400987 / 200000000000 : ℝ)
  | 15 => (-1924009243 / 62500000000 : ℝ)
  | 16 => (-31456020623 / 1000000000000 : ℝ)
  | 17 => (-16068866417 / 500000000000 : ℝ)
  | 18 => (-8207348799 / 250000000000 : ℝ)
  | 19 => (-1676555969 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch050Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5321444453 / 250000000000 : ℝ)
  | 1 => (-2181448837 / 100000000000 : ℝ)
  | 2 => (-22351396853 / 1000000000000 : ℝ)
  | 3 => (-11448299499 / 500000000000 : ℝ)
  | 4 => (-23450191427 / 1000000000000 : ℝ)
  | 5 => (-24012271653 / 1000000000000 : ℝ)
  | 6 => (-6145734521 / 250000000000 : ℝ)
  | 7 => (-25162290031 / 1000000000000 : ℝ)
  | 8 => (-25750427717 / 1000000000000 : ℝ)
  | 9 => (-13173726139 / 500000000000 : ℝ)
  | 10 => (-26953465777 / 1000000000000 : ℝ)
  | 11 => (-27568571203 / 1000000000000 : ℝ)
  | 12 => (-5638574497 / 200000000000 : ℝ)
  | 13 => (-14413237247 / 500000000000 : ℝ)
  | 14 => (-29469483051 / 1000000000000 : ℝ)
  | 15 => (-15061002467 / 500000000000 : ℝ)
  | 16 => (-30784147887 / 1000000000000 : ℝ)
  | 17 => (-15728010311 / 500000000000 : ℝ)
  | 18 => (-32137732833 / 1000000000000 : ℝ)
  | 19 => (-6565879039 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch050Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1000 : ℝ) + (j.val : ℝ)) / 1600)
      (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch050Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch050Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1000 : ℝ) + (j.val : ℝ)) / 1600)
    (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch050Neg100WeightLower j.val) (hpThetaShiftTwoBatch050Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch050Neg100WeightLower, hpThetaShiftTwoBatch050Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch050Neg100_integral_bounds :
    (-6065040617 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-5814535951 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1000 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch050Lower hpThetaJensenCellsBatch050Upper
    hpThetaShiftTwoBatch050Neg100WeightLower hpThetaShiftTwoBatch050Neg100WeightUpper hpThetaJensenCellsBatch050_bounds hpThetaShiftTwoBatch050Neg100_weight_bounds
  have hl : (-6065040617 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch050Lower j * hpThetaShiftTwoBatch050Neg100WeightLower j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftTwoBatch050Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftTwoBatch050Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch050Lower j * hpThetaShiftTwoBatch050Neg100WeightUpper j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftTwoBatch050Neg100WeightUpper j) / 1600) ≤ (-5814535951 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftTwoBatch050Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1000 : ℝ) / 1600 = 50 / 80 by norm_num,
    show ((1000 : ℝ) + 20) / 1600 = (50 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch050Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (8924621373 / 1000000000000 : ℝ)
  | 1 => (4486751109 / 500000000000 : ℝ)
  | 2 => (2255505383 / 250000000000 : ℝ)
  | 3 => (4535083659 / 500000000000 : ℝ)
  | 4 => (9117927417 / 1000000000000 : ℝ)
  | 5 => (916528951 / 100000000000 : ℝ)
  | 6 => (4606120559 / 500000000000 : ℝ)
  | 7 => (5786731 / 625000000 : ℝ)
  | 8 => (2326215537 / 250000000000 : ℝ)
  | 9 => (9350505791 / 1000000000000 : ℝ)
  | 10 => (939568739 / 100000000000 : ℝ)
  | 11 => (9440393637 / 1000000000000 : ℝ)
  | 12 => (9484611053 / 1000000000000 : ℝ)
  | 13 => (952832599 / 100000000000 : ℝ)
  | 14 => (4785762313 / 500000000000 : ℝ)
  | 15 => (9614192963 / 1000000000000 : ℝ)
  | 16 => (2414079207 / 250000000000 : ℝ)
  | 17 => (9697881871 / 1000000000000 : ℝ)
  | 18 => (4869436781 / 500000000000 : ℝ)
  | 19 => (977927719 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch050Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (8973502219 / 1000000000000 : ℝ)
  | 1 => (9022021533 / 1000000000000 : ℝ)
  | 2 => (9070167319 / 1000000000000 : ℝ)
  | 3 => (4558963709 / 500000000000 : ℝ)
  | 4 => (9165289511 / 1000000000000 : ℝ)
  | 5 => (9212241119 / 1000000000000 : ℝ)
  | 6 => (9258769601 / 1000000000000 : ℝ)
  | 7 => (9304862149 / 1000000000000 : ℝ)
  | 8 => (146101653 / 15625000000 : ℝ)
  | 9 => (9395687391 / 1000000000000 : ℝ)
  | 10 => (4720196819 / 500000000000 : ℝ)
  | 11 => (4742305527 / 500000000000 : ℝ)
  | 12 => (9528325991 / 1000000000000 : ℝ)
  | 13 => (9571524627 / 1000000000000 : ℝ)
  | 14 => (2403548241 / 250000000000 : ℝ)
  | 15 => (9656316829 / 1000000000000 : ℝ)
  | 16 => (606117617 / 62500000000 : ℝ)
  | 17 => (9738873563 / 1000000000000 : ℝ)
  | 18 => (9779277191 / 1000000000000 : ℝ)
  | 19 => (1963815573 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch050Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1000 : ℝ) + (j.val : ℝ)) / 1600)
      (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch050Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch050Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1000 : ℝ) + (j.val : ℝ)) / 1600)
    (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch050Neg65WeightLower j.val) (hpThetaShiftTwoBatch050Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch050Neg65WeightLower, hpThetaShiftTwoBatch050Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch050Neg65_integral_bounds :
    (1022561421 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (1047722909 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1000 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch050Lower hpThetaJensenCellsBatch050Upper
    hpThetaShiftTwoBatch050Neg65WeightLower hpThetaShiftTwoBatch050Neg65WeightUpper hpThetaJensenCellsBatch050_bounds hpThetaShiftTwoBatch050Neg65_weight_bounds
  have hl : (1022561421 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch050Lower j * hpThetaShiftTwoBatch050Neg65WeightLower j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftTwoBatch050Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftTwoBatch050Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch050Lower j * hpThetaShiftTwoBatch050Neg65WeightUpper j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftTwoBatch050Neg65WeightUpper j) / 1600) ≤ (1047722909 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftTwoBatch050Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1000 : ℝ) / 1600 = 50 / 80 by norm_num,
    show ((1000 : ℝ) + 20) / 1600 = (50 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch050Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (2447007621 / 1000000000000 : ℝ)
  | 1 => (1247606459 / 500000000000 : ℝ)
  | 2 => (254380817 / 100000000000 : ℝ)
  | 3 => (1296397081 / 500000000000 : ℝ)
  | 4 => (528434331 / 200000000000 : ℝ)
  | 5 => (2691941391 / 1000000000000 : ℝ)
  | 6 => (274210409 / 100000000000 : ℝ)
  | 7 => (2792660447 / 1000000000000 : ℝ)
  | 8 => (2843611137 / 1000000000000 : ℝ)
  | 9 => (2894956813 / 1000000000000 : ℝ)
  | 10 => (1473349051 / 500000000000 : ℝ)
  | 11 => (2998835611 / 1000000000000 : ℝ)
  | 12 => (3051369921 / 1000000000000 : ℝ)
  | 13 => (3104301589 / 1000000000000 : ℝ)
  | 14 => (789407787 / 250000000000 : ℝ)
  | 15 => (3211359107 / 1000000000000 : ℝ)
  | 16 => (816371487 / 250000000000 : ℝ)
  | 17 => (332001213 / 100000000000 : ℝ)
  | 18 => (3374938083 / 1000000000000 : ℝ)
  | 19 => (1715132107 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch050Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (2495212919 / 1000000000000 : ℝ)
  | 1 => (2543808171 / 1000000000000 : ℝ)
  | 2 => (2592794163 / 1000000000000 : ℝ)
  | 3 => (330271457 / 125000000000 : ℝ)
  | 4 => (168246337 / 62500000000 : ℝ)
  | 5 => (2742104091 / 1000000000000 : ℝ)
  | 6 => (87270639 / 31250000000 : ℝ)
  | 7 => (1421805569 / 500000000000 : ℝ)
  | 8 => (1447478407 / 500000000000 : ℝ)
  | 9 => (2946698103 / 1000000000000 : ℝ)
  | 10 => (749708903 / 250000000000 : ℝ)
  | 11 => (1525684961 / 500000000000 : ℝ)
  | 12 => (310430159 / 100000000000 : ℝ)
  | 13 => (3157631149 / 1000000000000 : ℝ)
  | 14 => (802839777 / 250000000000 : ℝ)
  | 15 => (3265485949 / 1000000000000 : ℝ)
  | 16 => (3320012131 / 1000000000000 : ℝ)
  | 17 => (843734521 / 250000000000 : ℝ)
  | 18 => (686052843 / 200000000000 : ℝ)
  | 19 => (3485990903 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch050Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1000 : ℝ) + (j.val : ℝ)) / 1600)
      (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch050Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch050Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1000 : ℝ) + (j.val : ℝ)) / 1600)
    (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch050Neg45WeightLower j.val) (hpThetaShiftTwoBatch050Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch050Neg45WeightLower, hpThetaShiftTwoBatch050Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch050Neg45_integral_bounds :
    (636275753 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (660377331 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1000 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch050Lower hpThetaJensenCellsBatch050Upper
    hpThetaShiftTwoBatch050Neg45WeightLower hpThetaShiftTwoBatch050Neg45WeightUpper hpThetaJensenCellsBatch050_bounds hpThetaShiftTwoBatch050Neg45_weight_bounds
  have hl : (636275753 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch050Lower j * hpThetaShiftTwoBatch050Neg45WeightLower j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftTwoBatch050Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftTwoBatch050Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch050Lower j * hpThetaShiftTwoBatch050Neg45WeightUpper j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftTwoBatch050Neg45WeightUpper j) / 1600) ≤ (660377331 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftTwoBatch050Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1000 : ℝ) / 1600 = 50 / 80 by norm_num,
    show ((1000 : ℝ) + 20) / 1600 = (50 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch050Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-407846159 / 125000000000 : ℝ)
  | 1 => (-654886173 / 200000000000 : ℝ)
  | 2 => (-821505707 / 250000000000 : ℝ)
  | 3 => (-1648771981 / 500000000000 : ℝ)
  | 4 => (-165449653 / 50000000000 : ℝ)
  | 5 => (-332036891 / 100000000000 : ℝ)
  | 6 => (-333167029 / 100000000000 : ℝ)
  | 7 => (-1671447987 / 500000000000 : ℝ)
  | 8 => (-419255591 / 125000000000 : ℝ)
  | 9 => (-336511531 / 100000000000 : ℝ)
  | 10 => (-3376106473 / 1000000000000 : ℝ)
  | 11 => (-1693508481 / 500000000000 : ℝ)
  | 12 => (-679569103 / 200000000000 : ℝ)
  | 13 => (-3408590863 / 1000000000000 : ℝ)
  | 14 => (-854812933 / 250000000000 : ℝ)
  | 15 => (-1714913419 / 500000000000 : ℝ)
  | 16 => (-860078723 / 250000000000 : ℝ)
  | 17 => (-1725357299 / 500000000000 : ℝ)
  | 18 => (-3461024653 / 1000000000000 : ℝ)
  | 19 => (-1735621873 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch050Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1625519621 / 500000000000 : ℝ)
  | 1 => (-3262769271 / 1000000000000 : ℝ)
  | 2 => (-204651929 / 62500000000 : ℝ)
  | 3 => (-3286022827 / 1000000000000 : ℝ)
  | 4 => (-3297543961 / 1000000000000 : ℝ)
  | 5 => (-3308993059 / 1000000000000 : ℝ)
  | 6 => (-3320368909 / 1000000000000 : ℝ)
  | 7 => (-3331670289 / 1000000000000 : ℝ)
  | 8 => (-3342895973 / 1000000000000 : ℝ)
  | 9 => (-3354044727 / 1000000000000 : ℝ)
  | 10 => (-3365115309 / 1000000000000 : ℝ)
  | 11 => (-422013309 / 125000000000 : ℝ)
  | 12 => (-3387016961 / 1000000000000 : ℝ)
  | 13 => (-1698922757 / 500000000000 : ℝ)
  | 14 => (-1704295431 / 500000000000 : ℝ)
  | 15 => (-3419251731 / 1000000000000 : ℝ)
  | 16 => (-3429826837 / 1000000000000 : ℝ)
  | 17 => (-3440314891 / 1000000000000 : ℝ)
  | 18 => (-3450714597 / 1000000000000 : ℝ)
  | 19 => (-865256163 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch050Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1000 : ℝ) + (j.val : ℝ)) / 1600)
      (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch050Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch050Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1000 : ℝ) + (j.val : ℝ)) / 1600)
    (((1000 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch050Neg25WeightLower j.val) (hpThetaShiftTwoBatch050Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch050Neg25WeightLower, hpThetaShiftTwoBatch050Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch050Neg25_integral_bounds :
    (-375339311 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (50 / 80 : ℝ) ((50 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (-366877427 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1000 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch050Lower hpThetaJensenCellsBatch050Upper
    hpThetaShiftTwoBatch050Neg25WeightLower hpThetaShiftTwoBatch050Neg25WeightUpper hpThetaJensenCellsBatch050_bounds hpThetaShiftTwoBatch050Neg25_weight_bounds
  have hl : (-375339311 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch050Lower j * hpThetaShiftTwoBatch050Neg25WeightLower j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftTwoBatch050Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftTwoBatch050Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch050Lower j * hpThetaShiftTwoBatch050Neg25WeightUpper j)
        (hpThetaJensenCellsBatch050Upper j * hpThetaShiftTwoBatch050Neg25WeightUpper j) / 1600) ≤ (-366877427 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch050Lower, hpThetaJensenCellsBatch050Upper,
      hpThetaShiftTwoBatch050Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1000 : ℝ) / 1600 = 50 / 80 by norm_num,
    show ((1000 : ℝ) + 20) / 1600 = (50 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch050Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch050Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch050Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch050Neg25_integral_bounds
end HodgeProofHP
