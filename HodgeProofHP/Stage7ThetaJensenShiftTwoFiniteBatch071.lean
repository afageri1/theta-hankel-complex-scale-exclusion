/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch071

/-! Exact signed weight and batch integral certificates, batch 71 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch071Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1089799233273 / 250000000000 : ℝ)
  | 1 => (-1099126544293 / 250000000000 : ℝ)
  | 2 => (-277130839351 / 62500000000 : ℝ)
  | 3 => (-4471960480001 / 1000000000000 : ℝ)
  | 4 => (-1127527281933 / 250000000000 : ℝ)
  | 5 => (-1137135295523 / 250000000000 : ℝ)
  | 6 => (-4587258462281 / 1000000000000 : ℝ)
  | 7 => (-4626262797469 / 1000000000000 : ℝ)
  | 8 => (-1166389006709 / 250000000000 : ℝ)
  | 9 => (-235256999981 / 50000000000 : ℝ)
  | 10 => (-1186254143791 / 250000000000 : ℝ)
  | 11 => (-59814845287 / 12500000000 : ℝ)
  | 12 => (-2412827511349 / 500000000000 : ℝ)
  | 13 => (-608302583039 / 125000000000 : ℝ)
  | 14 => (-613435806003 / 125000000000 : ℝ)
  | 15 => (-1237213571099 / 250000000000 : ℝ)
  | 16 => (-4990526094373 / 1000000000000 : ℝ)
  | 17 => (-5032503809331 / 1000000000000 : ℝ)
  | 18 => (-5074789371127 / 1000000000000 : ℝ)
  | 19 => (-5117384732143 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch071Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2161081958793 / 500000000000 : ℝ)
  | 1 => (-4359196933091 / 1000000000000 : ℝ)
  | 2 => (-4396506177171 / 1000000000000 : ℝ)
  | 3 => (-886818685923 / 200000000000 : ℝ)
  | 4 => (-27949753 / 6250000 : ℝ)
  | 5 => (-4510109127731 / 1000000000000 : ℝ)
  | 6 => (-4548541182091 / 1000000000000 : ℝ)
  | 7 => (-114681461557 / 25000000000 : ℝ)
  | 8 => (-1156565699367 / 250000000000 : ℝ)
  | 9 => (-933111205367 / 200000000000 : ℝ)
  | 10 => (-4705139999619 / 1000000000000 : ℝ)
  | 11 => (-4745016575163 / 1000000000000 : ℝ)
  | 12 => (-4785187622959 / 1000000000000 : ℝ)
  | 13 => (-4825655022697 / 1000000000000 : ℝ)
  | 14 => (-4866420664311 / 1000000000000 : ℝ)
  | 15 => (-4907486448023 / 1000000000000 : ℝ)
  | 16 => (-989770856879 / 200000000000 : ℝ)
  | 17 => (-1247631523593 / 250000000000 : ℝ)
  | 18 => (-503250380933 / 100000000000 : ℝ)
  | 19 => (-2537394685563 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch071Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1420 : ℝ) + (j.val : ℝ)) / 1600)
      (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch071Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch071Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1420 : ℝ) + (j.val : ℝ)) / 1600)
    (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch071Neg100WeightLower j.val) (hpThetaShiftTwoBatch071Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch071Neg100WeightLower, hpThetaShiftTwoBatch071Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch071Neg100_integral_bounds :
    (-429867613 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-828125577 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch071Lower hpThetaJensenCellsBatch071Upper
    hpThetaShiftTwoBatch071Neg100WeightLower hpThetaShiftTwoBatch071Neg100WeightUpper hpThetaJensenCellsBatch071_bounds hpThetaShiftTwoBatch071Neg100_weight_bounds
  have hl : (-429867613 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch071Lower j * hpThetaShiftTwoBatch071Neg100WeightLower j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftTwoBatch071Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftTwoBatch071Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch071Lower j * hpThetaShiftTwoBatch071Neg100WeightUpper j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftTwoBatch071Neg100WeightUpper j) / 1600) ≤ (-828125577 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftTwoBatch071Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1420 : ℝ) / 1600 = 71 / 80 by norm_num,
    show ((1420 : ℝ) + 20) / 1600 = (71 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch071Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-74742978109 / 125000000000 : ℝ)
  | 1 => (-60426329011 / 100000000000 : ℝ)
  | 2 => (-610637274437 / 1000000000000 : ℝ)
  | 3 => (-617066167997 / 1000000000000 : ℝ)
  | 4 => (-155887590813 / 250000000000 : ℝ)
  | 5 => (-630090254993 / 1000000000000 : ℝ)
  | 6 => (-159171560087 / 250000000000 : ℝ)
  | 7 => (-643338718797 / 1000000000000 : ℝ)
  | 8 => (-650048092181 / 1000000000000 : ℝ)
  | 9 => (-656814764717 / 1000000000000 : ℝ)
  | 10 => (-165909785751 / 250000000000 : ℝ)
  | 11 => (-335260818019 / 500000000000 : ℝ)
  | 12 => (-338731327613 / 500000000000 : ℝ)
  | 13 => (-684462614391 / 1000000000000 : ℝ)
  | 14 => (-691521929791 / 1000000000000 : ℝ)
  | 15 => (-5589128161 / 8000000000 : ℝ)
  | 16 => (-176455076637 / 250000000000 : ℝ)
  | 17 => (-713060212681 / 1000000000000 : ℝ)
  | 18 => (-5762889317 / 8000000000 : ℝ)
  | 19 => (-727723590971 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch071Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-591678490881 / 1000000000000 : ℝ)
  | 1 => (-597943824871 / 1000000000000 : ℝ)
  | 2 => (-604263290109 / 1000000000000 : ℝ)
  | 3 => (-152659318609 / 250000000000 : ℝ)
  | 4 => (-154266541999 / 250000000000 : ℝ)
  | 5 => (-623550363251 / 1000000000000 : ℝ)
  | 6 => (-39380640937 / 62500000000 : ℝ)
  | 7 => (-636686240347 / 1000000000000 : ℝ)
  | 8 => (-160834679699 / 250000000000 : ℝ)
  | 9 => (-32502404609 / 50000000000 : ℝ)
  | 10 => (-164203691179 / 250000000000 : ℝ)
  | 11 => (-663639143003 / 1000000000000 : ℝ)
  | 12 => (-670521636037 / 1000000000000 : ℝ)
  | 13 => (-27098506209 / 40000000000 : ℝ)
  | 14 => (-68446261439 / 100000000000 : ℝ)
  | 15 => (-69152192979 / 100000000000 : ℝ)
  | 16 => (-174660255031 / 250000000000 : ℝ)
  | 17 => (-705820306547 / 1000000000000 : ℝ)
  | 18 => (-17826505317 / 25000000000 : ℝ)
  | 19 => (-45022572789 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch071Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1420 : ℝ) + (j.val : ℝ)) / 1600)
      (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch071Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch071Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1420 : ℝ) + (j.val : ℝ)) / 1600)
    (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch071Neg65WeightLower j.val) (hpThetaShiftTwoBatch071Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch071Neg65WeightLower, hpThetaShiftTwoBatch071Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch071Neg65_integral_bounds :
    (-120024587 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-57695637 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch071Lower hpThetaJensenCellsBatch071Upper
    hpThetaShiftTwoBatch071Neg65WeightLower hpThetaShiftTwoBatch071Neg65WeightUpper hpThetaJensenCellsBatch071_bounds hpThetaShiftTwoBatch071Neg65_weight_bounds
  have hl : (-120024587 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch071Lower j * hpThetaShiftTwoBatch071Neg65WeightLower j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftTwoBatch071Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftTwoBatch071Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch071Lower j * hpThetaShiftTwoBatch071Neg65WeightUpper j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftTwoBatch071Neg65WeightUpper j) / 1600) ≤ (-57695637 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftTwoBatch071Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1420 : ℝ) / 1600 = 71 / 80 by norm_num,
    show ((1420 : ℝ) + 20) / 1600 = (71 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch071Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-20563329519 / 1000000000000 : ℝ)
  | 1 => (-10673982057 / 500000000000 : ℝ)
  | 2 => (-22142771421 / 1000000000000 : ℝ)
  | 3 => (-22947841969 / 1000000000000 : ℝ)
  | 4 => (-23763266901 / 1000000000000 : ℝ)
  | 5 => (-1229456899 / 50000000000 : ℝ)
  | 6 => (-25425547591 / 1000000000000 : ℝ)
  | 7 => (-5254517749 / 200000000000 : ℝ)
  | 8 => (-27130355079 / 1000000000000 : ℝ)
  | 9 => (-5599788173 / 200000000000 : ℝ)
  | 10 => (-2887844101 / 100000000000 : ℝ)
  | 11 => (-29768951057 / 1000000000000 : ℝ)
  | 12 => (-6134113439 / 200000000000 : ℝ)
  | 13 => (-6316677251 / 200000000000 : ℝ)
  | 14 => (-812687643 / 25000000000 : ℝ)
  | 15 => (-8360755931 / 250000000000 : ℝ)
  | 16 => (-6878007811 / 200000000000 : ℝ)
  | 17 => (-17674325581 / 500000000000 : ℝ)
  | 18 => (-18159480079 / 500000000000 : ℝ)
  | 19 => (-1865053341 / 50000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch071Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-19788777719 / 1000000000000 : ℝ)
  | 1 => (-10281664759 / 500000000000 : ℝ)
  | 2 => (-21347964113 / 1000000000000 : ℝ)
  | 3 => (-1107138571 / 50000000000 : ℝ)
  | 4 => (-1434240123 / 62500000000 : ℝ)
  | 5 => (-237632669 / 10000000000 : ℝ)
  | 6 => (-24589137979 / 1000000000000 : ℝ)
  | 7 => (-2542554759 / 100000000000 : ℝ)
  | 8 => (-3284073593 / 125000000000 : ℝ)
  | 9 => (-13565177539 / 500000000000 : ℝ)
  | 10 => (-437483451 / 15625000000 : ℝ)
  | 11 => (-28878441009 / 1000000000000 : ℝ)
  | 12 => (-1860559441 / 62500000000 : ℝ)
  | 13 => (-15335283597 / 500000000000 : ℝ)
  | 14 => (-15791693127 / 500000000000 : ℝ)
  | 15 => (-32507505719 / 1000000000000 : ℝ)
  | 16 => (-33443023723 / 1000000000000 : ℝ)
  | 17 => (-17195019527 / 500000000000 : ℝ)
  | 18 => (-35348651161 / 1000000000000 : ℝ)
  | 19 => (-36318960157 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch071Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1420 : ℝ) + (j.val : ℝ)) / 1600)
      (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch071Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch071Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1420 : ℝ) + (j.val : ℝ)) / 1600)
    (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch071Neg45WeightLower j.val) (hpThetaShiftTwoBatch071Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch071Neg45WeightLower, hpThetaShiftTwoBatch071Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch071Neg45_integral_bounds :
    (-10245427 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-2410971 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch071Lower hpThetaJensenCellsBatch071Upper
    hpThetaShiftTwoBatch071Neg45WeightLower hpThetaShiftTwoBatch071Neg45WeightUpper hpThetaJensenCellsBatch071_bounds hpThetaShiftTwoBatch071Neg45_weight_bounds
  have hl : (-10245427 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch071Lower j * hpThetaShiftTwoBatch071Neg45WeightLower j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftTwoBatch071Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftTwoBatch071Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch071Lower j * hpThetaShiftTwoBatch071Neg45WeightUpper j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftTwoBatch071Neg45WeightUpper j) / 1600) ≤ (-2410971 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftTwoBatch071Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1420 : ℝ) / 1600 = 71 / 80 by norm_num,
    show ((1420 : ℝ) + 20) / 1600 = (71 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch071Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (19213288573 / 1000000000000 : ℝ)
  | 1 => (3877156261 / 200000000000 : ℝ)
  | 2 => (1955897487 / 100000000000 : ℝ)
  | 3 => (3946573571 / 200000000000 : ℝ)
  | 4 => (19907458803 / 1000000000000 : ℝ)
  | 5 => (20082746213 / 1000000000000 : ℝ)
  | 6 => (20258728537 / 1000000000000 : ℝ)
  | 7 => (4087080837 / 200000000000 : ℝ)
  | 8 => (64414911 / 3125000000 : ℝ)
  | 9 => (20790828857 / 1000000000000 : ℝ)
  | 10 => (20969574469 / 1000000000000 : ℝ)
  | 11 => (10574503289 / 500000000000 : ℝ)
  | 12 => (21329123361 / 1000000000000 : ℝ)
  | 13 => (5377480737 / 250000000000 : ℝ)
  | 14 => (21691403419 / 1000000000000 : ℝ)
  | 15 => (21873562809 / 1000000000000 : ℝ)
  | 16 => (22056399101 / 1000000000000 : ℝ)
  | 17 => (22239910231 / 1000000000000 : ℝ)
  | 18 => (4484818817 / 200000000000 : ℝ)
  | 19 => (45217897 / 2000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch071Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (9692890653 / 500000000000 : ℝ)
  | 1 => (19558974871 / 1000000000000 : ℝ)
  | 2 => (1233304241 / 62500000000 : ℝ)
  | 3 => (4976864701 / 250000000000 : ℝ)
  | 4 => (10041373107 / 500000000000 : ℝ)
  | 5 => (10129364269 / 500000000000 : ℝ)
  | 6 => (10217702093 / 500000000000 : ℝ)
  | 7 => (20612771521 / 1000000000000 : ℝ)
  | 8 => (10395414429 / 500000000000 : ℝ)
  | 9 => (2096957447 / 100000000000 : ℝ)
  | 10 => (21149006579 / 1000000000000 : ℝ)
  | 11 => (10664561681 / 500000000000 : ℝ)
  | 12 => (21509922949 / 1000000000000 : ℝ)
  | 13 => (1084570171 / 50000000000 : ℝ)
  | 14 => (2187356281 / 100000000000 : ℝ)
  | 15 => (11028199551 / 500000000000 : ℝ)
  | 16 => (2779988779 / 125000000000 : ℝ)
  | 17 => (11212047043 / 500000000000 : ℝ)
  | 18 => (22608948501 / 1000000000000 : ℝ)
  | 19 => (11397235631 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch071Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1420 : ℝ) + (j.val : ℝ)) / 1600)
      (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch071Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch071Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1420 : ℝ) + (j.val : ℝ)) / 1600)
    (((1420 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch071Neg25WeightLower j.val) (hpThetaShiftTwoBatch071Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch071Neg25WeightLower, hpThetaShiftTwoBatch071Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch071Neg25_integral_bounds :
    (461057 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (71 / 80 : ℝ) ((71 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (7659363 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1420 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch071Lower hpThetaJensenCellsBatch071Upper
    hpThetaShiftTwoBatch071Neg25WeightLower hpThetaShiftTwoBatch071Neg25WeightUpper hpThetaJensenCellsBatch071_bounds hpThetaShiftTwoBatch071Neg25_weight_bounds
  have hl : (461057 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch071Lower j * hpThetaShiftTwoBatch071Neg25WeightLower j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftTwoBatch071Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftTwoBatch071Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch071Lower j * hpThetaShiftTwoBatch071Neg25WeightUpper j)
        (hpThetaJensenCellsBatch071Upper j * hpThetaShiftTwoBatch071Neg25WeightUpper j) / 1600) ≤ (7659363 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch071Lower, hpThetaJensenCellsBatch071Upper,
      hpThetaShiftTwoBatch071Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1420 : ℝ) / 1600 = 71 / 80 by norm_num,
    show ((1420 : ℝ) + 20) / 1600 = (71 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch071Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch071Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch071Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch071Neg25_integral_bounds
end HodgeProofHP
