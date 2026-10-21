/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch042

/-! Exact signed weight and batch integral certificates, batch 42 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch042Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (8486430587 / 250000000000 : ℝ)
  | 1 => (119118699 / 4000000000 : ℝ)
  | 2 => (12764847549 / 500000000000 : ℝ)
  | 3 => (165584367 / 7812500000 : ℝ)
  | 4 => (4193498483 / 250000000000 : ℝ)
  | 5 => (12266279429 / 1000000000000 : ℝ)
  | 6 => (7670646799 / 1000000000000 : ℝ)
  | 7 => (373259899 / 125000000000 : ℝ)
  | 8 => (-111778029 / 62500000000 : ℝ)
  | 9 => (-3326984759 / 500000000000 : ℝ)
  | 10 => (-11611525641 / 1000000000000 : ℝ)
  | 11 => (-1666216687 / 100000000000 : ℝ)
  | 12 => (-1362934479 / 62500000000 : ℝ)
  | 13 => (-13523473473 / 500000000000 : ℝ)
  | 14 => (-6476645631 / 200000000000 : ℝ)
  | 15 => (-9454219823 / 250000000000 : ℝ)
  | 16 => (-10837248243 / 250000000000 : ℝ)
  | 17 => (-48980670471 / 1000000000000 : ℝ)
  | 18 => (-2188520871 / 40000000000 : ℝ)
  | 19 => (-60547165633 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch042Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (9507203579 / 250000000000 : ℝ)
  | 1 => (33945722349 / 1000000000000 : ℝ)
  | 2 => (29779674751 / 1000000000000 : ℝ)
  | 3 => (25529695099 / 1000000000000 : ℝ)
  | 4 => (21194798977 / 1000000000000 : ℝ)
  | 5 => (16773993933 / 1000000000000 : ℝ)
  | 6 => (1226627943 / 100000000000 : ℝ)
  | 7 => (19176617 / 2500000000 : ℝ)
  | 8 => (2986079193 / 1000000000000 : ℝ)
  | 9 => (-1788448463 / 1000000000000 : ℝ)
  | 10 => (-6653969517 / 1000000000000 : ℝ)
  | 11 => (-290288141 / 25000000000 : ℝ)
  | 12 => (-16662166869 / 1000000000000 : ℝ)
  | 13 => (-21806951663 / 1000000000000 : ℝ)
  | 14 => (-5409389389 / 200000000000 : ℝ)
  | 15 => (-16191614077 / 500000000000 : ℝ)
  | 16 => (-37816879291 / 1000000000000 : ℝ)
  | 17 => (-43348992971 / 1000000000000 : ℝ)
  | 18 => (-4898067047 / 100000000000 : ℝ)
  | 19 => (-27356510887 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch042Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((840 : ℝ) + (j.val : ℝ)) / 1600)
      (((840 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch042Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch042Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((840 : ℝ) + (j.val : ℝ)) / 1600)
    (((840 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch042Neg100WeightLower j.val) (hpThetaShiftOneBatch042Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch042Neg100WeightLower, hpThetaShiftOneBatch042Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch042Neg100_integral_bounds :
    (-9666240453 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-2125295397 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (840 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch042Lower hpThetaJensenCellsBatch042Upper
    hpThetaShiftOneBatch042Neg100WeightLower hpThetaShiftOneBatch042Neg100WeightUpper hpThetaJensenCellsBatch042_bounds hpThetaShiftOneBatch042Neg100_weight_bounds
  have hl : (-9666240453 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch042Lower j * hpThetaShiftOneBatch042Neg100WeightLower j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftOneBatch042Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftOneBatch042Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch042Lower j * hpThetaShiftOneBatch042Neg100WeightUpper j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftOneBatch042Neg100WeightUpper j) / 1600) ≤ (-2125295397 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftOneBatch042Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (840 : ℝ) / 1600 = 42 / 80 by norm_num,
    show ((840 : ℝ) + 20) / 1600 = (42 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch042Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (21446868741 / 125000000000 : ℝ)
  | 1 => (172836533399 / 1000000000000 : ℝ)
  | 2 => (87048267039 / 500000000000 : ℝ)
  | 3 => (175354812457 / 1000000000000 : ℝ)
  | 4 => (88305613683 / 500000000000 : ℝ)
  | 5 => (35573127191 / 200000000000 : ℝ)
  | 6 => (35823578737 / 200000000000 : ℝ)
  | 7 => (36073570863 / 200000000000 : ℝ)
  | 8 => (45403842473 / 250000000000 : ℝ)
  | 9 => (182860290739 / 1000000000000 : ℝ)
  | 10 => (92051232721 / 500000000000 : ℝ)
  | 11 => (185341740839 / 1000000000000 : ℝ)
  | 12 => (18657796201 / 100000000000 : ℝ)
  | 13 => (9390548613 / 50000000000 : ℝ)
  | 14 => (94520306557 / 500000000000 : ℝ)
  | 15 => (190266724299 / 1000000000000 : ℝ)
  | 16 => (23936142967 / 125000000000 : ℝ)
  | 17 => (7708308301 / 40000000000 : ℝ)
  | 18 => (96961124967 / 500000000000 : ℝ)
  | 19 => (19513260339 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch042Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (864182667 / 5000000000 : ℝ)
  | 1 => (174096534079 / 1000000000000 : ℝ)
  | 2 => (87677406229 / 500000000000 : ℝ)
  | 3 => (176611227367 / 1000000000000 : ℝ)
  | 4 => (44466408989 / 250000000000 : ℝ)
  | 5 => (89558946843 / 500000000000 : ℝ)
  | 6 => (45091963579 / 250000000000 : ℝ)
  | 7 => (181615369893 / 1000000000000 : ℝ)
  | 8 => (9143014537 / 50000000000 : ℝ)
  | 9 => (184102465443 / 1000000000000 : ℝ)
  | 10 => (4633543521 / 25000000000 : ℝ)
  | 11 => (186577962011 / 1000000000000 : ℝ)
  | 12 => (187810972261 / 1000000000000 : ℝ)
  | 13 => (37808122623 / 200000000000 : ℝ)
  | 14 => (1902667243 / 10000000000 : ℝ)
  | 15 => (191489143737 / 1000000000000 : ℝ)
  | 16 => (96353853763 / 500000000000 : ℝ)
  | 17 => (38784449987 / 200000000000 : ℝ)
  | 18 => (195132603391 / 1000000000000 : ℝ)
  | 19 => (196338598461 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch042Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((840 : ℝ) + (j.val : ℝ)) / 1600)
      (((840 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch042Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch042Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((840 : ℝ) + (j.val : ℝ)) / 1600)
    (((840 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch042Neg65WeightLower j.val) (hpThetaShiftOneBatch042Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch042Neg65WeightLower, hpThetaShiftOneBatch042Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch042Neg65_integral_bounds :
    (184583579547 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (94514691119 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (840 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch042Lower hpThetaJensenCellsBatch042Upper
    hpThetaShiftOneBatch042Neg65WeightLower hpThetaShiftOneBatch042Neg65WeightUpper hpThetaJensenCellsBatch042_bounds hpThetaShiftOneBatch042Neg65_weight_bounds
  have hl : (184583579547 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch042Lower j * hpThetaShiftOneBatch042Neg65WeightLower j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftOneBatch042Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftOneBatch042Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch042Lower j * hpThetaShiftOneBatch042Neg65WeightUpper j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftOneBatch042Neg65WeightUpper j) / 1600) ≤ (94514691119 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftOneBatch042Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (840 : ℝ) / 1600 = 42 / 80 by norm_num,
    show ((840 : ℝ) + 20) / 1600 = (42 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch042Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-41785719 / 10000000000 : ℝ)
  | 1 => (-1788268123 / 500000000000 : ℝ)
  | 2 => (-1484427221 / 500000000000 : ℝ)
  | 3 => (-94220503 / 40000000000 : ℝ)
  | 4 => (-434124227 / 250000000000 : ℝ)
  | 5 => (-222358777 / 200000000000 : ℝ)
  | 6 => (-481390129 / 1000000000000 : ℝ)
  | 7 => (1208809 / 7812500000 : ℝ)
  | 8 => (199143041 / 250000000000 : ℝ)
  | 9 => (1444156527 / 1000000000000 : ℝ)
  | 10 => (2097493269 / 1000000000000 : ℝ)
  | 11 => (2756594827 / 1000000000000 : ℝ)
  | 12 => (3421473443 / 1000000000000 : ℝ)
  | 13 => (1023035291 / 250000000000 : ℝ)
  | 14 => (4768609837 / 1000000000000 : ℝ)
  | 15 => (5450891107 / 1000000000000 : ℝ)
  | 16 => (3069498209 / 500000000000 : ℝ)
  | 17 => (6832937007 / 1000000000000 : ℝ)
  | 18 => (7532723903 / 1000000000000 : ℝ)
  | 19 => (4119183963 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch042Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-715307249 / 200000000000 : ℝ)
  | 1 => (-2968854441 / 1000000000000 : ℝ)
  | 2 => (-1177756287 / 500000000000 : ℝ)
  | 3 => (-1736496907 / 1000000000000 : ℝ)
  | 4 => (-277948471 / 250000000000 : ℝ)
  | 5 => (-30086883 / 62500000000 : ℝ)
  | 6 => (154727553 / 1000000000000 : ℝ)
  | 7 => (159314433 / 200000000000 : ℝ)
  | 8 => (90259783 / 62500000000 : ℝ)
  | 9 => (209749327 / 100000000000 : ℝ)
  | 10 => (689148707 / 250000000000 : ℝ)
  | 11 => (855368361 / 250000000000 : ℝ)
  | 12 => (818428233 / 200000000000 : ℝ)
  | 13 => (2384304919 / 500000000000 : ℝ)
  | 14 => (1362722777 / 250000000000 : ℝ)
  | 15 => (6138996419 / 1000000000000 : ℝ)
  | 16 => (427058563 / 62500000000 : ℝ)
  | 17 => (117698811 / 15625000000 : ℝ)
  | 18 => (8238367927 / 1000000000000 : ℝ)
  | 19 => (1789975937 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch042Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((840 : ℝ) + (j.val : ℝ)) / 1600)
      (((840 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch042Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch042Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((840 : ℝ) + (j.val : ℝ)) / 1600)
    (((840 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch042Neg40WeightLower j.val) (hpThetaShiftOneBatch042Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch042Neg40WeightLower, hpThetaShiftOneBatch042Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch042Neg40_integral_bounds :
    (336826853 / 200000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (1205731789 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (840 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch042Lower hpThetaJensenCellsBatch042Upper
    hpThetaShiftOneBatch042Neg40WeightLower hpThetaShiftOneBatch042Neg40WeightUpper hpThetaJensenCellsBatch042_bounds hpThetaShiftOneBatch042Neg40_weight_bounds
  have hl : (336826853 / 200000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch042Lower j * hpThetaShiftOneBatch042Neg40WeightLower j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftOneBatch042Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftOneBatch042Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch042Lower j * hpThetaShiftOneBatch042Neg40WeightUpper j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftOneBatch042Neg40WeightUpper j) / 1600) ≤ (1205731789 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftOneBatch042Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (840 : ℝ) / 1600 = 42 / 80 by norm_num,
    show ((840 : ℝ) + 20) / 1600 = (42 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch042Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-60372120461 / 1000000000000 : ℝ)
  | 1 => (-1894308997 / 31250000000 : ℝ)
  | 2 => (-30431490123 / 500000000000 : ℝ)
  | 3 => (-61107385951 / 1000000000000 : ℝ)
  | 4 => (-30675546723 / 500000000000 : ℝ)
  | 5 => (-30797045559 / 500000000000 : ℝ)
  | 6 => (-3864772957 / 62500000000 : ℝ)
  | 7 => (-12415582067 / 200000000000 : ℝ)
  | 8 => (-31159354227 / 500000000000 : ℝ)
  | 9 => (-12511749979 / 200000000000 : ℝ)
  | 10 => (-31399011423 / 500000000000 : ℝ)
  | 11 => (-492472777 / 7812500000 : ℝ)
  | 12 => (-7909276979 / 125000000000 : ℝ)
  | 13 => (-63511112043 / 1000000000000 : ℝ)
  | 14 => (-1593679803 / 25000000000 : ℝ)
  | 15 => (-31991222027 / 500000000000 : ℝ)
  | 16 => (-16054213949 / 250000000000 : ℝ)
  | 17 => (-64450415259 / 1000000000000 : ℝ)
  | 18 => (-64683110319 / 1000000000000 : ℝ)
  | 19 => (-64914928809 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch042Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-60125689407 / 1000000000000 : ℝ)
  | 1 => (-3018606023 / 50000000000 : ℝ)
  | 2 => (-60617887903 / 1000000000000 : ℝ)
  | 3 => (-12172596049 / 200000000000 : ℝ)
  | 4 => (-1222147719 / 20000000000 : ℝ)
  | 5 => (-12270218689 / 200000000000 : ℝ)
  | 6 => (-61594091117 / 1000000000000 : ℝ)
  | 7 => (-61836367311 / 1000000000000 : ℝ)
  | 8 => (-31038955167 / 500000000000 : ℝ)
  | 9 => (-62318708453 / 1000000000000 : ℝ)
  | 10 => (-31279374947 / 500000000000 : ℝ)
  | 11 => (-12559604569 / 200000000000 : ℝ)
  | 12 => (-12607303091 / 200000000000 : ℝ)
  | 13 => (-63274215831 / 1000000000000 : ℝ)
  | 14 => (-31755556021 / 500000000000 : ℝ)
  | 15 => (-63747192119 / 1000000000000 : ℝ)
  | 16 => (-63982444053 / 1000000000000 : ℝ)
  | 17 => (-12843371159 / 200000000000 : ℝ)
  | 18 => (-32225207629 / 500000000000 : ℝ)
  | 19 => (-32341555159 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch042Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((840 : ℝ) + (j.val : ℝ)) / 1600)
      (((840 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch042Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch042Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((840 : ℝ) + (j.val : ℝ)) / 1600)
    (((840 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch042Neg20WeightLower j.val) (hpThetaShiftOneBatch042Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch042Neg20WeightLower, hpThetaShiftOneBatch042Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch042Neg20_integral_bounds :
    (-4012190909 / 62500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (42 / 80 : ℝ) ((42 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-3929243321 / 62500000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (840 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch042Lower hpThetaJensenCellsBatch042Upper
    hpThetaShiftOneBatch042Neg20WeightLower hpThetaShiftOneBatch042Neg20WeightUpper hpThetaJensenCellsBatch042_bounds hpThetaShiftOneBatch042Neg20_weight_bounds
  have hl : (-4012190909 / 62500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch042Lower j * hpThetaShiftOneBatch042Neg20WeightLower j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftOneBatch042Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftOneBatch042Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch042Lower j * hpThetaShiftOneBatch042Neg20WeightUpper j)
        (hpThetaJensenCellsBatch042Upper j * hpThetaShiftOneBatch042Neg20WeightUpper j) / 1600) ≤ (-3929243321 / 62500000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch042Lower, hpThetaJensenCellsBatch042Upper,
      hpThetaShiftOneBatch042Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (840 : ℝ) / 1600 = 42 / 80 by norm_num,
    show ((840 : ℝ) + 20) / 1600 = (42 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch042Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch042Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch042Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch042Neg20_integral_bounds
end HodgeProofHP
