/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch063

/-! Exact signed weight and batch integral certificates, batch 63 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch063Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-7605382009747 / 200000000000 : ℝ)
  | 1 => (-38335096401637 / 1000000000000 : ℝ)
  | 2 => (-38645356633541 / 1000000000000 : ℝ)
  | 3 => (-19478851098761 / 500000000000 : ℝ)
  | 4 => (-4909018074679 / 125000000000 : ℝ)
  | 5 => (-39588695388079 / 1000000000000 : ℝ)
  | 6 => (-19953683087699 / 500000000000 : ℝ)
  | 7 => (-4022816861663 / 100000000000 : ℝ)
  | 8 => (-20275557210247 / 500000000000 : ℝ)
  | 9 => (-8175243069473 / 200000000000 : ℝ)
  | 10 => (-41203483209451 / 1000000000000 : ℝ)
  | 11 => (-41532929870967 / 1000000000000 : ℝ)
  | 12 => (-10466141812079 / 250000000000 : ℝ)
  | 13 => (-5274800913783 / 125000000000 : ℝ)
  | 14 => (-21267231039061 / 500000000000 : ℝ)
  | 15 => (-21436371812959 / 500000000000 : ℝ)
  | 16 => (-5401658010073 / 125000000000 : ℝ)
  | 17 => (-4355603562213 / 100000000000 : ℝ)
  | 18 => (-21950535241913 / 500000000000 : ℝ)
  | 19 => (-44248380952381 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch063Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-37720786172367 / 1000000000000 : ℝ)
  | 1 => (-19013455024367 / 500000000000 : ℝ)
  | 2 => (-9583774100409 / 250000000000 : ℝ)
  | 3 => (-1932267831677 / 50000000000 : ℝ)
  | 4 => (-38957702197521 / 1000000000000 : ℝ)
  | 5 => (-39272144597431 / 1000000000000 : ℝ)
  | 6 => (-19794347694039 / 500000000000 : ℝ)
  | 7 => (-39907366175397 / 1000000000000 : ℝ)
  | 8 => (-40228168616629 / 1000000000000 : ℝ)
  | 9 => (-40551114420493 / 1000000000000 : ℝ)
  | 10 => (-10219053836841 / 250000000000 : ℝ)
  | 11 => (-824069664189 / 20000000000 : ℝ)
  | 12 => (-20766464935483 / 500000000000 : ℝ)
  | 13 => (-8372913449663 / 200000000000 : ℝ)
  | 14 => (-42198407310263 / 1000000000000 : ℝ)
  | 15 => (-42534462078121 / 1000000000000 : ℝ)
  | 16 => (-42872743625917 / 1000000000000 : ℝ)
  | 17 => (-43213264080583 / 1000000000000 : ℝ)
  | 18 => (-43556035622129 / 1000000000000 : ℝ)
  | 19 => (-1756042819353 / 40000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch063Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1260 : ℝ) + (j.val : ℝ)) / 1600)
      (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch063Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch063Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1260 : ℝ) + (j.val : ℝ)) / 1600)
    (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch063Neg100WeightLower j.val) (hpThetaShiftOneBatch063Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch063Neg100WeightLower, hpThetaShiftOneBatch063Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch063Neg100_integral_bounds :
    (-279566240781 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-270553420787 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch063Lower hpThetaJensenCellsBatch063Upper
    hpThetaShiftOneBatch063Neg100WeightLower hpThetaShiftOneBatch063Neg100WeightUpper hpThetaJensenCellsBatch063_bounds hpThetaShiftOneBatch063Neg100_weight_bounds
  have hl : (-279566240781 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch063Lower j * hpThetaShiftOneBatch063Neg100WeightLower j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftOneBatch063Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftOneBatch063Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch063Lower j * hpThetaShiftOneBatch063Neg100WeightUpper j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftOneBatch063Neg100WeightUpper j) / 1600) ≤ (-270553420787 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftOneBatch063Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1260 : ℝ) / 1600 = 63 / 80 by norm_num,
    show ((1260 : ℝ) + 20) / 1600 = (63 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch063Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-31119260061 / 6250000000 : ℝ)
  | 1 => (-5032620572139 / 1000000000000 : ℝ)
  | 2 => (-2543294239977 / 500000000000 : ℝ)
  | 3 => (-5140987989797 / 1000000000000 : ℝ)
  | 4 => (-1298955442743 / 250000000000 : ℝ)
  | 5 => (-5251092505547 / 1000000000000 : ℝ)
  | 6 => (-5306802888393 / 1000000000000 : ℝ)
  | 7 => (-1340738906809 / 250000000000 : ℝ)
  | 8 => (-2709776721349 / 500000000000 : ℝ)
  | 9 => (-5476599068347 / 1000000000000 : ℝ)
  | 10 => (-5534095250743 / 1000000000000 : ℝ)
  | 11 => (-1398011187371 / 250000000000 : ℝ)
  | 12 => (-22601801349 / 4000000000 : ℝ)
  | 13 => (-1141862959971 / 200000000000 : ℝ)
  | 14 => (-576864093629 / 100000000000 : ℝ)
  | 15 => (-5828431558773 / 1000000000000 : ℝ)
  | 16 => (-5888689492793 / 1000000000000 : ℝ)
  | 17 => (-2974708788579 / 500000000000 : ℝ)
  | 18 => (-3005309332023 / 500000000000 : ℝ)
  | 19 => (-759036952381 / 125000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch063Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4925968948893 / 1000000000000 : ℝ)
  | 1 => (-4979081609759 / 1000000000000 : ℝ)
  | 2 => (-2516310286069 / 500000000000 : ℝ)
  | 3 => (-5086588479953 / 1000000000000 : ℝ)
  | 4 => (-1285246997449 / 250000000000 : ℝ)
  | 5 => (-5195821770971 / 1000000000000 : ℝ)
  | 6 => (-2625546252773 / 500000000000 : ℝ)
  | 7 => (-663350361049 / 125000000000 : ℝ)
  | 8 => (-1072591125447 / 200000000000 : ℝ)
  | 9 => (-5419553442697 / 1000000000000 : ℝ)
  | 10 => (-2738299534173 / 500000000000 : ℝ)
  | 11 => (-2767047625371 / 500000000000 : ℝ)
  | 12 => (-5592044749483 / 1000000000000 : ℝ)
  | 13 => (-5650450337249 / 1000000000000 : ℝ)
  | 14 => (-2854657399927 / 500000000000 : ℝ)
  | 15 => (-5768640936289 / 1000000000000 : ℝ)
  | 16 => (-1457107889693 / 250000000000 : ℝ)
  | 17 => (-736086186599 / 125000000000 : ℝ)
  | 18 => (-5949417577157 / 1000000000000 : ℝ)
  | 19 => (-1202123732809 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch063Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1260 : ℝ) + (j.val : ℝ)) / 1600)
      (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch063Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch063Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1260 : ℝ) + (j.val : ℝ)) / 1600)
    (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch063Neg65WeightLower j.val) (hpThetaShiftOneBatch063Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch063Neg65WeightLower, hpThetaShiftOneBatch063Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch063Neg65_integral_bounds :
    (-37470811517 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-7234563297 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch063Lower hpThetaJensenCellsBatch063Upper
    hpThetaShiftOneBatch063Neg65WeightLower hpThetaShiftOneBatch063Neg65WeightUpper hpThetaJensenCellsBatch063_bounds hpThetaShiftOneBatch063Neg65_weight_bounds
  have hl : (-37470811517 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch063Lower j * hpThetaShiftOneBatch063Neg65WeightLower j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftOneBatch063Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftOneBatch063Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch063Lower j * hpThetaShiftOneBatch063Neg65WeightUpper j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftOneBatch063Neg65WeightUpper j) / 1600) ≤ (-7234563297 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftOneBatch063Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1260 : ℝ) / 1600 = 63 / 80 by norm_num,
    show ((1260 : ℝ) + 20) / 1600 = (63 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch063Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (73525162361 / 200000000000 : ℝ)
  | 1 => (73098269869 / 200000000000 : ℝ)
  | 2 => (45413610437 / 125000000000 : ℝ)
  | 3 => (180538993931 / 500000000000 : ℝ)
  | 4 => (71759646717 / 200000000000 : ℝ)
  | 5 => (178234594669 / 500000000000 : ℝ)
  | 6 => (354090421317 / 1000000000000 : ℝ)
  | 7 => (87915373307 / 250000000000 : ℝ)
  | 8 => (174590983139 / 500000000000 : ℝ)
  | 9 => (173325699583 / 500000000000 : ℝ)
  | 10 => (43008668509 / 125000000000 : ℝ)
  | 11 => (42679420831 / 125000000000 : ℝ)
  | 12 => (169374503003 / 500000000000 : ℝ)
  | 13 => (336009814709 / 1000000000000 : ℝ)
  | 14 => (166608669381 / 500000000000 : ℝ)
  | 15 => (330371121601 / 1000000000000 : ℝ)
  | 16 => (327470704083 / 1000000000000 : ℝ)
  | 17 => (12980624979 / 40000000000 : ℝ)
  | 18 => (80376354611 / 250000000000 : ℝ)
  | 19 => (318439619047 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch063Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (184856347413 / 500000000000 : ℝ)
  | 1 => (183812905903 / 500000000000 : ℝ)
  | 2 => (182745674673 / 500000000000 : ℝ)
  | 3 => (363308883497 / 1000000000000 : ℝ)
  | 4 => (361077987863 / 1000000000000 : ℝ)
  | 5 => (179399116793 / 500000000000 : ℝ)
  | 6 => (356469189339 / 1000000000000 : ℝ)
  | 7 => (177045210659 / 500000000000 : ℝ)
  | 8 => (351661493229 / 1000000000000 : ℝ)
  | 9 => (349181966279 / 1000000000000 : ℝ)
  | 10 => (346651399167 / 1000000000000 : ℝ)
  | 11 => (344069348073 / 1000000000000 : ℝ)
  | 12 => (341435366649 / 1000000000000 : ℝ)
  | 13 => (338749006007 / 1000000000000 : ℝ)
  | 14 => (33600981471 / 100000000000 : ℝ)
  | 15 => (333217338763 / 1000000000000 : ℝ)
  | 16 => (165185560801 / 500000000000 : ℝ)
  | 17 => (81867676021 / 250000000000 : ℝ)
  | 18 => (81128906119 / 250000000000 : ℝ)
  | 19 => (64301083689 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch063Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1260 : ℝ) + (j.val : ℝ)) / 1600)
      (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch063Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch063Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1260 : ℝ) + (j.val : ℝ)) / 1600)
    (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch063Neg40WeightLower j.val) (hpThetaShiftOneBatch063Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch063Neg40WeightLower, hpThetaShiftOneBatch063Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch063Neg40_integral_bounds :
    (2306527567 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (595429453 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch063Lower hpThetaJensenCellsBatch063Upper
    hpThetaShiftOneBatch063Neg40WeightLower hpThetaShiftOneBatch063Neg40WeightUpper hpThetaJensenCellsBatch063_bounds hpThetaShiftOneBatch063Neg40_weight_bounds
  have hl : (2306527567 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch063Lower j * hpThetaShiftOneBatch063Neg40WeightLower j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftOneBatch063Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftOneBatch063Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch063Lower j * hpThetaShiftOneBatch063Neg40WeightUpper j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftOneBatch063Neg40WeightUpper j) / 1600) ≤ (595429453 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftOneBatch063Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1260 : ℝ) / 1600 = 63 / 80 by norm_num,
    show ((1260 : ℝ) + 20) / 1600 = (63 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch063Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (13569391349 / 200000000000 : ℝ)
  | 1 => (34561513657 / 500000000000 : ℝ)
  | 2 => (8800647523 / 125000000000 : ℝ)
  | 3 => (560104819 / 7812500000 : ℝ)
  | 4 => (72987738587 / 1000000000000 : ℝ)
  | 5 => (74288146627 / 1000000000000 : ℝ)
  | 6 => (3779732099 / 50000000000 : ℝ)
  | 7 => (76907225519 / 1000000000000 : ℝ)
  | 8 => (78225897969 / 1000000000000 : ℝ)
  | 9 => (79550659897 / 1000000000000 : ℝ)
  | 10 => (40440755859 / 500000000000 : ℝ)
  | 11 => (82218453689 / 1000000000000 : ℝ)
  | 12 => (10445185739 / 125000000000 : ℝ)
  | 13 => (8491060833 / 100000000000 : ℝ)
  | 14 => (86265820727 / 1000000000000 : ℝ)
  | 15 => (8762712273 / 100000000000 : ℝ)
  | 16 => (88994513801 / 1000000000000 : ℝ)
  | 17 => (22591998311 / 250000000000 : ℝ)
  | 18 => (45873780099 / 500000000000 : ℝ)
  | 19 => (2328330341 / 25000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch063Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (13824605463 / 200000000000 : ℝ)
  | 1 => (14081036037 / 200000000000 : ℝ)
  | 2 => (71693416833 / 1000000000000 : ℝ)
  | 3 => (18246934647 / 250000000000 : ℝ)
  | 4 => (18572036657 / 250000000000 : ℝ)
  | 5 => (75594641981 / 1000000000000 : ℝ)
  | 6 => (961340319 / 12500000000 : ℝ)
  | 7 => (7822589797 / 100000000000 : ℝ)
  | 8 => (39775329949 / 500000000000 : ℝ)
  | 9 => (80881511719 / 1000000000000 : ℝ)
  | 10 => (8221845369 / 100000000000 : ℝ)
  | 11 => (83561485913 / 1000000000000 : ℝ)
  | 12 => (84910608331 / 1000000000000 : ℝ)
  | 13 => (10783227591 / 125000000000 : ℝ)
  | 14 => (87627122731 / 1000000000000 : ℝ)
  | 15 => (44497256901 / 500000000000 : ℝ)
  | 16 => (18073598649 / 200000000000 : ℝ)
  | 17 => (91747560199 / 1000000000000 : ℝ)
  | 18 => (93133213641 / 1000000000000 : ℝ)
  | 19 => (94524952381 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch063Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1260 : ℝ) + (j.val : ℝ)) / 1600)
      (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch063Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch063Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1260 : ℝ) + (j.val : ℝ)) / 1600)
    (((1260 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch063Neg20WeightLower j.val) (hpThetaShiftOneBatch063Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch063Neg20WeightLower, hpThetaShiftOneBatch063Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch063Neg20_integral_bounds :
    (530775163 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (63 / 80 : ℝ) ((63 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (110638939 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1260 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch063Lower hpThetaJensenCellsBatch063Upper
    hpThetaShiftOneBatch063Neg20WeightLower hpThetaShiftOneBatch063Neg20WeightUpper hpThetaJensenCellsBatch063_bounds hpThetaShiftOneBatch063Neg20_weight_bounds
  have hl : (530775163 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch063Lower j * hpThetaShiftOneBatch063Neg20WeightLower j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftOneBatch063Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftOneBatch063Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch063Lower j * hpThetaShiftOneBatch063Neg20WeightUpper j)
        (hpThetaJensenCellsBatch063Upper j * hpThetaShiftOneBatch063Neg20WeightUpper j) / 1600) ≤ (110638939 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch063Lower, hpThetaJensenCellsBatch063Upper,
      hpThetaShiftOneBatch063Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1260 : ℝ) / 1600 = 63 / 80 by norm_num,
    show ((1260 : ℝ) + 20) / 1600 = (63 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch063Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch063Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch063Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch063Neg20_integral_bounds
end HodgeProofHP
