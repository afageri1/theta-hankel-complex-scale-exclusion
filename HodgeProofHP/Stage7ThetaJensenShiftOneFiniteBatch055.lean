/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch055

/-! Exact signed weight and batch integral certificates, batch 55 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch055Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8750715613887 / 1000000000000 : ℝ)
  | 1 => (-2210957856157 / 250000000000 : ℝ)
  | 2 => (-4468866570513 / 500000000000 : ℝ)
  | 3 => (-2258106513221 / 250000000000 : ℝ)
  | 4 => (-2281978869509 / 250000000000 : ℝ)
  | 5 => (-4612103381227 / 500000000000 : ℝ)
  | 6 => (-1864261056073 / 200000000000 : ℝ)
  | 7 => (-4709608217183 / 500000000000 : ℝ)
  | 8 => (-9517945655533 / 1000000000000 : ℝ)
  | 9 => (-9617498403543 / 1000000000000 : ℝ)
  | 10 => (-9717880166783 / 1000000000000 : ℝ)
  | 11 => (-2454774115617 / 250000000000 : ℝ)
  | 12 => (-1984230567351 / 200000000000 : ℝ)
  | 13 => (-10024054864861 / 1000000000000 : ℝ)
  | 14 => (-5063904075589 / 500000000000 : ℝ)
  | 15 => (-639526145587 / 62500000000 : ℝ)
  | 16 => (-2067578212519 / 200000000000 : ℝ)
  | 17 => (-5222116021703 / 500000000000 : ℝ)
  | 18 => (-1318930874261 / 125000000000 : ℝ)
  | 19 => (-10659541666667 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch055Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-8658380446911 / 1000000000000 : ℝ)
  | 1 => (-4375357806943 / 500000000000 : ℝ)
  | 2 => (-8843831424627 / 1000000000000 : ℝ)
  | 3 => (-357509325641 / 40000000000 : ℝ)
  | 4 => (-9032426052883 / 1000000000000 : ℝ)
  | 5 => (-1825583095607 / 200000000000 : ℝ)
  | 6 => (-9224206762453 / 1000000000000 : ℝ)
  | 7 => (-2330326320091 / 250000000000 : ℝ)
  | 8 => (-1883843286873 / 200000000000 : ℝ)
  | 9 => (-2379486413883 / 250000000000 : ℝ)
  | 10 => (-4808749201771 / 500000000000 : ℝ)
  | 11 => (-4858940083391 / 500000000000 : ℝ)
  | 12 => (-9819096462467 / 1000000000000 : ℝ)
  | 13 => (-4960576418377 / 500000000000 : ℝ)
  | 14 => (-501202743243 / 50000000000 : ℝ)
  | 15 => (-10127808151177 / 1000000000000 : ℝ)
  | 16 => (-10232418329391 / 1000000000000 : ℝ)
  | 17 => (-5168945531297 / 500000000000 : ℝ)
  | 18 => (-2088846408681 / 200000000000 : ℝ)
  | 19 => (-10551446994087 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch055Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1100 : ℝ) + (j.val : ℝ)) / 1600)
      (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch055Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch055Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1100 : ℝ) + (j.val : ℝ)) / 1600)
    (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch055Neg100WeightLower j.val) (hpThetaShiftOneBatch055Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch055Neg100WeightLower, hpThetaShiftOneBatch055Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch055Neg100_integral_bounds :
    (-662448273987 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-641752105353 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch055Lower hpThetaJensenCellsBatch055Upper
    hpThetaShiftOneBatch055Neg100WeightLower hpThetaShiftOneBatch055Neg100WeightUpper hpThetaJensenCellsBatch055_bounds hpThetaShiftOneBatch055Neg100_weight_bounds
  have hl : (-662448273987 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch055Lower j * hpThetaShiftOneBatch055Neg100WeightLower j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftOneBatch055Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftOneBatch055Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch055Lower j * hpThetaShiftOneBatch055Neg100WeightUpper j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftOneBatch055Neg100WeightUpper j) / 1600) ≤ (-641752105353 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftOneBatch055Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1100 : ℝ) / 1600 = 55 / 80 by norm_num,
    show ((1100 : ℝ) + 20) / 1600 = (55 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch055Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-82115036723 / 200000000000 : ℝ)
  | 1 => (-16882066579 / 40000000000 : ℝ)
  | 2 => (-216833534087 / 500000000000 : ℝ)
  | 3 => (-445422530967 / 1000000000000 : ℝ)
  | 4 => (-45731919587 / 100000000000 : ℝ)
  | 5 => (-469358212699 / 1000000000000 : ℝ)
  | 6 => (-481540738091 / 1000000000000 : ℝ)
  | 7 => (-246933967771 / 500000000000 : ℝ)
  | 8 => (-126585243857 / 250000000000 : ℝ)
  | 9 => (-518961035043 / 1000000000000 : ℝ)
  | 10 => (-265864649311 / 500000000000 : ℝ)
  | 11 => (-272323478687 / 500000000000 : ℝ)
  | 12 => (-557715209513 / 1000000000000 : ℝ)
  | 13 => (-285467630143 / 500000000000 : ℝ)
  | 14 => (-146077080501 / 250000000000 : ℝ)
  | 15 => (-597835614073 / 1000000000000 : ℝ)
  | 16 => (-305759181511 / 500000000000 : ℝ)
  | 17 => (-78169725317 / 125000000000 : ℝ)
  | 18 => (-319677586743 / 500000000000 : ℝ)
  | 19 => (-653511723959 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch055Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-399236496081 / 1000000000000 : ℝ)
  | 1 => (-205287591807 / 500000000000 : ℝ)
  | 2 => (-211025832237 / 500000000000 : ℝ)
  | 3 => (-433667068173 / 1000000000000 : ℝ)
  | 4 => (-222711265483 / 500000000000 : ℝ)
  | 5 => (-457319195869 / 1000000000000 : ℝ)
  | 6 => (-234679106349 / 500000000000 : ℝ)
  | 7 => (-48154073809 / 100000000000 : ℝ)
  | 8 => (-493867935541 / 1000000000000 : ℝ)
  | 9 => (-506340975427 / 1000000000000 : ℝ)
  | 10 => (-259480517521 / 500000000000 : ℝ)
  | 11 => (-531729298621 / 1000000000000 : ℝ)
  | 12 => (-544646957373 / 1000000000000 : ℝ)
  | 13 => (-69714401189 / 125000000000 : ℝ)
  | 14 => (-114187052057 / 200000000000 : ℝ)
  | 15 => (-584308322003 / 1000000000000 : ℝ)
  | 16 => (-74729451759 / 125000000000 : ℝ)
  | 17 => (-611518363021 / 1000000000000 : ℝ)
  | 18 => (-125071560507 / 200000000000 : ℝ)
  | 19 => (-127871034697 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch055Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1100 : ℝ) + (j.val : ℝ)) / 1600)
      (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch055Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch055Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1100 : ℝ) + (j.val : ℝ)) / 1600)
    (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch055Neg65WeightLower j.val) (hpThetaShiftOneBatch055Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch055Neg65WeightLower, hpThetaShiftOneBatch055Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch055Neg65_integral_bounds :
    (-17951278979 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-34293017999 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch055Lower hpThetaJensenCellsBatch055Upper
    hpThetaShiftOneBatch055Neg65WeightLower hpThetaShiftOneBatch055Neg65WeightUpper hpThetaJensenCellsBatch055_bounds hpThetaShiftOneBatch055Neg65_weight_bounds
  have hl : (-17951278979 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch055Lower j * hpThetaShiftOneBatch055Neg65WeightLower j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftOneBatch055Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftOneBatch055Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch055Lower j * hpThetaShiftOneBatch055Neg65WeightUpper j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftOneBatch055Neg65WeightUpper j) / 1600) ≤ (-34293017999 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftOneBatch055Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1100 : ℝ) / 1600 = 55 / 80 by norm_num,
    show ((1100 : ℝ) + 20) / 1600 = (55 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch055Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (32471209729 / 100000000000 : ℝ)
  | 1 => (326226303739 / 1000000000000 : ℝ)
  | 2 => (163867665559 / 500000000000 : ℝ)
  | 3 => (329239038197 / 1000000000000 : ℝ)
  | 4 => (330737282559 / 1000000000000 : ℝ)
  | 5 => (66445984117 / 200000000000 : ℝ)
  | 6 => (333716807453 / 1000000000000 : ℝ)
  | 7 => (335197797133 / 1000000000000 : ℝ)
  | 8 => (2693381939 / 8000000000 : ℝ)
  | 9 => (338141494709 / 1000000000000 : ℝ)
  | 10 => (84900976109 / 250000000000 : ℝ)
  | 11 => (17052991031 / 50000000000 : ℝ)
  | 12 => (342509091087 / 1000000000000 : ℝ)
  | 13 => (343951562413 / 1000000000000 : ℝ)
  | 14 => (345387079921 / 1000000000000 : ℝ)
  | 15 => (13872619507 / 40000000000 : ℝ)
  | 16 => (348236628471 / 1000000000000 : ℝ)
  | 17 => (349650343833 / 1000000000000 : ℝ)
  | 18 => (175528237003 / 500000000000 : ℝ)
  | 19 => (7049097159 / 20000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch055Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (16311315187 / 50000000000 : ℝ)
  | 1 => (327735331119 / 1000000000000 : ℝ)
  | 2 => (164619519099 / 500000000000 : ℝ)
  | 3 => (129194251 / 390625000 : ℝ)
  | 4 => (166114960293 / 500000000000 : ℝ)
  | 5 => (166858403727 / 500000000000 : ℝ)
  | 6 => (167598898567 / 500000000000 : ℝ)
  | 7 => (42084092797 / 125000000000 : ℝ)
  | 8 => (33814149471 / 100000000000 : ℝ)
  | 9 => (339603904437 / 1000000000000 : ℝ)
  | 10 => (341059820621 / 1000000000000 : ℝ)
  | 11 => (21406818193 / 62500000000 : ℝ)
  | 12 => (171975781207 / 500000000000 : ℝ)
  | 13 => (172693539961 / 500000000000 : ℝ)
  | 14 => (86703871919 / 250000000000 : ℝ)
  | 15 => (43529578559 / 125000000000 : ℝ)
  | 16 => (174825171917 / 500000000000 : ℝ)
  | 17 => (351056474007 / 1000000000000 : ℝ)
  | 18 => (352454857951 / 1000000000000 : ℝ)
  | 19 => (176922666667 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch055Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1100 : ℝ) + (j.val : ℝ)) / 1600)
      (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch055Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch055Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1100 : ℝ) + (j.val : ℝ)) / 1600)
    (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch055Neg40WeightLower j.val) (hpThetaShiftOneBatch055Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch055Neg40WeightLower, hpThetaShiftOneBatch055Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch055Neg40_integral_bounds :
    (22748984751 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (23339926397 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch055Lower hpThetaJensenCellsBatch055Upper
    hpThetaShiftOneBatch055Neg40WeightLower hpThetaShiftOneBatch055Neg40WeightUpper hpThetaJensenCellsBatch055_bounds hpThetaShiftOneBatch055Neg40_weight_bounds
  have hl : (22748984751 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch055Lower j * hpThetaShiftOneBatch055Neg40WeightLower j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftOneBatch055Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftOneBatch055Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch055Lower j * hpThetaShiftOneBatch055Neg40WeightUpper j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftOneBatch055Neg40WeightUpper j) / 1600) ≤ (23339926397 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftOneBatch055Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1100 : ℝ) / 1600 = 55 / 80 by norm_num,
    show ((1100 : ℝ) + 20) / 1600 = (55 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch055Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3121114897 / 50000000000 : ℝ)
  | 1 => (-62021079363 / 1000000000000 : ℝ)
  | 2 => (-15403838037 / 250000000000 : ℝ)
  | 3 => (-382531883 / 6250000000 : ℝ)
  | 4 => (-1899697243 / 31250000000 : ℝ)
  | 5 => (-30185484343 / 500000000000 : ℝ)
  | 6 => (-29973528547 / 500000000000 : ℝ)
  | 7 => (-59518562119 / 1000000000000 : ℝ)
  | 8 => (-3692841807 / 62500000000 : ℝ)
  | 9 => (-58647762661 / 1000000000000 : ℝ)
  | 10 => (-58205428589 / 1000000000000 : ℝ)
  | 11 => (-11551690391 / 200000000000 : ℝ)
  | 12 => (-11461363611 / 200000000000 : ℝ)
  | 13 => (-56850512223 / 1000000000000 : ℝ)
  | 14 => (-14097379957 / 250000000000 : ℝ)
  | 15 => (-55923826281 / 1000000000000 : ℝ)
  | 16 => (-5545341703 / 100000000000 : ℝ)
  | 17 => (-54978277561 / 1000000000000 : ℝ)
  | 18 => (-13624598351 / 250000000000 : ℝ)
  | 19 => (-432110001 / 8000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch055Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-31010539681 / 500000000000 : ℝ)
  | 1 => (-61615352147 / 1000000000000 : ℝ)
  | 2 => (-61205101279 / 1000000000000 : ℝ)
  | 3 => (-2431612471 / 40000000000 : ℝ)
  | 4 => (-12074193737 / 200000000000 : ℝ)
  | 5 => (-59947057093 / 1000000000000 : ℝ)
  | 6 => (-29759281059 / 500000000000 : ℝ)
  | 7 => (-59085468911 / 1000000000000 : ℝ)
  | 8 => (-2932388133 / 50000000000 : ℝ)
  | 9 => (-14551357147 / 250000000000 : ℝ)
  | 10 => (-28879225977 / 500000000000 : ℝ)
  | 11 => (-28653409027 / 500000000000 : ℝ)
  | 12 => (-28425256111 / 500000000000 : ℝ)
  | 13 => (-56389519827 / 1000000000000 : ℝ)
  | 14 => (-1398095657 / 25000000000 : ℝ)
  | 15 => (-55453417029 / 1000000000000 : ℝ)
  | 16 => (-1374456939 / 25000000000 : ℝ)
  | 17 => (-54498393403 / 1000000000000 : ℝ)
  | 18 => (-13503437531 / 250000000000 : ℝ)
  | 19 => (-53524333333 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch055Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1100 : ℝ) + (j.val : ℝ)) / 1600)
      (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch055Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch055Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1100 : ℝ) + (j.val : ℝ)) / 1600)
    (((1100 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch055Neg20WeightLower j.val) (hpThetaShiftOneBatch055Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch055Neg20WeightLower, hpThetaShiftOneBatch055Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch055Neg20_integral_bounds :
    (-50287799 / 12500000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (55 / 80 : ℝ) ((55 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (-488540031 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1100 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch055Lower hpThetaJensenCellsBatch055Upper
    hpThetaShiftOneBatch055Neg20WeightLower hpThetaShiftOneBatch055Neg20WeightUpper hpThetaJensenCellsBatch055_bounds hpThetaShiftOneBatch055Neg20_weight_bounds
  have hl : (-50287799 / 12500000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch055Lower j * hpThetaShiftOneBatch055Neg20WeightLower j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftOneBatch055Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftOneBatch055Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch055Lower j * hpThetaShiftOneBatch055Neg20WeightUpper j)
        (hpThetaJensenCellsBatch055Upper j * hpThetaShiftOneBatch055Neg20WeightUpper j) / 1600) ≤ (-488540031 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch055Lower, hpThetaJensenCellsBatch055Upper,
      hpThetaShiftOneBatch055Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1100 : ℝ) / 1600 = 55 / 80 by norm_num,
    show ((1100 : ℝ) + 20) / 1600 = (55 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch055Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch055Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch055Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch055Neg20_integral_bounds
end HodgeProofHP
