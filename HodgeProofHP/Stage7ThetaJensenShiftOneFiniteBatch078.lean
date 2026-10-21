/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch078

/-! Exact signed weight and batch integral certificates, batch 78 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch078Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-147590264272623 / 500000000000 : ℝ)
  | 1 => (-296917669218841 / 1000000000000 : ℝ)
  | 2 => (-74665883044777 / 250000000000 : ℝ)
  | 3 => (-300418154116017 / 1000000000000 : ℝ)
  | 4 => (-151090785922741 / 500000000000 : ℝ)
  | 5 => (-60790764461939 / 200000000000 : ℝ)
  | 6 => (-305734942577471 / 1000000000000 : ℝ)
  | 7 => (-307524969844587 / 1000000000000 : ℝ)
  | 8 => (-154661970717061 / 500000000000 : ℝ)
  | 9 => (-311131894796801 / 1000000000000 : ℝ)
  | 10 => (-156474433755667 / 500000000000 : ℝ)
  | 11 => (-78693724321191 / 250000000000 : ℝ)
  | 12 => (-39576252744101 / 125000000000 : ℝ)
  | 13 => (-159227139740101 / 500000000000 : ℝ)
  | 14 => (-80076926990261 / 250000000000 : ℝ)
  | 15 => (-161085172809573 / 500000000000 : ℝ)
  | 16 => (-162021115404187 / 500000000000 : ℝ)
  | 17 => (-325923402013001 / 1000000000000 : ℝ)
  | 18 => (-327813897848049 / 1000000000000 : ℝ)
  | 19 => (-329713757059643 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch078Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-293452073593957 / 1000000000000 : ℝ)
  | 1 => (-59036105709049 / 200000000000 : ℝ)
  | 2 => (-7422941730471 / 25000000000 : ℝ)
  | 3 => (-298663532179107 / 1000000000000 : ℝ)
  | 4 => (-18776134632251 / 62500000000 : ℝ)
  | 5 => (-302181571845481 / 1000000000000 : ℝ)
  | 6 => (-151976911154847 / 500000000000 : ℝ)
  | 7 => (-30573494257747 / 100000000000 : ℝ)
  | 8 => (-153762484922293 / 500000000000 : ℝ)
  | 9 => (-309323941434121 / 1000000000000 : ℝ)
  | 10 => (-24307179281 / 78125000 : ℝ)
  | 11 => (-312948867511333 / 1000000000000 : ℝ)
  | 12 => (-314774897284763 / 1000000000000 : ℝ)
  | 13 => (-316610021952807 / 1000000000000 : ℝ)
  | 14 => (-318454279480201 / 1000000000000 : ℝ)
  | 15 => (-320307707961043 / 1000000000000 : ℝ)
  | 16 => (-64434069123829 / 200000000000 : ℝ)
  | 17 => (-324042230808373 / 1000000000000 : ℝ)
  | 18 => (-325923402013 / 1000000000 : ℝ)
  | 19 => (-20488368615503 / 62500000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch078Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1560 : ℝ) + (j.val : ℝ)) / 1600)
      (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch078Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch078Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1560 : ℝ) + (j.val : ℝ)) / 1600)
    (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch078Neg100WeightLower j.val) (hpThetaShiftOneBatch078Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch078Neg100WeightLower, hpThetaShiftOneBatch078Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch078Neg100_integral_bounds :
    (-4740902641 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-1139468471 / 250000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch078Lower hpThetaJensenCellsBatch078Upper
    hpThetaShiftOneBatch078Neg100WeightLower hpThetaShiftOneBatch078Neg100WeightUpper hpThetaJensenCellsBatch078_bounds hpThetaShiftOneBatch078Neg100_weight_bounds
  have hl : (-4740902641 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch078Lower j * hpThetaShiftOneBatch078Neg100WeightLower j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftOneBatch078Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftOneBatch078Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch078Lower j * hpThetaShiftOneBatch078Neg100WeightUpper j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftOneBatch078Neg100WeightUpper j) / 1600) ≤ (-1139468471 / 250000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftOneBatch078Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1560 : ℝ) / 1600 = 78 / 80 by norm_num,
    show ((1560 : ℝ) + 20) / 1600 = (78 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch078Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-14335004172451 / 250000000000 : ℝ)
  | 1 => (-57715707075103 / 1000000000000 : ℝ)
  | 2 => (-58093440945401 / 1000000000000 : ℝ)
  | 3 => (-58473227421693 / 1000000000000 : ℝ)
  | 4 => (-7356884457207 / 125000000000 : ℝ)
  | 5 => (-59238994839743 / 1000000000000 : ℝ)
  | 6 => (-14906248546817 / 250000000000 : ℝ)
  | 7 => (-7501635369063 / 125000000000 : ℝ)
  | 8 => (-60403270420771 / 1000000000000 : ℝ)
  | 9 => (-2431822636421 / 40000000000 : ℝ)
  | 10 => (-12237995754691 / 200000000000 : ℝ)
  | 11 => (-6158651839457 / 100000000000 : ℝ)
  | 12 => (-30992597096147 / 500000000000 : ℝ)
  | 13 => (-12477203123711 / 200000000000 : ℝ)
  | 14 => (-62788992158881 / 1000000000000 : ℝ)
  | 15 => (-63194133332491 / 1000000000000 : ℝ)
  | 16 => (-12720289738477 / 200000000000 : ℝ)
  | 17 => (-64010947825443 / 1000000000000 : ℝ)
  | 18 => (-251650938877 / 3906250000 : ℝ)
  | 19 => (-64836535928501 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch078Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3560397543819 / 62500000000 : ℝ)
  | 1 => (-57340016689803 / 1000000000000 : ℝ)
  | 2 => (-28857853537551 / 500000000000 : ℝ)
  | 3 => (-290467204727 / 5000000000 : ℝ)
  | 4 => (-14618306855423 / 250000000000 : ℝ)
  | 5 => (-11771015131531 / 200000000000 : ℝ)
  | 6 => (-29619497419871 / 500000000000 : ℝ)
  | 7 => (-59624994187267 / 1000000000000 : ℝ)
  | 8 => (-60013082952503 / 1000000000000 : ℝ)
  | 9 => (-6040327042077 / 100000000000 : ℝ)
  | 10 => (-15198891477631 / 250000000000 : ℝ)
  | 11 => (-30594989386727 / 500000000000 : ℝ)
  | 12 => (-61586518394569 / 1000000000000 : ℝ)
  | 13 => (-61985194192293 / 1000000000000 : ℝ)
  | 14 => (-31193007809277 / 500000000000 : ℝ)
  | 15 => (-392431200993 / 6250000000 : ℝ)
  | 16 => (-6319413333249 / 100000000000 : ℝ)
  | 17 => (-1987545271637 / 31250000000 : ℝ)
  | 18 => (-32005473912721 / 500000000000 : ℝ)
  | 19 => (-64422640352511 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch078Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1560 : ℝ) + (j.val : ℝ)) / 1600)
      (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch078Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch078Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1560 : ℝ) + (j.val : ℝ)) / 1600)
    (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch078Neg65WeightLower j.val) (hpThetaShiftOneBatch078Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch078Neg65WeightLower, hpThetaShiftOneBatch078Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch078Neg65_integral_bounds :
    (-926271193 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-111241929 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch078Lower hpThetaJensenCellsBatch078Upper
    hpThetaShiftOneBatch078Neg65WeightLower hpThetaShiftOneBatch078Neg65WeightUpper hpThetaJensenCellsBatch078_bounds hpThetaShiftOneBatch078Neg65_weight_bounds
  have hl : (-926271193 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch078Lower j * hpThetaShiftOneBatch078Neg65WeightLower j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftOneBatch078Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftOneBatch078Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch078Lower j * hpThetaShiftOneBatch078Neg65WeightUpper j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftOneBatch078Neg65WeightUpper j) / 1600) ≤ (-111241929 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftOneBatch078Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1560 : ℝ) / 1600 = 78 / 80 by norm_num,
    show ((1560 : ℝ) + 20) / 1600 = (78 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch078Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-669935849231 / 125000000000 : ℝ)
  | 1 => (-5409932505861 / 1000000000000 : ℝ)
  | 2 => (-5460718137267 / 1000000000000 : ℝ)
  | 3 => (-2755922714727 / 500000000000 : ℝ)
  | 4 => (-5563316130641 / 1000000000000 : ℝ)
  | 5 => (-5615131995901 / 1000000000000 : ℝ)
  | 6 => (-283364739359 / 50000000000 : ℝ)
  | 7 => (-2859903136659 / 500000000000 : ℝ)
  | 8 => (-1443167057517 / 250000000000 : ℝ)
  | 9 => (-5825882440117 / 1000000000000 : ℝ)
  | 10 => (-2939725346553 / 500000000000 : ℝ)
  | 11 => (-118667495713 / 20000000000 : ℝ)
  | 12 => (-5987656521361 / 1000000000000 : ℝ)
  | 13 => (-1208459542173 / 200000000000 : ℝ)
  | 14 => (-3048650085911 / 500000000000 : ℝ)
  | 15 => (-769083216119 / 125000000000 : ℝ)
  | 16 => (-124167924281 / 20000000000 : ℝ)
  | 17 => (-783061683251 / 125000000000 : ℝ)
  | 18 => (-6320959330837 / 1000000000000 : ℝ)
  | 19 => (-6377795661687 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch078Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-5309379266653 / 1000000000000 : ℝ)
  | 1 => (-5359486793847 / 1000000000000 : ℝ)
  | 2 => (-270496625293 / 50000000000 : ℝ)
  | 3 => (-2730359068633 / 500000000000 : ℝ)
  | 4 => (-5511845429453 / 1000000000000 : ℝ)
  | 5 => (-69541451633 / 12500000000 : ℝ)
  | 6 => (-56151319959 / 10000000000 : ℝ)
  | 7 => (-5667294787179 / 1000000000000 : ℝ)
  | 8 => (-5719806273317 / 1000000000000 : ℝ)
  | 9 => (-5772668230067 / 1000000000000 : ℝ)
  | 10 => (-1456470610029 / 250000000000 : ℝ)
  | 11 => (-1175890138621 / 200000000000 : ℝ)
  | 12 => (-5933374785649 / 1000000000000 : ℝ)
  | 13 => (-74845706517 / 12500000000 : ℝ)
  | 14 => (-377643606929 / 62500000000 : ℝ)
  | 15 => (-6097300171821 / 1000000000000 : ℝ)
  | 16 => (-6152665728951 / 1000000000000 : ℝ)
  | 17 => (-6208396214049 / 1000000000000 : ℝ)
  | 18 => (-6264493466007 / 1000000000000 : ℝ)
  | 19 => (-1580239832709 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch078Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1560 : ℝ) + (j.val : ℝ)) / 1600)
      (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch078Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch078Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1560 : ℝ) + (j.val : ℝ)) / 1600)
    (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch078Neg40WeightLower j.val) (hpThetaShiftOneBatch078Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch078Neg40WeightLower, hpThetaShiftOneBatch078Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch078Neg40_integral_bounds :
    (-22180379 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-85010613 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch078Lower hpThetaJensenCellsBatch078Upper
    hpThetaShiftOneBatch078Neg40WeightLower hpThetaShiftOneBatch078Neg40WeightUpper hpThetaJensenCellsBatch078_bounds hpThetaShiftOneBatch078Neg40_weight_bounds
  have hl : (-22180379 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch078Lower j * hpThetaShiftOneBatch078Neg40WeightLower j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftOneBatch078Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftOneBatch078Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch078Lower j * hpThetaShiftOneBatch078Neg40WeightUpper j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftOneBatch078Neg40WeightUpper j) / 1600) ≤ (-85010613 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftOneBatch078Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1560 : ℝ) / 1600 = 78 / 80 by norm_num,
    show ((1560 : ℝ) + 20) / 1600 = (78 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch078Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (658737944451 / 1000000000000 : ℝ)
  | 1 => (330428627191 / 500000000000 : ℝ)
  | 2 => (165742746939 / 250000000000 : ℝ)
  | 3 => (66507904247 / 100000000000 : ℝ)
  | 4 => (667181315817 / 1000000000000 : ℝ)
  | 5 => (133855540897 / 200000000000 : ℝ)
  | 6 => (671368104553 / 1000000000000 : ℝ)
  | 7 => (673452411491 / 1000000000000 : ℝ)
  | 8 => (135106104031 / 200000000000 : ℝ)
  | 9 => (169400581197 / 250000000000 : ℝ)
  | 10 => (679667719017 / 1000000000000 : ℝ)
  | 11 => (681726595849 / 1000000000000 : ℝ)
  | 12 => (170944711917 / 250000000000 : ℝ)
  | 13 => (685824366239 / 1000000000000 : ℝ)
  | 14 => (343931521349 / 500000000000 : ℝ)
  | 15 => (344947383777 / 500000000000 : ℝ)
  | 16 => (691919430687 / 1000000000000 : ℝ)
  | 17 => (138787384269 / 200000000000 : ℝ)
  | 18 => (695947128139 / 1000000000000 : ℝ)
  | 19 => (697949939047 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch078Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (660857254383 / 1000000000000 : ℝ)
  | 1 => (662970987757 / 1000000000000 : ℝ)
  | 2 => (665079042471 / 1000000000000 : ℝ)
  | 3 => (333590657909 / 500000000000 : ℝ)
  | 4 => (334638852243 / 500000000000 : ℝ)
  | 5 => (335684052277 / 500000000000 : ℝ)
  | 6 => (168363102873 / 250000000000 : ℝ)
  | 7 => (168882630039 / 250000000000 : ℝ)
  | 8 => (677602324789 / 1000000000000 : ℝ)
  | 9 => (339833859509 / 500000000000 : ℝ)
  | 10 => (13634531917 / 20000000000 : ℝ)
  | 11 => (683778847669 / 1000000000000 : ℝ)
  | 12 => (4286402289 / 6250000000 : ℝ)
  | 13 => (687863042699 / 1000000000000 : ℝ)
  | 14 => (137978953511 / 200000000000 : ℝ)
  | 15 => (21622482209 / 31250000000 : ℝ)
  | 16 => (346968460673 / 500000000000 : ℝ)
  | 17 => (34797356407 / 50000000000 : ℝ)
  | 18 => (87243742381 / 125000000000 : ℝ)
  | 19 => (139989048281 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch078Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1560 : ℝ) + (j.val : ℝ)) / 1600)
      (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch078Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch078Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1560 : ℝ) + (j.val : ℝ)) / 1600)
    (((1560 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch078Neg20WeightLower j.val) (hpThetaShiftOneBatch078Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch078Neg20WeightLower, hpThetaShiftOneBatch078Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch078Neg20_integral_bounds :
    (9987251 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (78 / 80 : ℝ) ((78 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (517971 / 50000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1560 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch078Lower hpThetaJensenCellsBatch078Upper
    hpThetaShiftOneBatch078Neg20WeightLower hpThetaShiftOneBatch078Neg20WeightUpper hpThetaJensenCellsBatch078_bounds hpThetaShiftOneBatch078Neg20_weight_bounds
  have hl : (9987251 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch078Lower j * hpThetaShiftOneBatch078Neg20WeightLower j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftOneBatch078Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftOneBatch078Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch078Lower j * hpThetaShiftOneBatch078Neg20WeightUpper j)
        (hpThetaJensenCellsBatch078Upper j * hpThetaShiftOneBatch078Neg20WeightUpper j) / 1600) ≤ (517971 / 50000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch078Lower, hpThetaJensenCellsBatch078Upper,
      hpThetaShiftOneBatch078Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1560 : ℝ) / 1600 = 78 / 80 by norm_num,
    show ((1560 : ℝ) + 20) / 1600 = (78 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch078Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch078Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch078Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch078Neg20_integral_bounds
end HodgeProofHP
