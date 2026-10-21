/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch077

/-! Exact signed weight and batch integral certificates, batch 77 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch077Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-262213993640507 / 1000000000000 : ℝ)
  | 1 => (-263784202498447 / 1000000000000 : ℝ)
  | 2 => (-132681212887547 / 500000000000 : ℝ)
  | 3 => (-266948697711773 / 1000000000000 : ℝ)
  | 4 => (-268543052669111 / 1000000000000 : ℝ)
  | 5 => (-270145525127357 / 1000000000000 : ℝ)
  | 6 => (-271756149686709 / 1000000000000 : ℝ)
  | 7 => (-2135741883341 / 7812500000 : ℝ)
  | 8 => (-137500997055629 / 500000000000 : ℝ)
  | 9 => (-276637283779557 / 1000000000000 : ℝ)
  | 10 => (-278280865155829 / 1000000000000 : ℝ)
  | 11 => (-279932773444951 / 1000000000000 : ℝ)
  | 12 => (-140796521986861 / 500000000000 : ℝ)
  | 13 => (-283261712191199 / 1000000000000 : ℝ)
  | 14 => (-11397552546761 / 40000000000 : ℝ)
  | 15 => (-286624384101763 / 1000000000000 : ℝ)
  | 16 => (-288318459307229 / 1000000000000 : ℝ)
  | 17 => (-11600843009073 / 40000000000 : ℝ)
  | 18 => (-2333858143407 / 8000000000 : ℝ)
  | 19 => (-146726036796979 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch077Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-260651765078919 / 1000000000000 : ℝ)
  | 1 => (-131106996820253 / 500000000000 : ℝ)
  | 2 => (-131892101249223 / 500000000000 : ℝ)
  | 3 => (-265362425775093 / 1000000000000 : ℝ)
  | 4 => (-66737174427943 / 250000000000 : ℝ)
  | 5 => (-26854305266911 / 100000000000 : ℝ)
  | 6 => (-67536381281839 / 250000000000 : ℝ)
  | 7 => (-67939037421677 / 250000000000 : ℝ)
  | 8 => (-273374961067647 / 1000000000000 : ℝ)
  | 9 => (-275001994111257 / 1000000000000 : ℝ)
  | 10 => (-69159320944889 / 250000000000 : ℝ)
  | 11 => (-69570216288957 / 250000000000 : ℝ)
  | 12 => (-5598655468899 / 20000000000 : ℝ)
  | 13 => (-281593043973721 / 1000000000000 : ℝ)
  | 14 => (-141630856095599 / 500000000000 : ℝ)
  | 15 => (-8904337927157 / 31250000000 : ℝ)
  | 16 => (-143312192050881 / 500000000000 : ℝ)
  | 17 => (-72079614826807 / 250000000000 : ℝ)
  | 18 => (-36252634403353 / 125000000000 : ℝ)
  | 19 => (-145866133962937 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch077Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1540 : ℝ) + (j.val : ℝ)) / 1600)
      (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch077Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch077Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1540 : ℝ) + (j.val : ℝ)) / 1600)
    (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch077Neg100WeightLower j.val) (hpThetaShiftOneBatch077Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch077Neg100WeightLower, hpThetaShiftOneBatch077Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch077Neg100_integral_bounds :
    (-6902607181 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-6640168879 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch077Lower hpThetaJensenCellsBatch077Upper
    hpThetaShiftOneBatch077Neg100WeightLower hpThetaShiftOneBatch077Neg100WeightUpper hpThetaJensenCellsBatch077_bounds hpThetaShiftOneBatch077Neg100_weight_bounds
  have hl : (-6902607181 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch077Lower j * hpThetaShiftOneBatch077Neg100WeightLower j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftOneBatch077Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftOneBatch077Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch077Lower j * hpThetaShiftOneBatch077Neg100WeightUpper j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftOneBatch077Neg100WeightUpper j) / 1600) ≤ (-6640168879 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftOneBatch077Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1540 : ℝ) / 1600 = 77 / 80 by norm_num,
    show ((1540 : ℝ) + 20) / 1600 = (77 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch077Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-2512079004613 / 50000000000 : ℝ)
  | 1 => (-25289133324563 / 500000000000 : ℝ)
  | 2 => (-5091682099659 / 100000000000 : ℝ)
  | 3 => (-25628625810371 / 500000000000 : ℝ)
  | 4 => (-3224972939911 / 62500000000 : ℝ)
  | 5 => (-10388755159617 / 200000000000 : ℝ)
  | 6 => (-2614494323917 / 50000000000 : ℝ)
  | 7 => (-52637907689587 / 1000000000000 : ℝ)
  | 8 => (-13246962018331 / 250000000000 : ℝ)
  | 9 => (-53339716302399 / 1000000000000 : ℝ)
  | 10 => (-53693521081089 / 1000000000000 : ℝ)
  | 11 => (-10809854229039 / 200000000000 : ℝ)
  | 12 => (-27203487631063 / 500000000000 : ℝ)
  | 13 => (-54766642230989 / 1000000000000 : ℝ)
  | 14 => (-55128280882679 / 1000000000000 : ℝ)
  | 15 => (-27745950039983 / 500000000000 : ℝ)
  | 16 => (-3491094294849 / 62500000000 : ℝ)
  | 17 => (-702813946529 / 12500000000 : ℝ)
  | 18 => (-28297365026553 / 500000000000 : ℝ)
  | 19 => (-11393272140221 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch077Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-24953376435363 / 500000000000 : ℝ)
  | 1 => (-50241580092259 / 1000000000000 : ℝ)
  | 2 => (-404626133193 / 8000000000 : ℝ)
  | 3 => (-50916820996589 / 1000000000000 : ℝ)
  | 4 => (-51257251620741 / 1000000000000 : ℝ)
  | 5 => (-2063982681543 / 40000000000 : ℝ)
  | 6 => (-12985943949521 / 250000000000 : ℝ)
  | 7 => (-52289886478339 / 1000000000000 : ℝ)
  | 8 => (-26318953844793 / 500000000000 : ℝ)
  | 9 => (-52987848073323 / 1000000000000 : ℝ)
  | 10 => (-26669858151199 / 500000000000 : ℝ)
  | 11 => (-209740316723 / 3906250000 : ℝ)
  | 12 => (-27024635572597 / 500000000000 : ℝ)
  | 13 => (-435255802097 / 8000000000 : ℝ)
  | 14 => (-13691660557747 / 250000000000 : ℝ)
  | 15 => (-27564140441339 / 500000000000 : ℝ)
  | 16 => (-11098380015993 / 200000000000 : ℝ)
  | 17 => (-55857508717583 / 1000000000000 : ℝ)
  | 18 => (-56225115722319 / 1000000000000 : ℝ)
  | 19 => (-11318946010621 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch077Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1540 : ℝ) + (j.val : ℝ)) / 1600)
      (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch077Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch077Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1540 : ℝ) + (j.val : ℝ)) / 1600)
    (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch077Neg65WeightLower j.val) (hpThetaShiftOneBatch077Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch077Neg65WeightLower, hpThetaShiftOneBatch077Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch077Neg65_integral_bounds :
    (-1330782231 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-1279301559 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch077Lower hpThetaJensenCellsBatch077Upper
    hpThetaShiftOneBatch077Neg65WeightLower hpThetaShiftOneBatch077Neg65WeightUpper hpThetaJensenCellsBatch077_bounds hpThetaShiftOneBatch077Neg65_weight_bounds
  have hl : (-1330782231 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch077Lower j * hpThetaShiftOneBatch077Neg65WeightLower j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftOneBatch077Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftOneBatch077Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch077Lower j * hpThetaShiftOneBatch077Neg65WeightUpper j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftOneBatch077Neg65WeightUpper j) / 1600) ≤ (-1279301559 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftOneBatch077Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1540 : ℝ) / 1600 = 77 / 80 by norm_num,
    show ((1540 : ℝ) + 20) / 1600 = (77 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch077Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-4419333549551 / 1000000000000 : ℝ)
  | 1 => (-278958513647 / 62500000000 : ℝ)
  | 2 => (-281727836447 / 62500000000 : ℝ)
  | 3 => (-1138065663209 / 250000000000 : ℝ)
  | 4 => (-2298594821363 / 500000000000 : ℝ)
  | 5 => (-928485594921 / 200000000000 : ℝ)
  | 6 => (-2343989638367 / 500000000000 : ℝ)
  | 7 => (-4733845183871 / 1000000000000 : ℝ)
  | 8 => (-4780027337293 / 1000000000000 : ℝ)
  | 9 => (-482652738481 / 100000000000 : ℝ)
  | 10 => (-609168372599 / 125000000000 : ℝ)
  | 11 => (-4920487786181 / 1000000000000 : ℝ)
  | 12 => (-4967951468517 / 1000000000000 : ℝ)
  | 13 => (-5015739701953 / 1000000000000 : ℝ)
  | 14 => (-1265963541819 / 250000000000 : ℝ)
  | 15 => (-639037068991 / 125000000000 : ℝ)
  | 16 => (-206442742001 / 40000000000 : ℝ)
  | 17 => (-41681374899 / 8000000000 : ℝ)
  | 18 => (-5259608196499 / 1000000000000 : ℝ)
  | 19 => (-2654689633327 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch077Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-875127154857 / 200000000000 : ℝ)
  | 1 => (-88386670991 / 20000000000 : ℝ)
  | 2 => (-4463336218351 / 1000000000000 : ℝ)
  | 3 => (-4507645383151 / 1000000000000 : ℝ)
  | 4 => (-910452530567 / 200000000000 : ℝ)
  | 5 => (-183887585709 / 40000000000 : ℝ)
  | 6 => (-1160606993651 / 250000000000 : ℝ)
  | 7 => (-4687979276733 / 1000000000000 : ℝ)
  | 8 => (-473384518387 / 100000000000 : ℝ)
  | 9 => (-1195006834323 / 250000000000 : ℝ)
  | 10 => (-4826527384809 / 1000000000000 : ℝ)
  | 11 => (-4873346980791 / 1000000000000 : ℝ)
  | 12 => (-246024389309 / 50000000000 : ℝ)
  | 13 => (-1241987867129 / 250000000000 : ℝ)
  | 14 => (-78370932843 / 15625000000 : ℝ)
  | 15 => (-202554166691 / 40000000000 : ℝ)
  | 16 => (-5112296551927 / 1000000000000 : ℝ)
  | 17 => (-645133568753 / 125000000000 : ℝ)
  | 18 => (-2605085931187 / 500000000000 : ℝ)
  | 19 => (-2629804098249 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch077Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1540 : ℝ) + (j.val : ℝ)) / 1600)
      (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch077Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch077Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1540 : ℝ) + (j.val : ℝ)) / 1600)
    (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch077Neg40WeightLower j.val) (hpThetaShiftOneBatch077Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch077Neg40WeightLower, hpThetaShiftOneBatch077Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch077Neg40_integral_bounds :
    (-30091201 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-115354039 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch077Lower hpThetaJensenCellsBatch077Upper
    hpThetaShiftOneBatch077Neg40WeightLower hpThetaShiftOneBatch077Neg40WeightUpper hpThetaJensenCellsBatch077_bounds hpThetaShiftOneBatch077Neg40_weight_bounds
  have hl : (-30091201 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch077Lower j * hpThetaShiftOneBatch077Neg40WeightLower j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftOneBatch077Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftOneBatch077Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch077Lower j * hpThetaShiftOneBatch077Neg40WeightUpper j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftOneBatch077Neg40WeightUpper j) / 1600) ≤ (-115354039 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftOneBatch077Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1540 : ℝ) / 1600 = 77 / 80 by norm_num,
    show ((1540 : ℝ) + 20) / 1600 = (77 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch077Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (123066530909 / 200000000000 : ℝ)
  | 1 => (154385741109 / 250000000000 : ℝ)
  | 2 => (619749616383 / 1000000000000 : ℝ)
  | 3 => (124390503981 / 200000000000 : ℝ)
  | 4 => (624151583961 / 1000000000000 : ℝ)
  | 5 => (156586679237 / 250000000000 : ℝ)
  | 6 => (314268913347 / 500000000000 : ℝ)
  | 7 => (39420301279 / 62500000000 : ℝ)
  | 8 => (12658152099 / 20000000000 : ℝ)
  | 9 => (317543043137 / 500000000000 : ℝ)
  | 10 => (637260169983 / 1000000000000 : ℝ)
  | 11 => (639429761051 / 1000000000000 : ℝ)
  | 12 => (20049836371 / 31250000000 : ℝ)
  | 13 => (643755082259 / 1000000000000 : ℝ)
  | 14 => (129182123889 / 200000000000 : ℝ)
  | 15 => (324030639039 / 500000000000 : ℝ)
  | 16 => (650206960219 / 1000000000000 : ℝ)
  | 17 => (652347567341 / 1000000000000 : ℝ)
  | 18 => (654483000327 / 1000000000000 : ℝ)
  | 19 => (131322631893 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch077Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (617542964437 / 1000000000000 : ℝ)
  | 1 => (2420896939 / 3906250000 : ℝ)
  | 2 => (310976259953 / 500000000000 : ℝ)
  | 3 => (312075791981 / 500000000000 : ℝ)
  | 4 => (626346716949 / 1000000000000 : ℝ)
  | 5 => (125707565339 / 200000000000 : ℝ)
  | 6 => (126144964093 / 200000000000 : ℝ)
  | 7 => (632907604951 / 1000000000000 : ℝ)
  | 8 => (25403443451 / 40000000000 : ℝ)
  | 9 => (2489297539 / 3906250000 : ℝ)
  | 10 => (159857440263 / 250000000000 : ℝ)
  | 11 => (641594763873 / 1000000000000 : ℝ)
  | 12 => (32187754113 / 50000000000 : ℝ)
  | 13 => (322955309723 / 500000000000 : ℝ)
  | 14 => (648061278079 / 1000000000000 : ℝ)
  | 15 => (32510348011 / 50000000000 : ℝ)
  | 16 => (326173783671 / 500000000000 : ℝ)
  | 17 => (81810375041 / 125000000000 : ℝ)
  | 18 => (328306579733 / 500000000000 : ℝ)
  | 19 => (164684486113 / 250000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch077Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1540 : ℝ) + (j.val : ℝ)) / 1600)
      (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch077Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch077Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1540 : ℝ) + (j.val : ℝ)) / 1600)
    (((1540 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch077Neg20WeightLower j.val) (hpThetaShiftOneBatch077Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch077Neg20WeightLower, hpThetaShiftOneBatch077Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch077Neg20_integral_bounds :
    (7668587 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (77 / 80 : ℝ) ((77 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (1987919 / 125000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1540 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch077Lower hpThetaJensenCellsBatch077Upper
    hpThetaShiftOneBatch077Neg20WeightLower hpThetaShiftOneBatch077Neg20WeightUpper hpThetaJensenCellsBatch077_bounds hpThetaShiftOneBatch077Neg20_weight_bounds
  have hl : (7668587 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch077Lower j * hpThetaShiftOneBatch077Neg20WeightLower j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftOneBatch077Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftOneBatch077Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch077Lower j * hpThetaShiftOneBatch077Neg20WeightUpper j)
        (hpThetaJensenCellsBatch077Upper j * hpThetaShiftOneBatch077Neg20WeightUpper j) / 1600) ≤ (1987919 / 125000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch077Lower, hpThetaJensenCellsBatch077Upper,
      hpThetaShiftOneBatch077Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1540 : ℝ) / 1600 = 77 / 80 by norm_num,
    show ((1540 : ℝ) + 20) / 1600 = (77 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch077Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch077Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch077Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch077Neg20_integral_bounds
end HodgeProofHP
