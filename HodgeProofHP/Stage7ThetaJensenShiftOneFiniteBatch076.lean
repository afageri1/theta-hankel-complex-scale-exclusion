/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneBernstein
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch076

/-! Exact signed weight and batch integral certificates, batch 76 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBatch076Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-46488231083729 / 200000000000 : ℝ)
  | 1 => (-233858085719539 / 1000000000000 : ℝ)
  | 2 => (-235282370169163 / 1000000000000 : ℝ)
  | 3 => (-236714040690311 / 1000000000000 : ℝ)
  | 4 => (-238153129318697 / 1000000000000 : ℝ)
  | 5 => (-119799834101631 / 500000000000 : ℝ)
  | 6 => (-241053689606491 / 1000000000000 : ℝ)
  | 7 => (-242515225904727 / 1000000000000 : ℝ)
  | 8 => (-48796861917697 / 200000000000 : ℝ)
  | 9 => (-15341310828923 / 62500000000 : ℝ)
  | 10 => (-246945249647383 / 1000000000000 : ℝ)
  | 11 => (-248437171577259 / 1000000000000 : ℝ)
  | 12 => (-6248419300069 / 25000000000 : ℝ)
  | 13 => (-251444083990011 / 1000000000000 : ℝ)
  | 14 => (-25295914072121 / 100000000000 : ℝ)
  | 15 => (-254481975494949 / 1000000000000 : ℝ)
  | 16 => (-32001577715817 / 125000000000 : ℝ)
  | 17 => (-128775556474157 / 500000000000 : ℝ)
  | 18 => (-259097482809983 / 1000000000000 : ℝ)
  | 19 => (-6516294126973 / 25000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch076Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-231031547456287 / 1000000000000 : ℝ)
  | 1 => (-58110288854661 / 250000000000 : ℝ)
  | 2 => (-116929042859769 / 500000000000 : ℝ)
  | 3 => (-117641185084581 / 500000000000 : ℝ)
  | 4 => (-23671404069031 / 100000000000 : ℝ)
  | 5 => (-29769141164837 / 125000000000 : ℝ)
  | 6 => (-239599668203261 / 1000000000000 : ℝ)
  | 7 => (-24105368960649 / 100000000000 : ℝ)
  | 8 => (-121257612952363 / 500000000000 : ℝ)
  | 9 => (-60996077397121 / 250000000000 : ℝ)
  | 10 => (-245460973262767 / 1000000000000 : ℝ)
  | 11 => (-123472624823691 / 500000000000 : ℝ)
  | 12 => (-124218585788629 / 500000000000 : ℝ)
  | 13 => (-249936772002759 / 1000000000000 : ℝ)
  | 14 => (-25144408399001 / 100000000000 : ℝ)
  | 15 => (-252959140721209 / 1000000000000 : ℝ)
  | 16 => (-63620493873737 / 250000000000 : ℝ)
  | 17 => (-51202524345307 / 200000000000 : ℝ)
  | 18 => (-257551112948313 / 1000000000000 : ℝ)
  | 19 => (-129548741404991 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch076Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1520 : ℝ) + (j.val : ℝ)) / 1600)
      (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch076Neg100WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-100) u ∧
      hpThetaJensenShiftOneWeight (-100) u ≤ hpThetaShiftOneBatch076Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-100) (((1520 : ℝ) + (j.val : ℝ)) / 1600)
    (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch076Neg100WeightLower j.val) (hpThetaShiftOneBatch076Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch076Neg100WeightLower, hpThetaShiftOneBatch076Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch076Neg100_integral_bounds :
    (-9893504863 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-100) u) ≤ (-1904583609 / 200000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-100) (1520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch076Lower hpThetaJensenCellsBatch076Upper
    hpThetaShiftOneBatch076Neg100WeightLower hpThetaShiftOneBatch076Neg100WeightUpper hpThetaJensenCellsBatch076_bounds hpThetaShiftOneBatch076Neg100_weight_bounds
  have hl : (-9893504863 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch076Lower j * hpThetaShiftOneBatch076Neg100WeightLower j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftOneBatch076Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftOneBatch076Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch076Lower j * hpThetaShiftOneBatch076Neg100WeightUpper j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftOneBatch076Neg100WeightUpper j) / 1600) ≤ (-1904583609 / 200000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftOneBatch076Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1520 : ℝ) / 1600 = 76 / 80 by norm_num,
    show ((1520 : ℝ) + 20) / 1600 = (76 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch076Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-43887286427729 / 1000000000000 : ℝ)
  | 1 => (-44188352415953 / 1000000000000 : ℝ)
  | 2 => (-44491122831221 / 1000000000000 : ℝ)
  | 3 => (-11198901389867 / 250000000000 : ℝ)
  | 4 => (-45101808515833 / 1000000000000 : ℝ)
  | 5 => (-5676217455593 / 125000000000 : ℝ)
  | 6 => (-45719406919997 / 1000000000000 : ℝ)
  | 7 => (-46030818344847 / 1000000000000 : ℝ)
  | 8 => (-9268796390417 / 200000000000 : ℝ)
  | 9 => (-46658905804129 / 1000000000000 : ℝ)
  | 10 => (-46975597993103 / 1000000000000 : ℝ)
  | 11 => (-23647033320461 / 500000000000 : ℝ)
  | 12 => (-47614319899381 / 1000000000000 : ℝ)
  | 13 => (-9587273190047 / 200000000000 : ℝ)
  | 14 => (-6032526625661 / 125000000000 : ℝ)
  | 15 => (-48585869306477 / 1000000000000 : ℝ)
  | 16 => (-24456671562977 / 500000000000 : ℝ)
  | 17 => (-49242642766177 / 1000000000000 : ℝ)
  | 18 => (-24786888279997 / 500000000000 : ℝ)
  | 19 => (-49906752870727 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch076Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-43587917009733 / 1000000000000 : ℝ)
  | 1 => (-2742955401733 / 62500000000 : ℝ)
  | 2 => (-2761772025997 / 62500000000 : ℝ)
  | 3 => (-2224556141561 / 50000000000 : ℝ)
  | 4 => (-44795605559467 / 1000000000000 : ℝ)
  | 5 => (-5637726064479 / 125000000000 : ℝ)
  | 6 => (-45409739644743 / 1000000000000 : ℝ)
  | 7 => (-11429851729999 / 250000000000 : ℝ)
  | 8 => (-23015409172423 / 500000000000 : ℝ)
  | 9 => (-11585995488021 / 250000000000 : ℝ)
  | 10 => (-1458090806379 / 31250000000 : ℝ)
  | 11 => (-23487798996551 / 500000000000 : ℝ)
  | 12 => (-47294066640921 / 1000000000000 : ℝ)
  | 13 => (-2380715994969 / 50000000000 : ℝ)
  | 14 => (-23968182975117 / 500000000000 : ℝ)
  | 15 => (-48260213005287 / 1000000000000 : ℝ)
  | 16 => (-12146467326619 / 250000000000 : ℝ)
  | 17 => (-48913343125953 / 1000000000000 : ℝ)
  | 18 => (-1538832586443 / 31250000000 : ℝ)
  | 19 => (-49573776559993 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch076Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1520 : ℝ) + (j.val : ℝ)) / 1600)
      (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch076Neg65WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-65) u ∧
      hpThetaJensenShiftOneWeight (-65) u ≤ hpThetaShiftOneBatch076Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-65) (((1520 : ℝ) + (j.val : ℝ)) / 1600)
    (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch076Neg65WeightLower j.val) (hpThetaShiftOneBatch076Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch076Neg65WeightLower, hpThetaShiftOneBatch076Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch076Neg65_integral_bounds :
    (-940222761 / 500000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-65) u) ≤ (-1808670713 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-65) (1520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch076Lower hpThetaJensenCellsBatch076Upper
    hpThetaShiftOneBatch076Neg65WeightLower hpThetaShiftOneBatch076Neg65WeightUpper hpThetaJensenCellsBatch076_bounds hpThetaShiftOneBatch076Neg65_weight_bounds
  have hl : (-940222761 / 500000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch076Lower j * hpThetaShiftOneBatch076Neg65WeightLower j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftOneBatch076Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftOneBatch076Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch076Lower j * hpThetaShiftOneBatch076Neg65WeightUpper j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftOneBatch076Neg65WeightUpper j) / 1600) ≤ (-1808670713 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftOneBatch076Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1520 : ℝ) / 1600 = 76 / 80 by norm_num,
    show ((1520 : ℝ) + 20) / 1600 = (76 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch076Neg40WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-720244572981 / 200000000000 : ℝ)
  | 1 => (-1819711865471 / 500000000000 : ℝ)
  | 2 => (-3677900238343 / 1000000000000 : ℝ)
  | 3 => (-3716653871179 / 1000000000000 : ℝ)
  | 4 => (-1877843059793 / 500000000000 : ℝ)
  | 5 => (-189749923989 / 50000000000 : ℝ)
  | 6 => (-3834592454077 / 1000000000000 : ℝ)
  | 7 => (-3874469550913 / 1000000000000 : ℝ)
  | 8 => (-1957315642429 / 500000000000 : ℝ)
  | 9 => (-3955079176641 / 1000000000000 : ℝ)
  | 10 => (-3995814753163 / 1000000000000 : ℝ)
  | 11 => (-4036839547519 / 1000000000000 : ℝ)
  | 12 => (-2039077549507 / 500000000000 : ℝ)
  | 13 => (-2059881476593 / 500000000000 : ℝ)
  | 14 => (-4161664661821 / 1000000000000 : ℝ)
  | 15 => (-4203861782973 / 1000000000000 : ℝ)
  | 16 => (-530794485123 / 125000000000 : ℝ)
  | 17 => (-4289148526501 / 1000000000000 : ℝ)
  | 18 => (-270765081031 / 62500000000 : ℝ)
  | 19 => (-2187817887143 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch076Neg40WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1781648081101 / 500000000000 : ℝ)
  | 1 => (-450152858113 / 125000000000 : ℝ)
  | 2 => (-3639423730941 / 1000000000000 : ℝ)
  | 3 => (-1838950119171 / 500000000000 : ℝ)
  | 4 => (-1858326935589 / 500000000000 : ℝ)
  | 5 => (-751137223917 / 200000000000 : ℝ)
  | 6 => (-3794998479779 / 1000000000000 : ℝ)
  | 7 => (-958648113519 / 250000000000 : ℝ)
  | 8 => (-60538586733 / 15625000000 : ℝ)
  | 9 => (-3914631284857 / 1000000000000 : ℝ)
  | 10 => (-12359622427 / 3125000000 : ℝ)
  | 11 => (-1997907376581 / 500000000000 : ℝ)
  | 12 => (-2018419773759 / 500000000000 : ℝ)
  | 13 => (-4078155099013 / 1000000000000 : ℝ)
  | 14 => (-823952590637 / 200000000000 : ℝ)
  | 15 => (-208083233091 / 50000000000 : ℝ)
  | 16 => (-1050965445743 / 250000000000 : ℝ)
  | 17 => (-4246355880983 / 1000000000000 : ℝ)
  | 18 => (-8578297053 / 2000000000 : ℝ)
  | 19 => (-866448259299 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch076Neg40_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1520 : ℝ) + (j.val : ℝ)) / 1600)
      (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch076Neg40WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-40) u ∧
      hpThetaJensenShiftOneWeight (-40) u ≤ hpThetaShiftOneBatch076Neg40WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-40) (((1520 : ℝ) + (j.val : ℝ)) / 1600)
    (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch076Neg40WeightLower j.val) (hpThetaShiftOneBatch076Neg40WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch076Neg40WeightLower, hpThetaShiftOneBatch076Neg40WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch076Neg40_integral_bounds :
    (-4979093 / 31250000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ∧
    (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-40) u) ≤ (-3054239 / 20000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-40) (1520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch076Lower hpThetaJensenCellsBatch076Upper
    hpThetaShiftOneBatch076Neg40WeightLower hpThetaShiftOneBatch076Neg40WeightUpper hpThetaJensenCellsBatch076_bounds hpThetaShiftOneBatch076Neg40_weight_bounds
  have hl : (-4979093 / 31250000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch076Lower j * hpThetaShiftOneBatch076Neg40WeightLower j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftOneBatch076Neg40WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftOneBatch076Neg40WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch076Lower j * hpThetaShiftOneBatch076Neg40WeightUpper j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftOneBatch076Neg40WeightUpper j) / 1600) ≤ (-3054239 / 20000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftOneBatch076Neg40WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1520 : ℝ) / 1600 = 76 / 80 by norm_num,
    show ((1520 : ℝ) + 20) / 1600 = (76 + 1) / 80 by norm_num] using hb

def hpThetaShiftOneBatch076Neg20WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (570492745349 / 1000000000000 : ℝ)
  | 1 => (114551611887 / 200000000000 : ℝ)
  | 2 => (575021410473 / 1000000000000 : ℝ)
  | 3 => (577282718779 / 1000000000000 : ℝ)
  | 4 => (579541904149 / 1000000000000 : ℝ)
  | 5 => (581798885857 / 1000000000000 : ℝ)
  | 6 => (73006697831 / 125000000000 : ℝ)
  | 7 => (293152956373 / 500000000000 : ℝ)
  | 8 => (294277896921 / 500000000000 : ℝ)
  | 9 => (295401571549 / 500000000000 : ℝ)
  | 10 => (74130984643 / 125000000000 : ℝ)
  | 11 => (297644956037 / 500000000000 : ℝ)
  | 12 => (119505832689 / 200000000000 : ℝ)
  | 13 => (299882773139 / 500000000000 : ℝ)
  | 14 => (12039979501 / 20000000000 : ℝ)
  | 15 => (37764335231 / 62500000000 : ℝ)
  | 16 => (75807078201 / 125000000000 : ℝ)
  | 17 => (608680673629 / 1000000000000 : ℝ)
  | 18 => (122180284011 / 200000000000 : ℝ)
  | 19 => (61311877663 / 100000000000 : ℝ)
  | _ => 0

def hpThetaShiftOneBatch076Neg20WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (143189514859 / 250000000000 : ℝ)
  | 1 => (287510705237 / 500000000000 : ℝ)
  | 2 => (28864135939 / 50000000000 : ℝ)
  | 3 => (11590838083 / 20000000000 : ℝ)
  | 4 => (290899442929 / 500000000000 : ℝ)
  | 5 => (584053582649 / 1000000000000 : ℝ)
  | 6 => (586305912747 / 1000000000000 : ℝ)
  | 7 => (588555793843 / 1000000000000 : ℝ)
  | 8 => (590803143099 / 1000000000000 : ℝ)
  | 9 => (118609575429 / 200000000000 : ℝ)
  | 10 => (23811596483 / 40000000000 : ℝ)
  | 11 => (298764581723 / 500000000000 : ℝ)
  | 12 => (599765546279 / 1000000000000 : ℝ)
  | 13 => (601998975051 / 1000000000000 : ℝ)
  | 14 => (604229363697 / 1000000000000 : ℝ)
  | 15 => (606456625609 / 1000000000000 : ℝ)
  | 16 => (60868067363 / 100000000000 : ℝ)
  | 17 => (76362677507 / 125000000000 : ℝ)
  | 18 => (613118776631 / 1000000000000 : ℝ)
  | 19 => (307666327273 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Check nine exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftOneBatch076Neg20_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1520 : ℝ) + (j.val : ℝ)) / 1600)
      (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftOneBatch076Neg20WeightLower j.val ≤ hpThetaJensenShiftOneWeight (-20) u ∧
      hpThetaJensenShiftOneWeight (-20) u ≤ hpThetaShiftOneBatch076Neg20WeightUpper j.val := by
  apply hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (-20) (((1520 : ℝ) + (j.val : ℝ)) / 1600)
    (((1520 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftOneBatch076Neg20WeightLower j.val) (hpThetaShiftOneBatch076Neg20WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftOneBatch076Neg20WeightLower, hpThetaShiftOneBatch076Neg20WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftOneBatch076Neg20_integral_bounds :
    (23060737 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ∧
    (∫ u : ℝ in Set.Ioo (76 / 80 : ℝ) ((76 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight (-20) u) ≤ (11952253 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftOne_batchIntegral_of_bounds (-20) (1520 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch076Lower hpThetaJensenCellsBatch076Upper
    hpThetaShiftOneBatch076Neg20WeightLower hpThetaShiftOneBatch076Neg20WeightUpper hpThetaJensenCellsBatch076_bounds hpThetaShiftOneBatch076Neg20_weight_bounds
  have hl : (23060737 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch076Lower j * hpThetaShiftOneBatch076Neg20WeightLower j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftOneBatch076Neg20WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftOneBatch076Neg20WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch076Lower j * hpThetaShiftOneBatch076Neg20WeightUpper j)
        (hpThetaJensenCellsBatch076Upper j * hpThetaShiftOneBatch076Neg20WeightUpper j) / 1600) ≤ (11952253 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch076Lower, hpThetaJensenCellsBatch076Upper,
      hpThetaShiftOneBatch076Neg20WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1520 : ℝ) / 1600 = 76 / 80 by norm_num,
    show ((1520 : ℝ) + 20) / 1600 = (76 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftOneBatch076Neg100_integral_bounds
#print axioms hpThetaShiftOneBatch076Neg65_integral_bounds
#print axioms hpThetaShiftOneBatch076Neg40_integral_bounds
#print axioms hpThetaShiftOneBatch076Neg20_integral_bounds
end HodgeProofHP
