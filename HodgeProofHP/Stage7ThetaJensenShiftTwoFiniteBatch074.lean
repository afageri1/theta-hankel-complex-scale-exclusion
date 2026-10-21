/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoBernstein
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage5ThetaJensenCellsBatch074

/-! Exact signed weight and batch integral certificates, batch 74 of 80. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBatch074Neg100WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-3578057502551 / 500000000000 : ℝ)
  | 1 => (-7213631705937 / 1000000000000 : ℝ)
  | 2 => (-727155282317 / 100000000000 : ℝ)
  | 3 => (-7329880822349 / 1000000000000 : ℝ)
  | 4 => (-3694309090943 / 500000000000 : ℝ)
  | 5 => (-3723883696557 / 500000000000 : ℝ)
  | 6 => (-7507330960343 / 1000000000000 : ℝ)
  | 7 => (-7567311400917 / 1000000000000 : ℝ)
  | 8 => (-762771124527 / 100000000000 : ℝ)
  | 9 => (-1537706607397 / 200000000000 : ℝ)
  | 10 => (-154995586657 / 20000000000 : ℝ)
  | 11 => (-1562290540583 / 200000000000 : ℝ)
  | 12 => (-984194466319 / 125000000000 : ℝ)
  | 13 => (-248002844141 / 31250000000 : ℝ)
  | 14 => (-7999061158983 / 1000000000000 : ℝ)
  | 15 => (-8062468793647 / 1000000000000 : ℝ)
  | 16 => (-8126316553743 / 1000000000000 : ℝ)
  | 17 => (-8190607090119 / 1000000000000 : ℝ)
  | 18 => (-82553430673 / 10000000000 : ℝ)
  | 19 => (-4160263581769 / 500000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch074Neg100WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-7099000267923 / 1000000000000 : ℝ)
  | 1 => (-7156115005101 / 1000000000000 : ℝ)
  | 2 => (-450851981621 / 62500000000 : ℝ)
  | 3 => (-7271552823169 / 1000000000000 : ℝ)
  | 4 => (-1832470205587 / 250000000000 : ℝ)
  | 5 => (-1477723636377 / 200000000000 : ℝ)
  | 6 => (-7447767393113 / 1000000000000 : ℝ)
  | 7 => (-3753665480171 / 500000000000 : ℝ)
  | 8 => (-1891827850229 / 250000000000 : ℝ)
  | 9 => (-7627711245269 / 1000000000000 : ℝ)
  | 10 => (-961066629623 / 125000000000 : ℝ)
  | 11 => (-7749779332849 / 1000000000000 : ℝ)
  | 12 => (-3905726351457 / 500000000000 : ℝ)
  | 13 => (-7873555730551 / 1000000000000 : ℝ)
  | 14 => (-7936091012511 / 1000000000000 : ℝ)
  | 15 => (-3999530579491 / 500000000000 : ℝ)
  | 16 => (-4031234396823 / 500000000000 : ℝ)
  | 17 => (-4063158276871 / 500000000000 : ℝ)
  | 18 => (-4095303545059 / 500000000000 : ℝ)
  | 19 => (-8255343067299 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch074Neg100_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1480 : ℝ) + (j.val : ℝ)) / 1600)
      (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch074Neg100WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-100) u ∧
      hpThetaJensenShiftTwoWeight (-100) u ≤ hpThetaShiftTwoBatch074Neg100WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-100) (((1480 : ℝ) + (j.val : ℝ)) / 1600)
    (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch074Neg100WeightLower j.val) (hpThetaShiftTwoBatch074Neg100WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch074Neg100WeightLower, hpThetaShiftTwoBatch074Neg100WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch074Neg100_integral_bounds :
    (-777191179 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ∧
    (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-100) u) ≤ (-747627779 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-100) (1480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch074Lower hpThetaJensenCellsBatch074Upper
    hpThetaShiftTwoBatch074Neg100WeightLower hpThetaShiftTwoBatch074Neg100WeightUpper hpThetaJensenCellsBatch074_bounds hpThetaShiftTwoBatch074Neg100_weight_bounds
  have hl : (-777191179 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch074Lower j * hpThetaShiftTwoBatch074Neg100WeightLower j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftTwoBatch074Neg100WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftTwoBatch074Neg100WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch074Lower j * hpThetaShiftTwoBatch074Neg100WeightUpper j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftTwoBatch074Neg100WeightUpper j) / 1600) ≤ (-747627779 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftTwoBatch074Neg100WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1480 : ℝ) / 1600 = 74 / 80 by norm_num,
    show ((1480 : ℝ) + 20) / 1600 = (74 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch074Neg65WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-1088154900923 / 1000000000000 : ℝ)
  | 1 => (-137315137289 / 125000000000 : ℝ)
  | 2 => (-1108969732677 / 1000000000000 : ℝ)
  | 3 => (-1119501354729 / 1000000000000 : ℝ)
  | 4 => (-565058259129 / 500000000000 : ℝ)
  | 5 => (-1140815780143 / 1000000000000 : ℝ)
  | 6 => (-1151599700371 / 1000000000000 : ℝ)
  | 7 => (-18163575657 / 15625000000 : ℝ)
  | 8 => (-234684754283 / 200000000000 : ℝ)
  | 9 => (-1184465057861 / 1000000000000 : ℝ)
  | 10 => (-1195593273939 / 1000000000000 : ℝ)
  | 11 => (-1206808995379 / 1000000000000 : ℝ)
  | 12 => (-76132050069 / 62500000000 : ℝ)
  | 13 => (-1229505273243 / 1000000000000 : ℝ)
  | 14 => (-310246749287 / 250000000000 : ℝ)
  | 15 => (-250511712281 / 200000000000 : ℝ)
  | 16 => (-632110278927 / 500000000000 : ℝ)
  | 17 => (-1594966977 / 1250000000 : ℝ)
  | 18 => (-1287818231027 / 1000000000000 : ℝ)
  | 19 => (-1299755107817 / 1000000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch074Neg65WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-538935296429 / 500000000000 : ℝ)
  | 1 => (-544077450461 / 500000000000 : ℝ)
  | 2 => (-1098521098311 / 1000000000000 : ℝ)
  | 3 => (-277242433169 / 250000000000 : ℝ)
  | 4 => (-139937669341 / 125000000000 : ℝ)
  | 5 => (-1130116518257 / 1000000000000 : ℝ)
  | 6 => (-570407890071 / 500000000000 : ℝ)
  | 7 => (-115159970037 / 100000000000 : ℝ)
  | 8 => (-1162468842047 / 1000000000000 : ℝ)
  | 9 => (-586711885707 / 500000000000 : ℝ)
  | 10 => (-59223252893 / 50000000000 : ℝ)
  | 11 => (-597796636969 / 500000000000 : ℝ)
  | 12 => (-603404497689 / 500000000000 : ℝ)
  | 13 => (-1218112801103 / 1000000000000 : ℝ)
  | 14 => (-614752636621 / 500000000000 : ℝ)
  | 15 => (-1240986997147 / 1000000000000 : ℝ)
  | 16 => (-313139640351 / 250000000000 : ℝ)
  | 17 => (-1264220557853 / 1000000000000 : ℝ)
  | 18 => (-1275973581599 / 1000000000000 : ℝ)
  | 19 => (-643909115513 / 500000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch074Neg65_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1480 : ℝ) + (j.val : ℝ)) / 1600)
      (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch074Neg65WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-65) u ∧
      hpThetaJensenShiftTwoWeight (-65) u ≤ hpThetaShiftTwoBatch074Neg65WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-65) (((1480 : ℝ) + (j.val : ℝ)) / 1600)
    (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch074Neg65WeightLower j.val) (hpThetaShiftTwoBatch074Neg65WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch074Neg65WeightLower, hpThetaShiftTwoBatch074Neg65WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch074Neg65_integral_bounds :
    (-29931493 / 250000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ∧
    (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-65) u) ≤ (-115007769 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-65) (1480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch074Lower hpThetaJensenCellsBatch074Upper
    hpThetaShiftTwoBatch074Neg65WeightLower hpThetaShiftTwoBatch074Neg65WeightUpper hpThetaJensenCellsBatch074_bounds hpThetaShiftTwoBatch074Neg65_weight_bounds
  have hl : (-29931493 / 250000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch074Lower j * hpThetaShiftTwoBatch074Neg65WeightLower j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftTwoBatch074Neg65WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftTwoBatch074Neg65WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch074Lower j * hpThetaShiftTwoBatch074Neg65WeightUpper j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftTwoBatch074Neg65WeightUpper j) / 1600) ≤ (-115007769 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftTwoBatch074Neg65WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1480 : ℝ) / 1600 = 74 / 80 by norm_num,
    show ((1480 : ℝ) + 20) / 1600 = (74 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch074Neg45WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (-89063740401 / 1000000000000 : ℝ)
  | 1 => (-90641711597 / 1000000000000 : ℝ)
  | 2 => (-92236495787 / 1000000000000 : ℝ)
  | 3 => (-3753929069 / 40000000000 : ℝ)
  | 4 => (-47738519501 / 500000000000 : ℝ)
  | 5 => (-24280767013 / 250000000000 : ℝ)
  | 6 => (-19757290031 / 200000000000 : ℝ)
  | 7 => (-2511683061 / 25000000000 : ℝ)
  | 8 => (-51082911447 / 500000000000 : ℝ)
  | 9 => (-103882090361 / 1000000000000 : ℝ)
  | 10 => (-26404066137 / 250000000000 : ℝ)
  | 11 => (-107368486031 / 1000000000000 : ℝ)
  | 12 => (-109138896257 / 1000000000000 : ℝ)
  | 13 => (-2218552751 / 20000000000 : ℝ)
  | 14 => (-112734853113 / 1000000000000 : ℝ)
  | 15 => (-22912137407 / 200000000000 : ℝ)
  | 16 => (-23281056859 / 200000000000 : ℝ)
  | 17 => (-23653758153 / 200000000000 : ℝ)
  | 18 => (-60075676607 / 500000000000 : ℝ)
  | 19 => (-24410623863 / 200000000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch074Neg45WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (-136722577 / 1562500000 : ℝ)
  | 1 => (-222659351 / 2500000000 : ℝ)
  | 2 => (-22660427899 / 250000000000 : ℝ)
  | 3 => (-46118247893 / 500000000000 : ℝ)
  | 4 => (-23462056681 / 250000000000 : ℝ)
  | 5 => (-95477039001 / 1000000000000 : ℝ)
  | 6 => (-97123068051 / 1000000000000 : ℝ)
  | 7 => (-49393225077 / 500000000000 : ℝ)
  | 8 => (-100467322439 / 1000000000000 : ℝ)
  | 9 => (-102165822893 / 1000000000000 : ℝ)
  | 10 => (-2597052259 / 25000000000 : ℝ)
  | 11 => (-105616264547 / 1000000000000 : ℝ)
  | 12 => (-10736848603 / 100000000000 : ℝ)
  | 13 => (-852647627 / 7812500000 : ℝ)
  | 14 => (-110927637549 / 1000000000000 : ℝ)
  | 15 => (-14091856639 / 125000000000 : ℝ)
  | 16 => (-57280343517 / 500000000000 : ℝ)
  | 17 => (-58202642147 / 500000000000 : ℝ)
  | 18 => (-29567197691 / 250000000000 : ℝ)
  | 19 => (-120151353213 / 1000000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch074Neg45_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1480 : ℝ) + (j.val : ℝ)) / 1600)
      (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch074Neg45WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-45) u ∧
      hpThetaJensenShiftTwoWeight (-45) u ≤ hpThetaShiftTwoBatch074Neg45WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-45) (((1480 : ℝ) + (j.val : ℝ)) / 1600)
    (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch074Neg45WeightLower j.val) (hpThetaShiftTwoBatch074Neg45WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch074Neg45WeightLower, hpThetaShiftTwoBatch074Neg45WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch074Neg45_integral_bounds :
    (-10499243 / 1000000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ∧
    (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-45) u) ≤ (-5006057 / 500000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-45) (1480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch074Lower hpThetaJensenCellsBatch074Upper
    hpThetaShiftTwoBatch074Neg45WeightLower hpThetaShiftTwoBatch074Neg45WeightUpper hpThetaJensenCellsBatch074_bounds hpThetaShiftTwoBatch074Neg45_weight_bounds
  have hl : (-10499243 / 1000000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch074Lower j * hpThetaShiftTwoBatch074Neg45WeightLower j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftTwoBatch074Neg45WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftTwoBatch074Neg45WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch074Lower j * hpThetaShiftTwoBatch074Neg45WeightUpper j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftTwoBatch074Neg45WeightUpper j) / 1600) ≤ (-5006057 / 500000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftTwoBatch074Neg45WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1480 : ℝ) / 1600 = 74 / 80 by norm_num,
    show ((1480 : ℝ) + 20) / 1600 = (74 + 1) / 80 by norm_num] using hb

def hpThetaShiftTwoBatch074Neg25WeightLower (j : ℕ) : ℝ :=
  match j with
  | 0 => (3841421997 / 125000000000 : ℝ)
  | 1 => (6188343971 / 200000000000 : ℝ)
  | 2 => (3115258829 / 100000000000 : ℝ)
  | 3 => (31363976509 / 1000000000000 : ℝ)
  | 4 => (3946984959 / 125000000000 : ℝ)
  | 5 => (7947073217 / 250000000000 : ℝ)
  | 6 => (16000605557 / 500000000000 : ℝ)
  | 7 => (32214629359 / 1000000000000 : ℝ)
  | 8 => (32428542477 / 1000000000000 : ℝ)
  | 9 => (16321472637 / 500000000000 : ℝ)
  | 10 => (32857832481 / 1000000000000 : ℝ)
  | 11 => (8268299689 / 250000000000 : ℝ)
  | 12 => (6657807737 / 200000000000 : ℝ)
  | 13 => (16752673389 / 500000000000 : ℝ)
  | 14 => (33722117473 / 1000000000000 : ℝ)
  | 15 => (3393934513 / 100000000000 : ℝ)
  | 16 => (8539256009 / 250000000000 : ℝ)
  | 17 => (17187574201 / 500000000000 : ℝ)
  | 18 => (864842809 / 25000000000 : ℝ)
  | 19 => (2175794373 / 62500000000 : ℝ)
  | _ => 0

def hpThetaShiftTwoBatch074Neg25WeightUpper (j : ℕ) : ℝ :=
  match j with
  | 0 => (1933857491 / 62500000000 : ℝ)
  | 1 => (31152588291 / 1000000000000 : ℝ)
  | 2 => (3136397651 / 100000000000 : ℝ)
  | 3 => (31575879673 / 1000000000000 : ℝ)
  | 4 => (31788292869 / 1000000000000 : ℝ)
  | 5 => (6400242223 / 200000000000 : ℝ)
  | 6 => (402682867 / 12500000000 : ℝ)
  | 7 => (16214271239 / 500000000000 : ℝ)
  | 8 => (1305717811 / 40000000000 : ℝ)
  | 9 => (16428916241 / 500000000000 : ℝ)
  | 10 => (33073198757 / 1000000000000 : ℝ)
  | 11 => (16644519343 / 500000000000 : ℝ)
  | 12 => (33505346779 / 1000000000000 : ℝ)
  | 13 => (16861058737 / 500000000000 : ℝ)
  | 14 => (33939345131 / 1000000000000 : ℝ)
  | 15 => (34157024037 / 1000000000000 : ℝ)
  | 16 => (34375148403 / 1000000000000 : ℝ)
  | 17 => (34593712361 / 1000000000000 : ℝ)
  | 18 => (34812709969 / 1000000000000 : ℝ)
  | 19 => (7006427041 / 200000000000 : ℝ)
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Check eleven exact coefficients for each of the twenty rational cells.
theorem hpThetaShiftTwoBatch074Neg25_weight_bounds (j : Fin 20) (u : ℝ)
    (hu : u ∈ Set.Icc (((1480 : ℝ) + (j.val : ℝ)) / 1600)
      (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600)) :
    hpThetaShiftTwoBatch074Neg25WeightLower j.val ≤ hpThetaJensenShiftTwoWeight (-25) u ∧
      hpThetaJensenShiftTwoWeight (-25) u ≤ hpThetaShiftTwoBatch074Neg25WeightUpper j.val := by
  apply hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (-25) (((1480 : ℝ) + (j.val : ℝ)) / 1600)
    (((1480 : ℝ) + (j.val : ℝ) + 1) / 1600) u
    (hpThetaShiftTwoBatch074Neg25WeightLower j.val) (hpThetaShiftTwoBatch074Neg25WeightUpper j.val) (by linarith) hu
  intro k
  fin_cases j <;> fin_cases k <;>
    norm_num [hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
      Finset.sum_range_succ, Nat.choose, hpThetaShiftTwoBatch074Neg25WeightLower, hpThetaShiftTwoBatch074Neg25WeightUpper]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Verify the twenty signed rational products and rounded batch endpoints.
theorem hpThetaShiftTwoBatch074Neg25_integral_bounds :
    (319841 / 100000000000000 : ℝ) ≤ (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ∧
    (∫ u : ℝ in Set.Ioo (74 / 80 : ℝ) ((74 + 1) / 80 : ℝ),
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight (-25) u) ≤ (3320301 / 1000000000000000 : ℝ) := by
  have h := hpThetaJensenShiftTwo_batchIntegral_of_bounds (-25) (1480 : ℝ)
    (by norm_num) hpThetaJensenCellsBatch074Lower hpThetaJensenCellsBatch074Upper
    hpThetaShiftTwoBatch074Neg25WeightLower hpThetaShiftTwoBatch074Neg25WeightUpper hpThetaJensenCellsBatch074_bounds hpThetaShiftTwoBatch074Neg25_weight_bounds
  have hl : (319841 / 100000000000000 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      min (hpThetaJensenCellsBatch074Lower j * hpThetaShiftTwoBatch074Neg25WeightLower j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftTwoBatch074Neg25WeightLower j) / 1600 := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftTwoBatch074Neg25WeightLower]
  have hu : (∑ j ∈ Finset.range 20,
      max (hpThetaJensenCellsBatch074Lower j * hpThetaShiftTwoBatch074Neg25WeightUpper j)
        (hpThetaJensenCellsBatch074Upper j * hpThetaShiftTwoBatch074Neg25WeightUpper j) / 1600) ≤ (3320301 / 1000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ, hpThetaJensenCellsBatch074Lower, hpThetaJensenCellsBatch074Upper,
      hpThetaShiftTwoBatch074Neg25WeightUpper]
  have hb := And.intro (le_trans hl h.1) (le_trans h.2 hu)
  simpa only [show (1480 : ℝ) / 1600 = 74 / 80 by norm_num,
    show ((1480 : ℝ) + 20) / 1600 = (74 + 1) / 80 by norm_num] using hb

#print axioms hpThetaShiftTwoBatch074Neg100_integral_bounds
#print axioms hpThetaShiftTwoBatch074Neg65_integral_bounds
#print axioms hpThetaShiftTwoBatch074Neg45_integral_bounds
#print axioms hpThetaShiftTwoBatch074Neg25_integral_bounds
end HodgeProofHP
