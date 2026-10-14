/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVWeightedTailCertifiedBounds
import HodgeProofHP.Stage7ThetaJensenWeightedTailDerivative

/-!
# Sharper upper bound for the actual CNV weighted tail

Retain the rational total of the existing 1600 kernel rectangles rather than
rounding it to 0.09. The tail beyond one contributes at most 1/50000000.
Nonnegativity of the integrand transfers the resulting 0.087 upper bound at
zero to every nonnegative argument. No global CNV positivity is asserted.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

theorem hpThetaCNV_weightedTailRectangle_upper_sharp :
    (∑ b ∈ Finset.range 80, hpThetaJensenWeightedTailRectangleUpper b) ≤
      (86936498921467 / 1000000000000000 : ℝ) := by
  have h : (∑ b ∈ Finset.range 80, hpThetaJensenWeightedTailRectangleUpper b) ≤
      ∑ b ∈ Finset.range 80, hpThetaJensenWeightedTailBatchUpper b := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensen_weighted_tailRectangleBatch_bounds
      ⟨b, Finset.mem_range.mp hb⟩).2
  rw [hpThetaJensenWeightedTailUpperPrefix080] at h
  exact h

theorem hpThetaCNV_weightedTailFiniteIntegral_upper_sharp :
    (∫ u : ℝ in Set.Ioo 0 1, u * hpRiemannThetaDifferentialKernel u) ≤
      (86936498921467 / 1000000000000000 : ℝ) := by
  have hupp :
      (∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          u ^ 1 * hpRiemannThetaDifferentialKernel u) ≤
      ∑ b ∈ Finset.range 80, hpThetaJensenWeightedTailRectangleUpper b := by
    apply Finset.sum_le_sum
    intro b hb
    exact (hpThetaJensen_weighted_tailBatchIntegral_bounds
      ⟨b, Finset.mem_range.mp hb⟩).2
  have hsum :
      (∑ b ∈ Finset.range 80,
        ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
          u ^ 1 * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo 0 1, u ^ 1 * hpRiemannThetaDifferentialKernel u := by
    have h := hpThetaJensen_natPowerUniformCellIntegral_sum 1 80 0
      (1 / 80) (by norm_num) (by norm_num)
    simpa only [zero_add, mul_one_div, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      show (80 : ℝ) / 80 = 1 by norm_num] using h
  rw [hsum] at hupp
  simpa only [pow_one] using hupp.trans hpThetaCNV_weightedTailRectangle_upper_sharp

theorem hpThetaPhiWeightedTail_zero_le_eightySeven_thousandths :
    hpThetaPhiWeightedTail 0 ≤ (87 / 1000 : ℝ) := by
  have hfin := hpThetaCNV_weightedTailFiniteIntegral_upper_sharp
  have htail := hpThetaCNV_weightedTail_at_one_le_twoEminusEight
  have hsplit := hpThetaCNV_weightedTail_zero_split
  linarith

theorem hpThetaPhiWeightedTail_le_at_zero (t : ℝ) (ht : 0 ≤ t) :
    hpThetaPhiWeightedTail t ≤ hpThetaPhiWeightedTail 0 := by
  have hnonneg : 0 ≤ ∫ u : ℝ in (0 : ℝ)..t,
      u * hpRiemannThetaDifferentialKernel u := by
    apply intervalIntegral.integral_nonneg ht
    intro u hu
    exact mul_nonneg hu.1 (hpThetaPhi_pos_on_nonnegative u hu.1).le
  rw [hpThetaPhiWeightedTail_eq_total_sub_integral t ht]
  linarith

theorem hpThetaPhiWeightedTail_le_eightySeven_thousandths (t : ℝ) (ht : 0 ≤ t) :
    hpThetaPhiWeightedTail t ≤ (87 / 1000 : ℝ) :=
  (hpThetaPhiWeightedTail_le_at_zero t ht).trans
    hpThetaPhiWeightedTail_zero_le_eightySeven_thousandths

theorem hpThetaPhiWeightedTail_bounds_eightySeven_thousandths
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ hpThetaPhiWeightedTail t ∧ hpThetaPhiWeightedTail t ≤ (87 / 1000 : ℝ) :=
  ⟨hpThetaPhiWeightedTail_nonneg t ht,
    hpThetaPhiWeightedTail_le_eightySeven_thousandths t ht⟩

#print axioms hpThetaCNV_weightedTailRectangle_upper_sharp
#print axioms hpThetaCNV_weightedTailFiniteIntegral_upper_sharp
#print axioms hpThetaPhiWeightedTail_zero_le_eightySeven_thousandths
#print axioms hpThetaPhiWeightedTail_le_at_zero
#print axioms hpThetaPhiWeightedTail_le_eightySeven_thousandths
#print axioms hpThetaPhiWeightedTail_bounds_eightySeven_thousandths
end HodgeProofHP
