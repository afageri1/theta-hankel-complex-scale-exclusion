import HodgeProofHP.Stage5ThetaJensenFiniteIntegralBounds
import HodgeProofHP.Stage5ThetaJensenTailNumericBounds
import HodgeProofHP.Stage5ThetaJensenMomentBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Unconditional certified quadratic Jensen moment inequality

Combine the finite integral certificates with the proved tail bounds.
The numerical bounds imply a strictly positive moment gap, and hence
an unconditional real root for the degree-two, shift-zero Jensen polynomial.
This finite result does not assert the Riemann hypothesis.
-/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

theorem hpThetaJensen_fullIntegral_split
    (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (∫ u : ℝ in Set.Ioi 0, u ^ m * hpRiemannThetaDifferentialKernel u) =
      (∫ u : ℝ in Set.Ioo 0 1, u ^ m * hpRiemannThetaDifferentialKernel u) +
      (∫ u : ℝ in Set.Ioi 1, u ^ m * hpRiemannThetaDifferentialKernel u) := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi
    (hpThetaJensen_powerIntegrand_integrableOn m hm) (show (0 : ℝ) ≤ 1 by norm_num)
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] at h
  linarith

theorem hpThetaJensen_tailIntegral_nonneg (m : ℕ) :
    0 ≤ ∫ u : ℝ in Set.Ioi 1, u ^ m * hpRiemannThetaDifferentialKernel u := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := by
    change (1 : ℝ) < u at hu
    linarith
  exact mul_nonneg (pow_nonneg hu0 m)
    (le_of_lt (hpThetaPhi_pos_on_nonnegative u hu0))

theorem hpThetaJensen_momentZero_le_certified :
    hpThetaPhiMomentZero ≤ (501 / 1000 : ℝ) := by
  have hfin := hpThetaJensen_finiteIntegral_numeric_bounds.1
  have htail := hpThetaJensen_zeroMoment_tail_le_twoEminusEight
  have hsplit := hpThetaJensen_fullIntegral_split 0 (Or.inl rfl)
  simp only [pow_zero, one_mul] at hfin hsplit
  change (∫ u : ℝ in Set.Ioi 0, hpRiemannThetaDifferentialKernel u) ≤ 501 / 1000
  linarith

theorem hpThetaJensen_momentTwo_ge_certified :
    (227 / 10000 : ℝ) ≤ hpThetaPhiMomentTwo := by
  have hfin := hpThetaJensen_finiteIntegral_numeric_bounds.2.1
  have htail := hpThetaJensen_tailIntegral_nonneg 2
  have hsplit := hpThetaJensen_fullIntegral_split 2 (Or.inr (Or.inl rfl))
  unfold hpThetaPhiMomentTwo
  linarith

theorem hpThetaJensen_momentFour_le_certified :
    hpThetaPhiMomentFour ≤ (3 / 1000 : ℝ) := by
  have hfin := hpThetaJensen_finiteIntegral_numeric_bounds.2.2
  have htail := hpThetaJensen_fourthMoment_tail_le_twoEminusEight
  have hsplit := hpThetaJensen_fullIntegral_split 4 (Or.inr (Or.inr rfl))
  unfold hpThetaPhiMomentFour
  linarith

theorem hpThetaJensen_momentGap_ge_certified :
    (4287 / 100000000 : ℝ) ≤
      3 * hpThetaPhiMomentTwo ^ 2 - hpThetaPhiMomentZero * hpThetaPhiMomentFour := by
  have h0 := hpThetaJensen_momentZero_le_certified
  have h2 := hpThetaJensen_momentTwo_ge_certified
  have h4 := hpThetaJensen_momentFour_le_certified
  have hprod : hpThetaPhiMomentZero * hpThetaPhiMomentFour ≤
      (501 / 1000 : ℝ) * (3 / 1000 : ℝ) :=
    mul_le_mul h0 h4 (le_of_lt hpThetaJensen_fourthMoment_pos) (by norm_num)
  have hsq : (227 / 10000 : ℝ) ^ 2 ≤ hpThetaPhiMomentTwo ^ 2 := by
    nlinarith [sq_nonneg (hpThetaPhiMomentTwo - (227 / 10000 : ℝ))]
  nlinarith

theorem hpThetaJensen_moment_inequality_strict :
    hpThetaPhiMomentZero * hpThetaPhiMomentFour <
      3 * hpThetaPhiMomentTwo ^ 2 := by
  have h := hpThetaJensen_momentGap_ge_certified
  linarith

theorem hpThetaJensen_moment_inequality :
    hpThetaPhiMomentZero * hpThetaPhiMomentFour ≤
      3 * hpThetaPhiMomentTwo ^ 2 :=
  le_of_lt hpThetaJensen_moment_inequality_strict

theorem hpThetaJensenQuadratic_zero_discriminant_pos :
    0 < hpThetaJensenQuadraticDiscriminant 0 := by
  rw [hpThetaJensenQuadraticDiscriminant_zero_eq_stage4]
  have h := hpThetaJensen_moment_inequality_strict
  linarith

theorem hpThetaJensenQuadratic_zero_exists_real_root :
    ∃ x : ℝ, (hpThetaJensenPolynomial 2 0).eval x = 0 :=
  hpThetaJensenQuadratic_zero_real_root_iff_stage4_moments.mpr
    hpThetaJensen_moment_inequality

theorem hpThetaJensenQuadratic_zero_rootPlus_certified :
    (hpThetaJensenPolynomial 2 0).eval (hpThetaJensenQuadraticRootPlus 0) = 0 :=
  hpThetaJensenQuadratic_zero_rootPlus_of_stage4_moments hpThetaJensen_moment_inequality

#print axioms hpThetaJensen_fullIntegral_split
#print axioms hpThetaJensen_tailIntegral_nonneg
#print axioms hpThetaJensen_momentZero_le_certified
#print axioms hpThetaJensen_momentTwo_ge_certified
#print axioms hpThetaJensen_momentFour_le_certified
#print axioms hpThetaJensen_momentGap_ge_certified
#print axioms hpThetaJensen_moment_inequality_strict
#print axioms hpThetaJensen_moment_inequality
#print axioms hpThetaJensenQuadratic_zero_discriminant_pos
#print axioms hpThetaJensenQuadratic_zero_exists_real_root
#print axioms hpThetaJensenQuadratic_zero_rootPlus_certified
end HodgeProofHP
