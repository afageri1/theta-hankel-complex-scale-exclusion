import HodgeProofHP.Stage5ThetaJensenQuadraticConverse
import HodgeProofHP.Stage4ThetaPhiPositiveLowerBound
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Strict fourth-moment positivity and the shift-zero quadratic criterion

The actual theta kernel is strictly positive on the positive half-line.
Its integrable fourth-moment integrand has support containing that entire
half-line, so the fourth moment is strictly positive. This proves that
gamma(2) is positive and removes the nonzero-leading-coefficient hypothesis
from the shift-zero root-existence equivalence.

The moment inequality is still not proved here. This module does not
assert unconditional real-root existence or an equivalence with RH.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpThetaJensen_fourthMoment_pos :
    0 < hpThetaPhiMomentFour := by
  have hpos (u : ℝ) (hu : 0 < u) :
      0 < u ^ 4 * hpRiemannThetaDifferentialKernel u := by
    exact mul_pos (pow_pos hu 4)
      (hpThetaPhi_pos_on_nonnegative u (le_of_lt hu))
  have hnonneg :
      ∀ᵐ u ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        0 ≤ u ^ 4 * hpRiemannThetaDifferentialKernel u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact le_of_lt (hpos u hu)
  have hsupport :
      Function.support
          (fun u : ℝ => u ^ 4 * hpRiemannThetaDifferentialKernel u) ∩
          Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext u
    constructor
    · intro hu
      exact hu.2
    · intro hu
      refine ⟨?_, hu⟩
      change u ^ 4 * hpRiemannThetaDifferentialKernel u ≠ 0
      exact ne_of_gt (hpos u hu)
  unfold hpThetaPhiMomentFour
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    hnonneg hpThetaPhi_fourthMoment_integrableOn).mpr
  rw [hsupport]
  simp

theorem hpThetaJensen_fourthMoment_ne_zero :
    hpThetaPhiMomentFour ≠ 0 :=
  ne_of_gt hpThetaJensen_fourthMoment_pos

theorem hpThetaJensenGamma_two_pos :
    0 < hpThetaJensenGamma 2 := by
  rw [hpThetaJensenGamma_two]
  exact div_pos hpThetaJensen_fourthMoment_pos (by norm_num)

theorem hpThetaJensenGamma_two_ne_zero :
    hpThetaJensenGamma 2 ≠ 0 :=
  ne_of_gt hpThetaJensenGamma_two_pos

theorem hpThetaJensenQuadratic_zero_real_root_iff_moment_inequality :
    (∃ x : ℝ, (hpThetaJensenPolynomial 2 0).eval x = 0) ↔
      hpThetaPhiEvenMoment 0 * hpThetaPhiMomentFour ≤
        3 * hpThetaPhiEvenMoment 1 ^ 2 := by
  exact hpThetaJensenQuadratic_zero_exists_real_root_iff_moments
    hpThetaJensenGamma_two_ne_zero

theorem hpThetaJensenQuadratic_zero_rootPlus_of_moment_inequality
    (hM : hpThetaPhiEvenMoment 0 * hpThetaPhiMomentFour ≤
      3 * hpThetaPhiEvenMoment 1 ^ 2) :
    (hpThetaJensenPolynomial 2 0).eval
      (hpThetaJensenQuadraticRootPlus 0) = 0 := by
  exact hpThetaJensenQuadraticRootPlus_is_root 0
    hpThetaJensenGamma_two_ne_zero
    (hpThetaJensenQuadraticDiscriminant_zero_nonneg_iff.mpr hM)

#print axioms hpThetaJensen_fourthMoment_pos
#print axioms hpThetaJensen_fourthMoment_ne_zero
#print axioms hpThetaJensenGamma_two_pos
#print axioms hpThetaJensenGamma_two_ne_zero
#print axioms hpThetaJensenQuadratic_zero_real_root_iff_moment_inequality
#print axioms hpThetaJensenQuadratic_zero_rootPlus_of_moment_inequality

end HodgeProofHP
