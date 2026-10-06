import HodgeProofHP.Stage4ThetaPhiSecondIntegralDerivative

/-!
Connect the first-trace moment ratio to the second derivative of Ξ.
The separation result remains conditional on explicit moment and energy bounds.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpThetaPhiMomentTwo_eq_neg_xi_secondDeriv_re :
    hpThetaPhiMomentTwo =
      -(deriv (deriv hpRiemannXiCritical) 0).re := by
  rw [hpRiemannXiCritical_secondDeriv_zero_re]
  simp

theorem hpThetaXiMomentRatio_eq_xi_secondDeriv_re_ratio :
    hpThetaXiMomentRatio =
      -(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re) := by
  unfold hpThetaXiMomentRatio
  rw [hpRiemannXiCritical_secondDeriv_zero_re]
  rw [← hpThetaPhiMomentZero_eq_xi_zero_re]
  simp

theorem hpThetaXiMomentRatio_cast_eq_xi_secondDeriv_ratio :
    (hpThetaXiMomentRatio : ℂ) =
      -deriv (deriv hpRiemannXiCritical) 0 /
        (2 * hpRiemannXiCritical 0) := by
  rw [← hpThetaPhiMomentZero_cast_eq_xi_zero,
    hpRiemannXiCritical_secondDeriv_zero_eq_moment]
  unfold hpThetaXiMomentRatio
  push_cast
  simp

theorem hpThetaFirstTraceEnergy_ne_xi_secondDeriv_ratio_of_bounds
    (hzero : 0 < hpThetaPhiMomentZero)
    (htwo :
      hpThetaPhiMomentTwo < (3 / 50 : ℝ) * hpThetaPhiMomentZero)
    (henergy : (7 / 100 : ℝ) < hpThetaFirstTraceEnergy) :
    hpThetaFirstTraceEnergy ≠
      -(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re) := by
  rw [← hpThetaXiMomentRatio_eq_xi_secondDeriv_re_ratio]
  exact hpThetaFirstTraceEnergy_ne_ratio_of_bounds
    hzero htwo henergy

#print axioms hpThetaPhiMomentTwo_eq_neg_xi_secondDeriv_re
#print axioms hpThetaXiMomentRatio_eq_xi_secondDeriv_re_ratio
#print axioms hpThetaXiMomentRatio_cast_eq_xi_secondDeriv_ratio
#print axioms hpThetaFirstTraceEnergy_ne_xi_secondDeriv_ratio_of_bounds

end HodgeProofHP
