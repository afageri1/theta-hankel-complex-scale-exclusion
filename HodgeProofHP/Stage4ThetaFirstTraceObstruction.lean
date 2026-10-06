import HodgeProofHP.Stage4ThetaProfileNumericUpperBound
import HodgeProofHP.Stage4ThetaTraceRemainingBound

/-!
Unconditional separation of the theta Hankel kernel energy
from the second-derivative ratio of the Riemann Xi function.

This module proves a scalar obstruction. It does not identify
the energy with an operator trace or construct a Fredholm determinant.
-/

namespace HodgeProofHP

theorem hpThetaTrace_secondMoment_lt_scaled_zeroMoment :
    hpThetaPhiMomentTwo <
      (3 / 50 : ℝ) * hpThetaPhiMomentZero := by
  have hM0 := hpThetaPhiMomentZero_gt_nine_twentieths
  have hM2 := hpThetaPhiMomentTwo_lt_twentySeven_thousandths
  linarith

theorem hpThetaXiMomentRatio_lt_three_hundredths :
    hpThetaXiMomentRatio < (3 / 100 : ℝ) :=
  hpThetaXiMomentRatio_lt_three_hundredths_of_secondMoment_upper
    hpThetaPhiMomentTwo_lt_twentySeven_thousandths

theorem hpThetaFirstTraceEnergy_gt_momentRatio :
    hpThetaXiMomentRatio < hpThetaFirstTraceEnergy := by
  have hR := hpThetaXiMomentRatio_lt_three_hundredths
  have hE := hpThetaFirstTraceEnergy_gt_seven_hundredths
  linarith

theorem hpThetaFirstTraceEnergy_ne_momentRatio :
    hpThetaFirstTraceEnergy ≠ hpThetaXiMomentRatio :=
  hpThetaFirstTraceEnergy_ne_momentRatio_of_secondMoment_upper
    hpThetaPhiMomentTwo_lt_twentySeven_thousandths

theorem hpThetaFirstTraceEnergy_ne_xi_secondDeriv_ratio :
    hpThetaFirstTraceEnergy ≠
      -(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re) := by
  have hzero : 0 < hpThetaPhiMomentZero := by
    have h := hpThetaPhiMomentZero_gt_nine_twentieths
    linarith
  exact hpThetaFirstTraceEnergy_ne_xi_secondDeriv_ratio_of_bounds
    hzero
    hpThetaTrace_secondMoment_lt_scaled_zeroMoment
    hpThetaFirstTraceEnergy_gt_seven_hundredths

#print axioms hpThetaTrace_secondMoment_lt_scaled_zeroMoment
#print axioms hpThetaXiMomentRatio_lt_three_hundredths
#print axioms hpThetaFirstTraceEnergy_gt_momentRatio
#print axioms hpThetaFirstTraceEnergy_ne_momentRatio
#print axioms hpThetaFirstTraceEnergy_ne_xi_secondDeriv_ratio

end HodgeProofHP
