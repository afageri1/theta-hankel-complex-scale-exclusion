#!/usr/bin/env bash
set -euo pipefail

command -v lake >/dev/null || {
  echo "ERROR: lake is not available."
  exit 1
}

lake build HodgeProofHP.Stage4ThetaZeroMomentCertificate
lake build HodgeProofHP.Stage4ThetaPhiZeroMomentPositive

target="HodgeProofHP/Stage4ThetaTraceRemainingBound.lean"

if [ -f "$target" ]; then
  cp "$target" "$target.before_create_$(date +%Y%m%d_%H%M%S)_$$"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaZeroMomentCertificate
import HodgeProofHP.Stage4ThetaPhiZeroMomentPositive

/-!
The numerical first-trace obstruction reduces to one remaining
upper bound on the second moment. That bound is an explicit
hypothesis here; this module does not certify it.
-/

namespace HodgeProofHP

theorem hpThetaTrace_secondMoment_lt_scaled_zeroMoment_of_upper
    (hM2 : hpThetaPhiMomentTwo < (27 / 1000 : ℝ)) :
    hpThetaPhiMomentTwo <
      (3 / 50 : ℝ) * hpThetaPhiMomentZero := by
  have hM0 := hpThetaPhiMomentZero_gt_nine_twentieths
  linarith

theorem hpThetaXiMomentRatio_lt_three_hundredths_of_secondMoment_upper
    (hM2 : hpThetaPhiMomentTwo < (27 / 1000 : ℝ)) :
    hpThetaXiMomentRatio < (3 / 100 : ℝ) := by
  have hM0 := hpThetaPhiMomentZero_gt_nine_twentieths
  have hden : 0 < 2 * hpThetaPhiMomentZero := by
    linarith
  unfold hpThetaXiMomentRatio
  apply (div_lt_iff₀ hden).2
  linarith

theorem hpThetaFirstTraceEnergy_ne_momentRatio_of_secondMoment_upper
    (hM2 : hpThetaPhiMomentTwo < (27 / 1000 : ℝ)) :
    hpThetaFirstTraceEnergy ≠ hpThetaXiMomentRatio := by
  have hE := hpThetaFirstTraceEnergy_gt_seven_hundredths
  have hR :=
    hpThetaXiMomentRatio_lt_three_hundredths_of_secondMoment_upper hM2
  intro h
  linarith

theorem hpThetaFirstTraceEnergy_ne_xiRatio_of_secondMoment_upper
    (hM2 : hpThetaPhiMomentTwo < (27 / 1000 : ℝ)) :
    hpThetaFirstTraceEnergy ≠
      -(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re) := by
  exact hpThetaTrace_energy_ne_xi_ratio_of_two_bounds
    (hpThetaTrace_secondMoment_lt_scaled_zeroMoment_of_upper hM2)
    hpThetaFirstTraceEnergy_gt_seven_hundredths

#print hpThetaFirstTraceEnergy_ne_momentRatio_of_secondMoment_upper

#print axioms hpThetaTrace_secondMoment_lt_scaled_zeroMoment_of_upper
#print axioms hpThetaXiMomentRatio_lt_three_hundredths_of_secondMoment_upper
#print axioms hpThetaFirstTraceEnergy_ne_momentRatio_of_secondMoment_upper
#print axioms hpThetaFirstTraceEnergy_ne_xiRatio_of_secondMoment_upper

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaTraceRemainingBound

echo "PASS: Stage4ThetaTraceRemainingBound"
