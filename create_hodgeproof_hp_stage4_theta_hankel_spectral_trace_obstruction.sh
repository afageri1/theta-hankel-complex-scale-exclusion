#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSpectralTrace

target="HodgeProofHP/Stage4ThetaHankelSpectralTraceObstruction.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSpectralTrace
import HodgeProofHP.Stage4ThetaFirstTraceObstruction

/-!
The first-trace obstruction expressed through the eigenvalue sum
and the Hilbert-basis trace of the theta Hankel adjoint square.
This concerns the current normalization and assumes no determinant.
-/

namespace HodgeProofHP

theorem hpThetaHankelSpectralSum_re_ne_momentRatio :
    (∑' i : HPThetaHankelSpectralIndex, i.1.re) ≠
      hpThetaXiMomentRatio := by
  rw [hpThetaHankelSpectralValues_re_tsum]
  exact hpThetaFirstTraceEnergy_ne_momentRatio

theorem hpThetaHankelSpectralSum_re_ne_xiRatio :
    (∑' i : HPThetaHankelSpectralIndex, i.1.re) ≠
      -(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re) := by
  rw [hpThetaHankelSpectralValues_re_tsum]
  exact hpThetaFirstTraceEnergy_ne_xi_secondDeriv_ratio

theorem hpThetaHankelSpectralSum_ne_cast_xiRatio :
    (∑' i : HPThetaHankelSpectralIndex, i.1) ≠
      ((-(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re) : ℝ) : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  rw [hpThetaHankelSpectralValues_tsum] at hre
  simp only [Complex.ofReal_re] at hre
  exact hpThetaFirstTraceEnergy_ne_xi_secondDeriv_ratio hre

theorem hpThetaHankelSpectralTrace_re_ne_xiRatio :
    (hpThetaHankelBasisTrace hpThetaHankelSpectralBasis
      hpThetaHankelAdjointSquare).re ≠
      -(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re) := by
  rw [hpThetaHankelSpectralBasisTrace_eq_energy]
  simp only [Complex.ofReal_re]
  exact hpThetaFirstTraceEnergy_ne_xi_secondDeriv_ratio

#print axioms hpThetaHankelSpectralSum_re_ne_momentRatio
#print axioms hpThetaHankelSpectralSum_re_ne_xiRatio
#print axioms hpThetaHankelSpectralSum_ne_cast_xiRatio
#print axioms hpThetaHankelSpectralTrace_re_ne_xiRatio

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelSpectralTraceObstruction

printf '%s\n' 'PASS: Stage4ThetaHankelSpectralTraceObstruction'
