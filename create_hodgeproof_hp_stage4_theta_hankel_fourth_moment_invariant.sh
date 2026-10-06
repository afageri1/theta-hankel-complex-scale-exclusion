#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaPhiFourthIntegralDerivative
lake build HodgeProofHP.Stage4ThetaNormalizedXiFourthDerivative

target="HodgeProofHP/Stage4ThetaHankelFourthMomentInvariant.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaPhiFourthIntegralDerivative
import HodgeProofHP.Stage4ThetaNormalizedXiFourthDerivative

/-!
Express the necessary fourth-order spectral scaling invariant
using the zeroth, second and fourth theta moments.
This file does not establish a mismatch of that invariant.
-/

noncomputable section

namespace HodgeProofHP

theorem hpThetaXi_iteratedFourthDeriv_zero_eq_moment :
    hpThetaIteratedComplexDeriv 4 hpRiemannXiCritical 0 =
      (hpThetaPhiMomentFour : ℂ) := by
  change
    deriv (deriv (deriv (deriv hpRiemannXiCritical))) 0 =
      (hpThetaPhiMomentFour : ℂ)
  exact hpRiemannXiCritical_fourthDeriv_zero_eq_moment

theorem hpThetaNormalizedXiFourthTraceCoefficient_eq_moment_ratio :
    hpThetaNormalizedXiFourthTraceCoefficient =
      hpThetaPhiMomentFour / (12 * hpThetaPhiMomentZero) := by
  rw [hpThetaNormalizedXiFourthTraceCoefficient_eq_xi_ratio,
    hpThetaXi_iteratedFourthDeriv_zero_eq_moment,
    Complex.ofReal_re,
    ← hpThetaPhiMomentZero_eq_xi_zero_re]

theorem hpThetaHankelScaledSpectralProduct_eq_normalizedXi_moment_invariant
    (c : ℝ)
    (hmatch :
      hpThetaHankelScaledSpectralProduct c = hpThetaNormalizedXi) :
    (hpThetaPhiMomentTwo / (2 * hpThetaPhiMomentZero)) ^ 2 *
        (hpThetaFirstTraceEnergy ^ 2 -
          hpThetaHankelSpectralSquareEnergy) =
      hpThetaFirstTraceEnergy ^ 2 *
        (hpThetaPhiMomentFour / (12 * hpThetaPhiMomentZero)) := by
  have h :=
    hpThetaHankelScaledSpectralProduct_eq_normalizedXi_real_invariant
      c hmatch
  rw [hpRiemannXiCritical_secondDeriv_zero_re,
    ← hpThetaPhiMomentZero_eq_xi_zero_re,
    hpThetaNormalizedXiFourthTraceCoefficient_eq_moment_ratio] at h
  simpa only [neg_neg] using h

theorem hpThetaHankelScaledSpectralProduct_ne_normalizedXi_of_moment_invariant
    (hbad :
      (hpThetaPhiMomentTwo / (2 * hpThetaPhiMomentZero)) ^ 2 *
          (hpThetaFirstTraceEnergy ^ 2 -
            hpThetaHankelSpectralSquareEnergy) ≠
        hpThetaFirstTraceEnergy ^ 2 *
          (hpThetaPhiMomentFour / (12 * hpThetaPhiMomentZero)))
    (c : ℝ) :
    hpThetaHankelScaledSpectralProduct c ≠ hpThetaNormalizedXi := by
  intro hmatch
  exact hbad
    (hpThetaHankelScaledSpectralProduct_eq_normalizedXi_moment_invariant
      c hmatch)

#print axioms hpThetaXi_iteratedFourthDeriv_zero_eq_moment
#print axioms hpThetaNormalizedXiFourthTraceCoefficient_eq_moment_ratio
#print axioms hpThetaHankelScaledSpectralProduct_eq_normalizedXi_moment_invariant
#print axioms hpThetaHankelScaledSpectralProduct_ne_normalizedXi_of_moment_invariant

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelFourthMomentInvariant

printf '%s\n' 'PASS: Stage4ThetaHankelFourthMomentInvariant'
