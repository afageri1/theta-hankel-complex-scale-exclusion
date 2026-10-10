#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelFourthRealInvariant

target="HodgeProofHP/Stage4ThetaNormalizedXiFourthDerivative.lean"

if [ -f "$target" ]; then
  backup="$target.before_update_$(date +%Y%m%d_%H%M%S)"
  cp -p "$target" "$backup"
  printf 'BACKUP: %s\n' "$backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelFourthRealInvariant

/-!
Fourth derivative of normalized Xi and its real trace coefficient.
These identities do not yet identify the derivative with a theta moment.
-/

namespace HodgeProofHP

theorem hpThetaIteratedComplexDeriv_div_const_zero
    (n : ℕ) (f : ℂ → ℂ) (a : ℂ) :
    hpThetaIteratedComplexDeriv n (fun z => f z / a) 0 =
      hpThetaIteratedComplexDeriv n f 0 / a := by
  simp only [hpThetaIteratedComplexDeriv_eq_iteratedDeriv,
    iteratedDeriv_div_const]

private theorem hpTheta_re_div_real_cast
    (z : ℂ) (a : ℝ) :
    (z / (a : ℂ)).re = z.re / a := by
  rw [div_eq_mul_inv, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, div_eq_mul_inv]

theorem hpThetaNormalizedXi_fourthDeriv_zero :
    hpThetaIteratedComplexDeriv 4 hpThetaNormalizedXi 0 =
      hpThetaIteratedComplexDeriv 4 hpRiemannXiCritical 0 /
        hpRiemannXiCritical 0 := by
  unfold hpThetaNormalizedXi
  exact hpThetaIteratedComplexDeriv_div_const_zero
    4 hpRiemannXiCritical (hpRiemannXiCritical 0)

theorem hpThetaNormalizedXiFourthTraceCoefficient_eq_xi_ratio :
    hpThetaNormalizedXiFourthTraceCoefficient =
      (hpThetaIteratedComplexDeriv 4 hpRiemannXiCritical 0).re /
        (12 * (hpRiemannXiCritical 0).re) := by
  unfold hpThetaNormalizedXiFourthTraceCoefficient
  rw [hpThetaNormalizedXi_fourthDeriv_zero,
    ← hpThetaXi_zero_eq_cast_re]
  have h12 :
      (((hpThetaIteratedComplexDeriv 4 hpRiemannXiCritical 0 /
          ((hpRiemannXiCritical 0).re : ℂ)) / (12 : ℂ))).re =
        (hpThetaIteratedComplexDeriv 4 hpRiemannXiCritical 0 /
          ((hpRiemannXiCritical 0).re : ℂ)).re / 12 := by
    exact hpTheta_re_div_real_cast
      (hpThetaIteratedComplexDeriv 4 hpRiemannXiCritical 0 /
        ((hpRiemannXiCritical 0).re : ℂ)) (12 : ℝ)
  rw [h12,
    hpTheta_re_div_real_cast
      (hpThetaIteratedComplexDeriv 4 hpRiemannXiCritical 0)
      (hpRiemannXiCritical 0).re]
  simp only [Complex.ofReal_re]
  ring

theorem hpThetaHankelScaledSpectralProduct_eq_normalizedXi_real_derivative_invariant
    (c : ℝ)
    (hmatch :
      hpThetaHankelScaledSpectralProduct c = hpThetaNormalizedXi) :
    (-(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re)) ^ 2 *
        (hpThetaFirstTraceEnergy ^ 2 -
          hpThetaHankelSpectralSquareEnergy) =
      hpThetaFirstTraceEnergy ^ 2 *
        ((hpThetaIteratedComplexDeriv 4 hpRiemannXiCritical 0).re /
          (12 * (hpRiemannXiCritical 0).re)) := by
  have h :=
    hpThetaHankelScaledSpectralProduct_eq_normalizedXi_real_invariant
      c hmatch
  rw [hpThetaNormalizedXiFourthTraceCoefficient_eq_xi_ratio] at h
  exact h

#print axioms hpThetaIteratedComplexDeriv_div_const_zero
#print axioms hpThetaNormalizedXi_fourthDeriv_zero
#print axioms hpThetaNormalizedXiFourthTraceCoefficient_eq_xi_ratio
#print axioms hpThetaHankelScaledSpectralProduct_eq_normalizedXi_real_derivative_invariant

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaNormalizedXiFourthDerivative

printf '%s\n' 'PASS: Stage4ThetaNormalizedXiFourthDerivative'
