#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "Run this script from the hodgeproof-hp project root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaSecondDerivativeContinuity

target="HodgeProofHP/Stage4ThetaFiniteCosineIBP.lean"

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaSecondDerivativeContinuity

/-!
Second-order integration by parts for the theta log profile
and complex cosine on a finite interval.
The contribution at zero uses the proved value B'(0) = -1/2.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpThetaComplexProfileFirst_continuous :
    Continuous
      (fun u : ℝ =>
        ((deriv hpRiemannThetaLogProfile u : ℝ) : ℂ)) := by
  exact continuous_iff_continuousAt.mpr
    (fun u => (hpThetaComplexProfileFirst_hasDerivAt u).continuousAt)

theorem hpThetaComplexCos_continuous (z : ℂ) :
    Continuous (fun u : ℝ => Complex.cos (z * (u : ℂ))) := by
  exact continuous_iff_continuousAt.mpr
    (fun u => (hpThetaComplexCos_hasDerivAt z u).continuousAt)

theorem hpThetaComplexCosFirst_continuous (z : ℂ) :
    Continuous
      (fun u : ℝ => -z * Complex.sin (z * (u : ℂ))) := by
  exact continuous_iff_continuousAt.mpr
    (fun u => (hpThetaComplexCosFirst_hasDerivAt z u).continuousAt)

theorem hpRiemannThetaLogProfile_secondDeriv_finite_cosine_ibp
    (z : ℂ) (R : ℝ) :
    (∫ u in (0 : ℝ)..R,
      ((deriv (deriv hpRiemannThetaLogProfile) u : ℝ) : ℂ) *
        Complex.cos (z * (u : ℂ))) =
      ((deriv hpRiemannThetaLogProfile R : ℝ) : ℂ) *
          Complex.cos (z * (R : ℂ)) +
        z * (hpRiemannThetaLogProfile R : ℂ) *
          Complex.sin (z * (R : ℂ)) +
        (1 / 2 : ℂ) -
        z ^ 2 *
          (∫ u in (0 : ℝ)..R,
            (hpRiemannThetaLogProfile u : ℂ) *
              Complex.cos (z * (u : ℂ))) := by
  have hc₂ :
      Continuous
        (fun u : ℝ => -(z ^ 2) * Complex.cos (z * (u : ℂ))) :=
    continuous_const.mul (hpThetaComplexCos_continuous z)
  have h := hpSecondOrderIntegrationByParts
    (fun u : ℝ => (hpRiemannThetaLogProfile u : ℂ))
    (fun u : ℝ =>
      ((deriv hpRiemannThetaLogProfile u : ℝ) : ℂ))
    (fun u : ℝ =>
      ((deriv (deriv hpRiemannThetaLogProfile) u : ℝ) : ℂ))
    (fun u : ℝ => Complex.cos (z * (u : ℂ)))
    (fun u : ℝ => -z * Complex.sin (z * (u : ℂ)))
    (fun u : ℝ => -(z ^ 2) * Complex.cos (z * (u : ℂ)))
    R
    hpThetaComplexProfile_hasDerivAt
    hpThetaComplexProfileFirst_hasDerivAt
    (hpThetaComplexCos_hasDerivAt z)
    (hpThetaComplexCosFirst_hasDerivAt z)
    (hpThetaComplexProfileFirst_continuous.intervalIntegrable 0 R)
    (hpThetaComplexProfileSecond_intervalIntegrable 0 R)
    ((hpThetaComplexCosFirst_continuous z).intervalIntegrable 0 R)
    (hc₂.intervalIntegrable 0 R)
  have hzero :
      ((deriv hpRiemannThetaLogProfile 0 : ℝ) : ℂ) =
        -(1 / 2 : ℂ) := by
    rw [hpRiemannThetaLogProfile_deriv_zero]
    norm_num
  have hIntegral :
      (∫ u in (0 : ℝ)..R,
        (hpRiemannThetaLogProfile u : ℂ) *
          (-(z ^ 2) * Complex.cos (z * (u : ℂ)))) =
        -(z ^ 2) *
          (∫ u in (0 : ℝ)..R,
            (hpRiemannThetaLogProfile u : ℂ) *
              Complex.cos (z * (u : ℂ))) := by
    calc
      _ = ∫ u in (0 : ℝ)..R,
          -(z ^ 2) *
            ((hpRiemannThetaLogProfile u : ℂ) *
              Complex.cos (z * (u : ℂ))) := by
        congr 1
        funext u
        ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [hIntegral] at h
  simp only [hzero, Complex.ofReal_zero, mul_zero,
    Complex.cos_zero, Complex.sin_zero, mul_one,
    sub_zero, zero_mul, add_zero] at h
  convert h using 1 <;> ring

#print axioms hpThetaComplexProfileFirst_continuous
#print axioms hpThetaComplexCos_continuous
#print axioms hpThetaComplexCosFirst_continuous
#print axioms hpRiemannThetaLogProfile_secondDeriv_finite_cosine_ibp

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaFiniteCosineIBP

echo "PASS: finite cosine integration by parts with the zero boundary term"
