#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "Run this script from the hodgeproof-hp project root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaFiniteCosineIBP

target="HodgeProofHP/Stage4ThetaImproperCosineIBP.lean"

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaFiniteCosineIBP
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
Integrability of the second derivative of the theta log profile
on the positive half-line, including complex cosine and sine factors.
Passing to the limit in finite integration by parts gives
the improper cosine identity.
-/

noncomputable section

open MeasureTheory Filter

namespace HodgeProofHP

theorem hpRiemannThetaLogProfile_secondDeriv_exp_weighted_integrableOn
    (c : ℝ) :
    IntegrableOn
      (fun u : ℝ =>
        Real.exp (c * u) * deriv (deriv hpRiemannThetaLogProfile) u)
      (Set.Ioi 0) volume :=
  hpTheta_weighted_integrableOn_of_continuous_decay
    (deriv (deriv hpRiemannThetaLogProfile))
    hpRiemannThetaLogProfile_secondDeriv_continuous
    hpRiemannThetaLogProfile_secondDeriv_exp_weighted_tendsto_zero
    c

theorem hpRiemannThetaLogProfile_secondDeriv_cos_integrableOn
    (z : ℂ) :
    IntegrableOn
      (fun u : ℝ =>
        ((deriv (deriv hpRiemannThetaLogProfile) u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ)))
      (Set.Ioi 0) volume :=
  hpTheta_mul_complex_cos_integrableOn
    (deriv (deriv hpRiemannThetaLogProfile))
    hpRiemannThetaLogProfile_secondDeriv_continuous
    hpRiemannThetaLogProfile_secondDeriv_exp_weighted_integrableOn
    z

theorem hpRiemannThetaLogProfile_secondDeriv_sin_integrableOn
    (z : ℂ) :
    IntegrableOn
      (fun u : ℝ =>
        ((deriv (deriv hpRiemannThetaLogProfile) u : ℝ) : ℂ) *
          Complex.sin (z * (u : ℂ)))
      (Set.Ioi 0) volume :=
  hpTheta_mul_complex_sin_integrableOn
    (deriv (deriv hpRiemannThetaLogProfile))
    hpRiemannThetaLogProfile_secondDeriv_continuous
    hpRiemannThetaLogProfile_secondDeriv_exp_weighted_integrableOn
    z

theorem hpRiemannThetaLogProfile_secondDeriv_improper_cosine_ibp
    (z : ℂ) :
    (∫ u : ℝ in Set.Ioi 0,
      ((deriv (deriv hpRiemannThetaLogProfile) u : ℝ) : ℂ) *
        Complex.cos (z * (u : ℂ))) =
      (1 / 2 : ℂ) -
        z ^ 2 *
          (∫ u : ℝ in Set.Ioi 0,
            (hpRiemannThetaLogProfile u : ℂ) *
              Complex.cos (z * (u : ℂ))) := by
  have hLeft :
      Tendsto
        (fun R : ℝ =>
          ∫ u in (0 : ℝ)..R,
            ((deriv (deriv hpRiemannThetaLogProfile) u : ℝ) : ℂ) *
              Complex.cos (z * (u : ℂ)))
        atTop
        (nhds
          (∫ u : ℝ in Set.Ioi 0,
            ((deriv (deriv hpRiemannThetaLogProfile) u : ℝ) : ℂ) *
              Complex.cos (z * (u : ℂ)))) :=
    intervalIntegral_tendsto_integral_Ioi 0
      (hpRiemannThetaLogProfile_secondDeriv_cos_integrableOn z)
      tendsto_id
  have hBase :
      Tendsto
        (fun R : ℝ =>
          ∫ u in (0 : ℝ)..R,
            (hpRiemannThetaLogProfile u : ℂ) *
              Complex.cos (z * (u : ℂ)))
        atTop
        (nhds
          (∫ u : ℝ in Set.Ioi 0,
            (hpRiemannThetaLogProfile u : ℂ) *
              Complex.cos (z * (u : ℂ)))) :=
    intervalIntegral_tendsto_integral_Ioi 0
      (hpRiemannThetaLogProfile_cos_integrableOn z)
      tendsto_id
  have hCos :=
    hpRiemannThetaLogProfile_deriv_cos_boundary_tendsto_zero z
  have hSin :=
    hpRiemannThetaLogProfile_sin_boundary_tendsto_zero z
  have hZ : Tendsto (fun _ : ℝ => z) atTop (nhds z) :=
    tendsto_const_nhds
  have hHalf :
      Tendsto (fun _ : ℝ => (1 / 2 : ℂ)) atTop
        (nhds (1 / 2 : ℂ)) :=
    tendsto_const_nhds
  have hSquare :
      Tendsto (fun _ : ℝ => z ^ 2) atTop (nhds (z ^ 2)) :=
    tendsto_const_nhds
  have hRight :
      Tendsto
        (fun R : ℝ =>
          ((deriv hpRiemannThetaLogProfile R : ℝ) : ℂ) *
              Complex.cos (z * (R : ℂ)) +
            z * (hpRiemannThetaLogProfile R : ℂ) *
              Complex.sin (z * (R : ℂ)) +
            (1 / 2 : ℂ) -
            z ^ 2 *
              (∫ u in (0 : ℝ)..R,
                (hpRiemannThetaLogProfile u : ℂ) *
                  Complex.cos (z * (u : ℂ))))
        atTop
        (nhds
          ((1 / 2 : ℂ) -
            z ^ 2 *
              (∫ u : ℝ in Set.Ioi 0,
                (hpRiemannThetaLogProfile u : ℂ) *
                  Complex.cos (z * (u : ℂ))))) := by
    simpa only [mul_zero, zero_add, add_zero, mul_assoc] using
      ((hCos.add (hZ.mul hSin)).add hHalf).sub
        (hSquare.mul hBase)
  have hFunctions :
      (fun R : ℝ =>
        ∫ u in (0 : ℝ)..R,
          ((deriv (deriv hpRiemannThetaLogProfile) u : ℝ) : ℂ) *
            Complex.cos (z * (u : ℂ))) =
      (fun R : ℝ =>
        ((deriv hpRiemannThetaLogProfile R : ℝ) : ℂ) *
            Complex.cos (z * (R : ℂ)) +
          z * (hpRiemannThetaLogProfile R : ℂ) *
            Complex.sin (z * (R : ℂ)) +
          (1 / 2 : ℂ) -
          z ^ 2 *
            (∫ u in (0 : ℝ)..R,
              (hpRiemannThetaLogProfile u : ℂ) *
                Complex.cos (z * (u : ℂ)))) := by
    funext R
    exact hpRiemannThetaLogProfile_secondDeriv_finite_cosine_ibp z R
  rw [← hFunctions] at hRight
  exact tendsto_nhds_unique hLeft hRight

#print axioms hpRiemannThetaLogProfile_secondDeriv_exp_weighted_integrableOn
#print axioms hpRiemannThetaLogProfile_secondDeriv_cos_integrableOn
#print axioms hpRiemannThetaLogProfile_secondDeriv_sin_integrableOn
#print axioms hpRiemannThetaLogProfile_secondDeriv_improper_cosine_ibp

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaImproperCosineIBP

echo "PASS: improper cosine integration by parts"
