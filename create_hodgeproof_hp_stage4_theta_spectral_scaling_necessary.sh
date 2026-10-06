#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSpectralProductXiObstruction

target="HodgeProofHP/Stage4ThetaHankelSpectralScalingNecessary.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSpectralProductXiObstruction

/-!
A necessary second-coefficient condition for a real rescaling
of the constructed spectral product.

This condition is not sufficient for correspondence with Xi.
-/

namespace HodgeProofHP

theorem hpTheta_deriv_comp_scale
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) :
    deriv (fun z : ℂ => f (c * z)) =
      (fun z : ℂ => deriv f (c * z) * c) := by
  funext z
  have harg : HasDerivAt (fun w : ℂ => c * w) c z := by
    have h := (hasDerivAt_id z).const_mul c
    simp only [mul_one] at h
    convert h using 1 <;> rfl
  have h :
      HasDerivAt (fun w : ℂ => f (c * w))
        (deriv f (c * z) * c) z := by
    convert ((hf (c * z)).hasDerivAt.comp z harg) using 1 <;> rfl
  exact h.deriv

theorem hpTheta_secondDeriv_comp_scale_zero
    (f : ℂ → ℂ)
    (hf : Differentiable ℂ f)
    (hf' : Differentiable ℂ (deriv f))
    (c : ℂ) :
    deriv (deriv (fun z : ℂ => f (c * z))) 0 =
      c ^ 2 * deriv (deriv f) 0 := by
  rw [hpTheta_deriv_comp_scale f hf c]
  have harg : HasDerivAt (fun w : ℂ => c * w) c 0 := by
    have h := (hasDerivAt_id (0 : ℂ)).const_mul c
    simp only [mul_one] at h
    convert h using 1 <;> rfl
  have hcomp :
      HasDerivAt (fun w : ℂ => deriv f (c * w))
        (deriv (deriv f) 0 * c) 0 := by
    have h := (hf' (0 : ℂ)).hasDerivAt.comp_of_eq
      (0 : ℂ) harg (by simp)
    convert h using 1 <;> rfl
  have h := (hcomp.mul_const c).deriv
  convert h using 1 <;> first | rfl | ring

noncomputable def hpThetaHankelScaledSpectralProduct
    (c : ℝ) (z : ℂ) : ℂ :=
  hpThetaHankelSpectralProduct ((c : ℂ) * z)

theorem hpThetaHankelScaledSpectralProduct_secondDeriv_zero
    (c : ℝ) :
    deriv (deriv (hpThetaHankelScaledSpectralProduct c)) 0 =
      (-2 : ℂ) * (c : ℂ) ^ 2 * (hpThetaFirstTraceEnergy : ℂ) := by
  unfold hpThetaHankelScaledSpectralProduct
  rw [hpTheta_secondDeriv_comp_scale_zero
    hpThetaHankelSpectralProduct
    hpThetaHankelSpectralProduct_differentiable
    hpThetaHankelSpectralProduct_deriv_differentiable]
  rw [hpThetaHankelSpectralProduct_secondDeriv_zero]
  ring

theorem hpThetaHankelScaledSpectralProduct_secondDeriv_zero_re
    (c : ℝ) :
    (deriv (deriv (hpThetaHankelScaledSpectralProduct c)) 0).re =
      -2 * c ^ 2 * hpThetaFirstTraceEnergy := by
  rw [hpThetaHankelScaledSpectralProduct_secondDeriv_zero]
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem hpThetaHankelScaledSpectralProduct_eq_normalizedXi_necessary
    (c : ℝ)
    (hmatch :
      hpThetaHankelScaledSpectralProduct c = hpThetaNormalizedXi) :
    c ^ 2 * hpThetaFirstTraceEnergy =
      -(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re) := by
  have h := hpThetaNormalizedXi_secondCoefficient
  rw [← hmatch,
    hpThetaHankelScaledSpectralProduct_secondDeriv_zero_re] at h
  nlinarith [h]

theorem hpThetaHankelScaledSpectralProduct_ne_normalizedXi_of_coefficient
    (c : ℝ)
    (hbad :
      c ^ 2 * hpThetaFirstTraceEnergy ≠
        -(deriv (deriv hpRiemannXiCritical) 0).re /
          (2 * (hpRiemannXiCritical 0).re)) :
    hpThetaHankelScaledSpectralProduct c ≠ hpThetaNormalizedXi := by
  intro hmatch
  exact hbad
    (hpThetaHankelScaledSpectralProduct_eq_normalizedXi_necessary c hmatch)

#print axioms hpTheta_deriv_comp_scale
#print axioms hpTheta_secondDeriv_comp_scale_zero
#print axioms hpThetaHankelScaledSpectralProduct_secondDeriv_zero
#print axioms hpThetaHankelScaledSpectralProduct_secondDeriv_zero_re
#print axioms hpThetaHankelScaledSpectralProduct_eq_normalizedXi_necessary
#print axioms hpThetaHankelScaledSpectralProduct_ne_normalizedXi_of_coefficient

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelSpectralScalingNecessary

printf '%s\n' 'PASS: Stage4ThetaHankelSpectralScalingNecessary'
