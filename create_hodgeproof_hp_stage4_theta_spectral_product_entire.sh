#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSpectralProductPolynomialLimits

target="HodgeProofHP/Stage4ThetaHankelSpectralProductEntire.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSpectralProductPolynomialLimits
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
The spectral product is entire. Finite spectral products and their first
derivatives converge locally uniformly. No identification with Xi is assumed.
-/

namespace HodgeProofHP

theorem hpThetaHankelFiniteSpectralProduct_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn
      (fun F : Finset HPThetaHankelSpectralIndex =>
        hpThetaHankelFiniteSpectralProduct F)
      hpThetaHankelSpectralProduct
      Filter.atTop (Set.univ : Set ℂ) := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z _
  have hr : 0 ≤ ‖z‖ + 1 := by positivity
  have h :=
    hpThetaHankelFiniteSpectralProduct_tendstoUniformlyOn_closedBall
      (‖z‖ + 1) hr
  refine ⟨Metric.ball (0 : ℂ) (‖z‖ + 1), ?_,
    h.mono Metric.ball_subset_closedBall⟩
  have hz : z ∈ Metric.ball (0 : ℂ) (‖z‖ + 1) := by
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  simpa only [nhdsWithin_univ] using
    (IsOpen.mem_nhds Metric.isOpen_ball hz)

theorem hpThetaHankelSpectralProduct_differentiable :
    Differentiable ℂ hpThetaHankelSpectralProduct := by
  have hF :
      ∀ᶠ F : Finset HPThetaHankelSpectralIndex in Filter.atTop,
        DifferentiableOn ℂ
          (hpThetaHankelFiniteSpectralProduct F)
          (Set.univ : Set ℂ) :=
    Filter.Eventually.of_forall (fun F =>
      (hpThetaHankelFiniteSpectralProduct_differentiable F).differentiableOn)
  have h :=
    hpThetaHankelFiniteSpectralProduct_tendstoLocallyUniformlyOn.differentiableOn
      hF isOpen_univ
  exact differentiableOn_univ.mp h

theorem hpThetaHankelSpectralProduct_continuous :
    Continuous hpThetaHankelSpectralProduct :=
  hpThetaHankelSpectralProduct_differentiable.continuous

theorem hpThetaHankelFiniteSpectralProduct_deriv_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn
      (fun F : Finset HPThetaHankelSpectralIndex =>
        deriv (hpThetaHankelFiniteSpectralProduct F))
      (deriv hpThetaHankelSpectralProduct)
      Filter.atTop (Set.univ : Set ℂ) := by
  have hF :
      ∀ᶠ F : Finset HPThetaHankelSpectralIndex in Filter.atTop,
        DifferentiableOn ℂ
          (hpThetaHankelFiniteSpectralProduct F)
          (Set.univ : Set ℂ) :=
    Filter.Eventually.of_forall (fun F =>
      (hpThetaHankelFiniteSpectralProduct_differentiable F).differentiableOn)
  simpa only [Function.comp_def] using
    hpThetaHankelFiniteSpectralProduct_tendstoLocallyUniformlyOn.deriv
      hF isOpen_univ

#print axioms hpThetaHankelFiniteSpectralProduct_tendstoLocallyUniformlyOn
#print axioms hpThetaHankelSpectralProduct_differentiable
#print axioms hpThetaHankelSpectralProduct_continuous
#print axioms hpThetaHankelFiniteSpectralProduct_deriv_tendstoLocallyUniformlyOn

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelSpectralProductEntire

printf '%s\n' 'PASS: Stage4ThetaHankelSpectralProductEntire'
