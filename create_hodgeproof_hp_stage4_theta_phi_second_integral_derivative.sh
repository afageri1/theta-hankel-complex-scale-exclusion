#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "Run from ~/hodgeproof-hp"
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaPhiFirstIntegralDerivative

target="HodgeProofHP/Stage4ThetaPhiSecondIntegralDerivative.lean"
mkdir -p HodgeProofHP

if [[ -f "$target" ]]; then
  cp "$target" \
    "${target}.before_update_$(date +%Y%m%d_%H%M%S)_$$"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaPhiFirstIntegralDerivative

/-!
Second complex derivative of the differential-theta
representation and its second-moment identity at zero.
-/

noncomputable section

open MeasureTheory Set Filter

namespace HodgeProofHP

theorem hpThetaPhiCosIntegrandSecond_continuous (z : ℂ) :
    Continuous (hpThetaPhiCosIntegrandSecond z) := by
  have hphi :
      Continuous
        (fun u : ℝ => (hpRiemannThetaDifferentialKernel u : ℂ)) :=
    Complex.continuous_ofReal.comp
      hpRiemannThetaDifferentialKernel_continuous
  exact (hphi.neg.mul (Complex.continuous_ofReal.pow 2)).mul
    (Complex.continuous_cos.comp
      (continuous_const.mul Complex.continuous_ofReal))

theorem hpThetaPhiCosIntegrandFirst_integrableOn (z : ℂ) :
    IntegrableOn (hpThetaPhiCosIntegrandFirst z)
      (Set.Ioi 0) volume := by
  have hG := hpThetaPhi_firstMoment_exp_integrableOn ‖z‖
  apply hG.norm.mono'
    (hpThetaPhiCosIntegrandFirst_continuous z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact hpThetaPhiCosIntegrandFirst_norm_le
    z u ‖z‖ (le_of_lt hu) le_rfl

theorem hpRiemannXiCritical_deriv_hasDerivAt_phi_integral (z : ℂ) :
    HasDerivAt (deriv hpRiemannXiCritical)
      (∫ u : ℝ in Set.Ioi 0, hpThetaPhiCosIntegrandSecond z u) z := by
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi 0))
      (F := hpThetaPhiCosIntegrandFirst)
      (F' := hpThetaPhiCosIntegrandSecond)
      (bound := fun u : ℝ =>
        ‖u ^ 2 * Real.exp ((‖z‖ + 1) * u) *
          hpRiemannThetaDifferentialKernel u‖)
      (x₀ := z)
      (s := Metric.ball z 1)
      (Metric.ball_mem_nhds z (by norm_num))
      (Filter.Eventually.of_forall fun w =>
        (hpThetaPhiCosIntegrandFirst_continuous w).aestronglyMeasurable)
      (hpThetaPhiCosIntegrandFirst_integrableOn z)
      (hpThetaPhiCosIntegrandSecond_continuous z).aestronglyMeasurable
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        intro w hw
        have hdist : ‖w - z‖ < 1 := by
          simpa only [Metric.mem_ball, dist_eq_norm] using hw
        have htri := norm_add_le (w - z) z
        have hsum : (w - z) + z = w := by ring
        rw [hsum] at htri
        have hwbound : ‖w‖ ≤ ‖z‖ + 1 := by linarith
        exact hpThetaPhiCosIntegrandSecond_norm_le
          w u (‖z‖ + 1) (le_of_lt hu) hwbound)
      (hpThetaPhi_secondMoment_exp_integrableOn (‖z‖ + 1)).norm
      (Filter.Eventually.of_forall fun u w _ =>
        hpThetaPhiCosIntegrandFirst_hasDerivAt w u)
  have heq :
      (fun w : ℂ =>
        ∫ u : ℝ in Set.Ioi 0, hpThetaPhiCosIntegrandFirst w u) =
          deriv hpRiemannXiCritical := by
    funext w
    exact (hpRiemannXiCritical_deriv_eq_phi_integral w).symm
  rw [heq] at h
  exact h.2

theorem hpRiemannXiCritical_secondDeriv_eq_phi_integral (z : ℂ) :
    deriv (deriv hpRiemannXiCritical) z =
      ∫ u : ℝ in Set.Ioi 0, hpThetaPhiCosIntegrandSecond z u :=
  (hpRiemannXiCritical_deriv_hasDerivAt_phi_integral z).deriv

theorem hpRiemannXiCritical_secondDeriv_zero_eq_moment :
    deriv (deriv hpRiemannXiCritical) 0 =
      -(hpThetaPhiMomentTwo : ℂ) := by
  rw [hpRiemannXiCritical_secondDeriv_eq_phi_integral]
  have heq :
      hpThetaPhiCosIntegrandSecond 0 =
        (fun u : ℝ =>
          -((u ^ 2 * hpRiemannThetaDifferentialKernel u : ℝ) : ℂ)) := by
    funext u
    rw [hpThetaPhiCosIntegrandSecond_zero]
    simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  rw [heq, integral_neg]
  have hcast :
      (∫ u : ℝ in Set.Ioi 0,
        ((u ^ 2 * hpRiemannThetaDifferentialKernel u : ℝ) : ℂ)) =
          (hpThetaPhiMomentTwo : ℂ) := by
    exact integral_complex_ofReal
      (f := fun u : ℝ =>
        u ^ 2 * hpRiemannThetaDifferentialKernel u)
      (μ := volume.restrict (Set.Ioi 0))
  exact congrArg (fun w : ℂ => -w) hcast

theorem hpRiemannXiCritical_secondDeriv_zero_re :
    (deriv (deriv hpRiemannXiCritical) 0).re =
      -hpThetaPhiMomentTwo := by
  have h := congrArg Complex.re
    hpRiemannXiCritical_secondDeriv_zero_eq_moment
  simpa using h

#print axioms hpThetaPhiCosIntegrandSecond_continuous
#print axioms hpThetaPhiCosIntegrandFirst_integrableOn
#print axioms hpRiemannXiCritical_deriv_hasDerivAt_phi_integral
#print axioms hpRiemannXiCritical_secondDeriv_eq_phi_integral
#print axioms hpRiemannXiCritical_secondDeriv_zero_eq_moment
#print axioms hpRiemannXiCritical_secondDeriv_zero_re

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaPhiSecondIntegralDerivative
echo "PASS: Stage4ThetaPhiSecondIntegralDerivative"
