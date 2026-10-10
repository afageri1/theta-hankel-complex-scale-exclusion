#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "Run from ~/hodgeproof-hp"
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaPhiLocalBounds

target="HodgeProofHP/Stage4ThetaPhiFirstIntegralDerivative.lean"
mkdir -p HodgeProofHP

if [[ -f "$target" ]]; then
  cp "$target" \
    "${target}.before_update_$(date +%Y%m%d_%H%M%S)_$$"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaPhiLocalBounds
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
First complex derivative of the differential-theta
representation of the Riemann Xi function.
-/

noncomputable section

open MeasureTheory Set Filter

namespace HodgeProofHP

theorem hpThetaPhiCosIntegrand_continuous (z : ℂ) :
    Continuous (hpThetaPhiCosIntegrand z) := by
  have hphi :
      Continuous
        (fun u : ℝ => (hpRiemannThetaDifferentialKernel u : ℂ)) :=
    Complex.continuous_ofReal.comp
      hpRiemannThetaDifferentialKernel_continuous
  exact hphi.mul
    (Complex.continuous_cos.comp
      (continuous_const.mul Complex.continuous_ofReal))

theorem hpThetaPhiCosIntegrandFirst_continuous (z : ℂ) :
    Continuous (hpThetaPhiCosIntegrandFirst z) := by
  have hphi :
      Continuous
        (fun u : ℝ => (hpRiemannThetaDifferentialKernel u : ℂ)) :=
    Complex.continuous_ofReal.comp
      hpRiemannThetaDifferentialKernel_continuous
  exact (hphi.neg.mul Complex.continuous_ofReal).mul
    (Complex.continuous_sin.comp
      (continuous_const.mul Complex.continuous_ofReal))

theorem hpThetaPhiCosIntegrand_integrableOn (z : ℂ) :
    IntegrableOn (hpThetaPhiCosIntegrand z)
      (Set.Ioi 0) volume := by
  have hG := hpThetaPhi_exp_weighted_integrableOn ‖z‖
  apply hG.norm.mono'
    (hpThetaPhiCosIntegrand_continuous z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have hc :
      ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp (‖z‖ * u) :=
    (hpThetaPhi_complex_cos_norm_le (z * (u : ℂ))).trans
      (hpThetaPhi_parameter_exp_bound z u ‖z‖ hu0 le_rfl)
  calc
    ‖hpThetaPhiCosIntegrand z u‖ =
        |hpRiemannThetaDifferentialKernel u| *
          ‖Complex.cos (z * (u : ℂ))‖ := by
      simp only [hpThetaPhiCosIntegrand, norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |hpRiemannThetaDifferentialKernel u| *
          Real.exp (‖z‖ * u) :=
      mul_le_mul_of_nonneg_left hc (abs_nonneg _)
    _ = ‖Real.exp (‖z‖ * u) *
          hpRiemannThetaDifferentialKernel u‖ := by
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos (‖z‖ * u))]
      ring

theorem hpRiemannXiCritical_hasDerivAt_phi_integral (z : ℂ) :
    HasDerivAt hpRiemannXiCritical
      (∫ u : ℝ in Set.Ioi 0, hpThetaPhiCosIntegrandFirst z u) z := by
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi 0))
      (F := hpThetaPhiCosIntegrand)
      (F' := hpThetaPhiCosIntegrandFirst)
      (bound := fun u : ℝ =>
        ‖u * Real.exp ((‖z‖ + 1) * u) *
          hpRiemannThetaDifferentialKernel u‖)
      (x₀ := z)
      (s := Metric.ball z 1)
      (Metric.ball_mem_nhds z (by norm_num))
      (Filter.Eventually.of_forall fun w =>
        (hpThetaPhiCosIntegrand_continuous w).aestronglyMeasurable)
      (hpThetaPhiCosIntegrand_integrableOn z)
      (hpThetaPhiCosIntegrandFirst_continuous z).aestronglyMeasurable
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        intro w hw
        have hdist : ‖w - z‖ < 1 := by
          simpa only [Metric.mem_ball, dist_eq_norm] using hw
        have htri := norm_add_le (w - z) z
        have hsum : (w - z) + z = w := by ring
        rw [hsum] at htri
        have hwbound : ‖w‖ ≤ ‖z‖ + 1 := by linarith
        exact hpThetaPhiCosIntegrandFirst_norm_le
          w u (‖z‖ + 1) (le_of_lt hu) hwbound)
      (hpThetaPhi_firstMoment_exp_integrableOn (‖z‖ + 1)).norm
      (Filter.Eventually.of_forall fun u w _ =>
        hpThetaPhiCosIntegrand_hasDerivAt w u)
  have heq :
      (fun w : ℂ =>
        ∫ u : ℝ in Set.Ioi 0, hpThetaPhiCosIntegrand w u) =
          hpRiemannXiCritical := by
    funext w
    exact (hpRiemannXiCritical_eq_differentialKernel_cosine_integral w).symm
  rw [heq] at h
  exact h.2

theorem hpRiemannXiCritical_deriv_eq_phi_integral (z : ℂ) :
    deriv hpRiemannXiCritical z =
      ∫ u : ℝ in Set.Ioi 0, hpThetaPhiCosIntegrandFirst z u :=
  (hpRiemannXiCritical_hasDerivAt_phi_integral z).deriv

theorem hpRiemannXiCritical_deriv_zero :
    deriv hpRiemannXiCritical 0 = 0 := by
  rw [hpRiemannXiCritical_deriv_eq_phi_integral]
  simp only [hpThetaPhiCosIntegrandFirst_zero, integral_zero]

#print axioms hpThetaPhiCosIntegrand_continuous
#print axioms hpThetaPhiCosIntegrandFirst_continuous
#print axioms hpThetaPhiCosIntegrand_integrableOn
#print axioms hpRiemannXiCritical_hasDerivAt_phi_integral
#print axioms hpRiemannXiCritical_deriv_eq_phi_integral
#print axioms hpRiemannXiCritical_deriv_zero

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaPhiFirstIntegralDerivative
echo "PASS: Stage4ThetaPhiFirstIntegralDerivative"
