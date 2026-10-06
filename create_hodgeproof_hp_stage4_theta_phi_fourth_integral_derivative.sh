#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaPhiThirdIntegralDerivative

target="HodgeProofHP/Stage4ThetaPhiFourthIntegralDerivative.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaPhiThirdIntegralDerivative

/-!
Fourth complex derivative of the differential-theta representation
of Riemann Xi and its fourth-moment identity at zero.
-/

noncomputable section

open MeasureTheory Set Filter

namespace HodgeProofHP

def hpThetaPhiMomentFour : ℝ :=
  ∫ u : ℝ in Set.Ioi 0,
    u ^ 4 * hpRiemannThetaDifferentialKernel u

theorem hpThetaPhiCosIntegrandFourth_integrableOn (z : ℂ) :
    IntegrableOn (hpThetaPhiCosIntegrandFourth z)
      (Set.Ioi 0) volume := by
  have hG := hpThetaPhi_fourthMoment_exp_integrableOn ‖z‖
  apply hG.norm.mono'
    (hpThetaPhiCosIntegrandFourth_continuous z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact hpThetaPhiCosIntegrandFourth_norm_le
    z u ‖z‖ (le_of_lt hu) le_rfl

theorem hpRiemannXiCritical_thirdDeriv_hasDerivAt_phi_integral
    (z : ℂ) :
    HasDerivAt (deriv (deriv (deriv hpRiemannXiCritical)))
      (∫ u : ℝ in Set.Ioi 0, hpThetaPhiCosIntegrandFourth z u)
      z := by
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi 0))
      (F := hpThetaPhiCosIntegrandThird)
      (F' := hpThetaPhiCosIntegrandFourth)
      (bound := fun u : ℝ =>
        ‖u ^ 4 * Real.exp ((‖z‖ + 1) * u) *
          hpRiemannThetaDifferentialKernel u‖)
      (x₀ := z)
      (s := Metric.ball z 1)
      (Metric.ball_mem_nhds z (by norm_num))
      (Filter.Eventually.of_forall fun w =>
        (hpThetaPhiCosIntegrandThird_continuous w).aestronglyMeasurable)
      (hpThetaPhiCosIntegrandThird_integrableOn z)
      (hpThetaPhiCosIntegrandFourth_continuous z).aestronglyMeasurable
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        intro w hw
        have hdist : ‖w - z‖ < 1 := by
          simpa only [Metric.mem_ball, dist_eq_norm] using hw
        have htri := norm_add_le (w - z) z
        have hsum : (w - z) + z = w := by ring
        rw [hsum] at htri
        have hwbound : ‖w‖ ≤ ‖z‖ + 1 := by linarith
        exact hpThetaPhiCosIntegrandFourth_norm_le
          w u (‖z‖ + 1) (le_of_lt hu) hwbound)
      (hpThetaPhi_fourthMoment_exp_integrableOn (‖z‖ + 1)).norm
      (Filter.Eventually.of_forall fun u w _ =>
        hpThetaPhiCosIntegrandThird_hasDerivAt w u)
  have heq :
      (fun w : ℂ =>
        ∫ u : ℝ in Set.Ioi 0, hpThetaPhiCosIntegrandThird w u) =
          deriv (deriv (deriv hpRiemannXiCritical)) := by
    funext w
    exact (hpRiemannXiCritical_thirdDeriv_eq_phi_integral w).symm
  rw [heq] at h
  exact h.2

theorem hpRiemannXiCritical_fourthDeriv_eq_phi_integral (z : ℂ) :
    deriv (deriv (deriv (deriv hpRiemannXiCritical))) z =
      ∫ u : ℝ in Set.Ioi 0, hpThetaPhiCosIntegrandFourth z u :=
  (hpRiemannXiCritical_thirdDeriv_hasDerivAt_phi_integral z).deriv

theorem hpRiemannXiCritical_fourthDeriv_zero_eq_moment :
    deriv (deriv (deriv (deriv hpRiemannXiCritical))) 0 =
      (hpThetaPhiMomentFour : ℂ) := by
  rw [hpRiemannXiCritical_fourthDeriv_eq_phi_integral]
  have heq :
      hpThetaPhiCosIntegrandFourth 0 =
        (fun u : ℝ =>
          ((u ^ 4 * hpRiemannThetaDifferentialKernel u : ℝ) : ℂ)) := by
    funext u
    exact hpThetaPhiCosIntegrandFourth_zero u
  rw [heq]
  exact integral_complex_ofReal
    (f := fun u : ℝ =>
      u ^ 4 * hpRiemannThetaDifferentialKernel u)
    (μ := volume.restrict (Set.Ioi 0))

theorem hpRiemannXiCritical_fourthDeriv_zero_re :
    (deriv (deriv (deriv (deriv hpRiemannXiCritical))) 0).re =
      hpThetaPhiMomentFour := by
  have h := congrArg Complex.re
    hpRiemannXiCritical_fourthDeriv_zero_eq_moment
  simpa only [Complex.ofReal_re] using h

theorem hpRiemannXiCritical_fourthDeriv_zero_im :
    (deriv (deriv (deriv (deriv hpRiemannXiCritical))) 0).im = 0 := by
  have h := congrArg Complex.im
    hpRiemannXiCritical_fourthDeriv_zero_eq_moment
  simpa only [Complex.ofReal_im] using h

#print axioms hpThetaPhiCosIntegrandFourth_integrableOn
#print axioms hpRiemannXiCritical_thirdDeriv_hasDerivAt_phi_integral
#print axioms hpRiemannXiCritical_fourthDeriv_eq_phi_integral
#print axioms hpRiemannXiCritical_fourthDeriv_zero_eq_moment
#print axioms hpRiemannXiCritical_fourthDeriv_zero_re
#print axioms hpRiemannXiCritical_fourthDeriv_zero_im

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaPhiFourthIntegralDerivative

printf '%s\n' 'PASS: Stage4ThetaPhiFourthIntegralDerivative'
