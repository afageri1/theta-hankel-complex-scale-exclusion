import HodgeProofHP.Stage4ThetaPhiHigherParameterDerivatives

/-!
Third complex derivative of the differential-theta representation
of the Riemann Xi function, obtained by dominated differentiation.
-/

noncomputable section

open MeasureTheory Set Filter

namespace HodgeProofHP

theorem hpThetaPhiCosIntegrandSecond_integrableOn (z : ℂ) :
    IntegrableOn (hpThetaPhiCosIntegrandSecond z)
      (Set.Ioi 0) volume := by
  have hG := hpThetaPhi_secondMoment_exp_integrableOn ‖z‖
  apply hG.norm.mono'
    (hpThetaPhiCosIntegrandSecond_continuous z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact hpThetaPhiCosIntegrandSecond_norm_le
    z u ‖z‖ (le_of_lt hu) le_rfl

theorem hpThetaPhiCosIntegrandThird_integrableOn (z : ℂ) :
    IntegrableOn (hpThetaPhiCosIntegrandThird z)
      (Set.Ioi 0) volume := by
  have hG := hpThetaPhi_thirdMoment_exp_integrableOn ‖z‖
  apply hG.norm.mono'
    (hpThetaPhiCosIntegrandThird_continuous z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact hpThetaPhiCosIntegrandThird_norm_le
    z u ‖z‖ (le_of_lt hu) le_rfl

theorem hpRiemannXiCritical_secondDeriv_hasDerivAt_phi_integral
    (z : ℂ) :
    HasDerivAt (deriv (deriv hpRiemannXiCritical))
      (∫ u : ℝ in Set.Ioi 0, hpThetaPhiCosIntegrandThird z u)
      z := by
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi 0))
      (F := hpThetaPhiCosIntegrandSecond)
      (F' := hpThetaPhiCosIntegrandThird)
      (bound := fun u : ℝ =>
        ‖u ^ 3 * Real.exp ((‖z‖ + 1) * u) *
          hpRiemannThetaDifferentialKernel u‖)
      (x₀ := z)
      (s := Metric.ball z 1)
      (Metric.ball_mem_nhds z (by norm_num))
      (Filter.Eventually.of_forall fun w =>
        (hpThetaPhiCosIntegrandSecond_continuous w).aestronglyMeasurable)
      (hpThetaPhiCosIntegrandSecond_integrableOn z)
      (hpThetaPhiCosIntegrandThird_continuous z).aestronglyMeasurable
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        intro w hw
        have hdist : ‖w - z‖ < 1 := by
          simpa only [Metric.mem_ball, dist_eq_norm] using hw
        have htri := norm_add_le (w - z) z
        have hsum : (w - z) + z = w := by ring
        rw [hsum] at htri
        have hwbound : ‖w‖ ≤ ‖z‖ + 1 := by linarith
        exact hpThetaPhiCosIntegrandThird_norm_le
          w u (‖z‖ + 1) (le_of_lt hu) hwbound)
      (hpThetaPhi_thirdMoment_exp_integrableOn (‖z‖ + 1)).norm
      (Filter.Eventually.of_forall fun u w _ =>
        hpThetaPhiCosIntegrandSecond_hasDerivAt w u)
  have heq :
      (fun w : ℂ =>
        ∫ u : ℝ in Set.Ioi 0, hpThetaPhiCosIntegrandSecond w u) =
          deriv (deriv hpRiemannXiCritical) := by
    funext w
    exact (hpRiemannXiCritical_secondDeriv_eq_phi_integral w).symm
  rw [heq] at h
  exact h.2

theorem hpRiemannXiCritical_thirdDeriv_eq_phi_integral (z : ℂ) :
    deriv (deriv (deriv hpRiemannXiCritical)) z =
      ∫ u : ℝ in Set.Ioi 0, hpThetaPhiCosIntegrandThird z u :=
  (hpRiemannXiCritical_secondDeriv_hasDerivAt_phi_integral z).deriv

theorem hpRiemannXiCritical_thirdDeriv_zero :
    deriv (deriv (deriv hpRiemannXiCritical)) 0 = 0 := by
  rw [hpRiemannXiCritical_thirdDeriv_eq_phi_integral]
  simp only [hpThetaPhiCosIntegrandThird_zero, integral_zero]

#print axioms hpThetaPhiCosIntegrandSecond_integrableOn
#print axioms hpThetaPhiCosIntegrandThird_integrableOn
#print axioms hpRiemannXiCritical_secondDeriv_hasDerivAt_phi_integral
#print axioms hpRiemannXiCritical_thirdDeriv_eq_phi_integral
#print axioms hpRiemannXiCritical_thirdDeriv_zero

end HodgeProofHP
