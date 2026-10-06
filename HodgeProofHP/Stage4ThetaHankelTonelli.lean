import HodgeProofHP.Stage4ThetaHankelKernel

/-!
Tonelli's identity for the nonnegative squared norm of the
theta Hankel kernel on the positive quadrant.
No finiteness of the double integral is assumed.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpThetaHankelKernel_norm_sq_measurable :
    Measurable
      (fun p : ℝ × ℝ => ‖hpThetaHankelKernel p.1 p.2‖ ^ 2) :=
  (hpThetaHankelKernel_continuous.norm.pow 2).measurable

theorem hpThetaHankelKernel_norm_sq_ofReal_measurable :
    Measurable
      (fun p : ℝ × ℝ =>
        ENNReal.ofReal (‖hpThetaHankelKernel p.1 p.2‖ ^ 2)) :=
  hpThetaHankelKernel_norm_sq_measurable.ennreal_ofReal

theorem hpThetaHankelKernel_sq_lintegral_prod :
    (∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (‖hpThetaHankelKernel p.1 p.2‖ ^ 2)
      ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (Set.Ioi (0 : ℝ))))) =
      ∫⁻ x : ℝ in Set.Ioi 0,
        ∫⁻ y : ℝ in Set.Ioi 0,
          ENNReal.ofReal (‖hpThetaHankelKernel x y‖ ^ 2) := by
  exact lintegral_prod _
    hpThetaHankelKernel_norm_sq_ofReal_measurable.aemeasurable

theorem hpThetaHankelKernel_sq_lintegral_eq_phi_iterated :
    (∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (‖hpThetaHankelKernel p.1 p.2‖ ^ 2)
      ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (Set.Ioi (0 : ℝ))))) =
      ∫⁻ x : ℝ in Set.Ioi 0,
        ∫⁻ y : ℝ in Set.Ioi 0,
          ENNReal.ofReal
            (hpRiemannThetaDifferentialKernel (x + y) ^ 2) := by
  rw [hpThetaHankelKernel_sq_lintegral_prod]
  simp_rw [hpThetaHankelKernel_norm_sq]

#print axioms hpThetaHankelKernel_norm_sq_measurable
#print axioms hpThetaHankelKernel_norm_sq_ofReal_measurable
#print axioms hpThetaHankelKernel_sq_lintegral_prod
#print axioms hpThetaHankelKernel_sq_lintegral_eq_phi_iterated

end HodgeProofHP
