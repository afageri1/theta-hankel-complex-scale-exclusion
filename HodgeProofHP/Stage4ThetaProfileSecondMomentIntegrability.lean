import HodgeProofHP.Stage4ThetaSecondMomentBoundaryDecay

/-!
Integrability of the polynomial weights used in second-moment
integration by parts on the positive half-line.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaSecondMoment_sq_le_exp_two_mul
    (u : ℝ) (hu : 0 ≤ u) :
    u ^ 2 ≤ Real.exp (2 * u) := by
  have hue : u ≤ Real.exp u := by
    linarith [Real.add_one_le_exp u]
  have hsq := mul_self_le_mul_self hu hue
  calc
    u ^ 2 ≤ Real.exp u * Real.exp u := by
      simpa only [pow_two] using hsq
    _ = Real.exp (2 * u) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem hpThetaSecondMoment_profile_weight_integrableOn :
    IntegrableOn
      (fun u : ℝ => u ^ 2 * hpRiemannThetaLogProfile u)
      (Set.Ioi 0) volume := by
  have hmajor :
      IntegrableOn
        (fun u : ℝ =>
          ‖Real.exp (2 * u) * hpRiemannThetaLogProfile u‖)
        (Set.Ioi 0) volume :=
    (hpRiemannThetaLogProfile_exp_weighted_integrableOn
      (2 : ℝ)).norm
  apply hmajor.mono'
    (((continuous_id.pow 2).mul
      hpRiemannThetaLogProfile_continuous).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  calc
    ‖u ^ 2 * hpRiemannThetaLogProfile u‖ =
        u ^ 2 * ‖hpRiemannThetaLogProfile u‖ := by
          rw [norm_mul, Real.norm_eq_abs,
            abs_of_nonneg (sq_nonneg u)]
    _ ≤ Real.exp (2 * u) * ‖hpRiemannThetaLogProfile u‖ :=
      mul_le_mul_of_nonneg_right
        (hpThetaSecondMoment_sq_le_exp_two_mul u hu0)
        (norm_nonneg _)
    _ = ‖Real.exp (2 * u) * hpRiemannThetaLogProfile u‖ := by
      simp only [norm_mul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos (2 * u))]

theorem hpThetaSecondMoment_secondDeriv_weight_integrableOn :
    IntegrableOn
      (fun u : ℝ =>
        u ^ 2 * deriv (deriv hpRiemannThetaLogProfile) u)
      (Set.Ioi 0) volume := by
  have h :=
    hpThetaPhi_secondMoment_integrableOn.add
      (hpThetaSecondMoment_profile_weight_integrableOn.const_mul
        (1 / 4 : ℝ))
  apply h.congr
  filter_upwards [] with u
  change
    u ^ 2 * hpRiemannThetaDifferentialKernel u +
        (1 / 4 : ℝ) * (u ^ 2 * hpRiemannThetaLogProfile u) =
      u ^ 2 * deriv (deriv hpRiemannThetaLogProfile) u
  unfold hpRiemannThetaDifferentialKernel
  ring

#print axioms hpThetaSecondMoment_sq_le_exp_two_mul
#print axioms hpThetaSecondMoment_profile_weight_integrableOn
#print axioms hpThetaSecondMoment_secondDeriv_weight_integrableOn

end HodgeProofHP
