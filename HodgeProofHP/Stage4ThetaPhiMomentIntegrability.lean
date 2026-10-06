import HodgeProofHP.Stage4ThetaFirstTraceMoments

/-!
Exponential integrability of the differential theta kernel
and integrability of its second moment on the positive half-line.
-/

noncomputable section

open MeasureTheory Set

namespace HodgeProofHP

theorem hpThetaPhi_exp_weighted_integrableOn (c : ℝ) :
    IntegrableOn
      (fun u : ℝ =>
        Real.exp (c * u) * hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume := by
  exact hpTheta_weighted_integrableOn_of_continuous_decay
    hpRiemannThetaDifferentialKernel
    hpRiemannThetaDifferentialKernel_continuous
    hpRiemannThetaDifferentialKernel_exp_weighted_tendsto_zero
    c

theorem hpThetaPhi_integrableOn :
    IntegrableOn hpRiemannThetaDifferentialKernel
      (Set.Ioi 0) volume := by
  simpa using hpThetaPhi_exp_weighted_integrableOn (0 : ℝ)

theorem hpThetaPhi_secondMoment_integrableOn :
    IntegrableOn
      (fun u : ℝ => u ^ 2 * hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume := by
  have hG := hpThetaPhi_exp_weighted_integrableOn (2 : ℝ)
  have hcont :
      Continuous
        (fun u : ℝ => u ^ 2 * hpRiemannThetaDifferentialKernel u) :=
    (continuous_id.pow 2).mul
      hpRiemannThetaDifferentialKernel_continuous
  apply hG.norm.mono' hcont.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have huexp : u ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    linarith
  have hsq : u ^ 2 ≤ (Real.exp u) ^ 2 := by
    simpa only [pow_two] using
      (mul_le_mul huexp huexp hu0
        (le_of_lt (Real.exp_pos u)))
  have hexp : Real.exp (2 * u) = (Real.exp u) ^ 2 := by
    rw [show 2 * u = u + u by ring, Real.exp_add, pow_two]
  have hweight : u ^ 2 ≤ Real.exp (2 * u) := by
    rw [hexp]
    exact hsq
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (sq_nonneg u),
    abs_of_pos (Real.exp_pos (2 * u))]
  exact mul_le_mul_of_nonneg_right hweight
    (abs_nonneg (hpRiemannThetaDifferentialKernel u))

#print axioms hpThetaPhi_exp_weighted_integrableOn
#print axioms hpThetaPhi_integrableOn
#print axioms hpThetaPhi_secondMoment_integrableOn

end HodgeProofHP
