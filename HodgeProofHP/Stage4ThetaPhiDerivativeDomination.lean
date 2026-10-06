import HodgeProofHP.Stage4ThetaPhiMomentIntegrability

/-!
Integrable exponential majorants for the first and second
parameter derivatives of the differential-theta cosine integral.
-/

noncomputable section

open MeasureTheory Set

namespace HodgeProofHP

theorem hpThetaPhi_firstMoment_exp_integrableOn (c : ℝ) :
    IntegrableOn
      (fun u : ℝ =>
        u * Real.exp (c * u) *
          hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume := by
  have hG := hpThetaPhi_exp_weighted_integrableOn (c + 1)
  have hcont :
      Continuous
        (fun u : ℝ =>
          u * Real.exp (c * u) *
            hpRiemannThetaDifferentialKernel u) :=
    (continuous_id.mul
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).mul
      hpRiemannThetaDifferentialKernel_continuous
  apply hG.norm.mono' hcont.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have huexp : u ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    linarith
  have hexp :
      Real.exp ((c + 1) * u) =
        Real.exp u * Real.exp (c * u) := by
    rw [show (c + 1) * u = u + c * u by ring, Real.exp_add]
  have hweight :
      u * Real.exp (c * u) ≤ Real.exp ((c + 1) * u) := by
    rw [hexp]
    exact mul_le_mul_of_nonneg_right huexp
      (le_of_lt (Real.exp_pos (c * u)))
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hu0,
    abs_of_pos (Real.exp_pos (c * u)),
    abs_of_pos (Real.exp_pos ((c + 1) * u))]
  exact mul_le_mul_of_nonneg_right hweight
    (abs_nonneg (hpRiemannThetaDifferentialKernel u))

theorem hpThetaPhi_secondMoment_exp_integrableOn (c : ℝ) :
    IntegrableOn
      (fun u : ℝ =>
        u ^ 2 * Real.exp (c * u) *
          hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume := by
  have hG := hpThetaPhi_exp_weighted_integrableOn (c + 2)
  have hcont :
      Continuous
        (fun u : ℝ =>
          u ^ 2 * Real.exp (c * u) *
            hpRiemannThetaDifferentialKernel u) :=
    ((continuous_id.pow 2).mul
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).mul
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
  have hexp :
      Real.exp ((c + 2) * u) =
        (Real.exp u) ^ 2 * Real.exp (c * u) := by
    rw [show (c + 2) * u = (u + u) + c * u by ring,
      Real.exp_add, Real.exp_add, pow_two]
  have hweight :
      u ^ 2 * Real.exp (c * u) ≤ Real.exp ((c + 2) * u) := by
    rw [hexp]
    exact mul_le_mul_of_nonneg_right hsq
      (le_of_lt (Real.exp_pos (c * u)))
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (sq_nonneg u),
    abs_of_pos (Real.exp_pos (c * u)),
    abs_of_pos (Real.exp_pos ((c + 2) * u))]
  exact mul_le_mul_of_nonneg_right hweight
    (abs_nonneg (hpRiemannThetaDifferentialKernel u))

theorem hpThetaPhi_derivativeMajorant_integrableOn (c : ℝ) :
    IntegrableOn
      (fun u : ℝ =>
        ‖Real.exp (c * u) *
            hpRiemannThetaDifferentialKernel u‖ +
        ‖u ^ 2 * Real.exp (c * u) *
            hpRiemannThetaDifferentialKernel u‖)
      (Set.Ioi 0) volume := by
  exact (hpThetaPhi_exp_weighted_integrableOn c).norm.add
    (hpThetaPhi_secondMoment_exp_integrableOn c).norm

#print axioms hpThetaPhi_firstMoment_exp_integrableOn
#print axioms hpThetaPhi_secondMoment_exp_integrableOn
#print axioms hpThetaPhi_derivativeMajorant_integrableOn

end HodgeProofHP
