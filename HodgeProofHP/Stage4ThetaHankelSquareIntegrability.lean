import HodgeProofHP.Stage4RiemannXiPhiRepresentation

/-!
Continuity and weighted square integrability of the theta differential kernel.
In particular, u * Phi(u)^2 is integrable on the positive half-line.
This is the one-dimensional integrability condition used for
the Hilbert-Schmidt norm of a Hankel kernel Phi(x+y).
-/

noncomputable section

open MeasureTheory Filter

namespace HodgeProofHP

theorem hpRiemannThetaDifferentialKernel_continuous :
    Continuous hpRiemannThetaDifferentialKernel := by
  have hB : Continuous hpRiemannThetaLogProfile :=
    continuous_iff_continuousAt.mpr
      (fun u => (hpRiemannThetaLogProfile_hasDerivAt u).continuousAt)
  unfold hpRiemannThetaDifferentialKernel
  exact hpRiemannThetaLogProfile_secondDeriv_continuous.sub
    (continuous_const.mul hB)

theorem hpRiemannThetaDifferentialKernel_sq_exp_weighted_tendsto_zero
    (c : ℝ) :
    Tendsto
      (fun u : ℝ =>
        Real.exp (c * u) * hpRiemannThetaDifferentialKernel u ^ 2)
      atTop (nhds 0) := by
  have h :=
    (hpRiemannThetaDifferentialKernel_exp_weighted_tendsto_zero c).mul
      hpRiemannThetaDifferentialKernel_tendsto_zero
  simpa only [pow_two, mul_assoc, mul_zero] using h

theorem hpRiemannThetaDifferentialKernel_sq_exp_weighted_integrableOn
    (c : ℝ) :
    IntegrableOn
      (fun u : ℝ =>
        Real.exp (c * u) * hpRiemannThetaDifferentialKernel u ^ 2)
      (Set.Ioi 0) volume :=
  hpTheta_weighted_integrableOn_of_continuous_decay
    (fun u : ℝ => hpRiemannThetaDifferentialKernel u ^ 2)
    (hpRiemannThetaDifferentialKernel_continuous.pow 2)
    hpRiemannThetaDifferentialKernel_sq_exp_weighted_tendsto_zero
    c

theorem hpRiemannThetaDifferentialKernel_sq_integrableOn :
    IntegrableOn
      (fun u : ℝ => hpRiemannThetaDifferentialKernel u ^ 2)
      (Set.Ioi 0) volume := by
  simpa only [zero_mul, Real.exp_zero, one_mul] using
    hpRiemannThetaDifferentialKernel_sq_exp_weighted_integrableOn 0

theorem hpRiemannThetaDifferentialKernel_hankel_weight_integrableOn :
    IntegrableOn
      (fun u : ℝ => u * hpRiemannThetaDifferentialKernel u ^ 2)
      (Set.Ioi 0) volume := by
  have hG :
      IntegrableOn
        (fun u : ℝ =>
          Real.exp u * hpRiemannThetaDifferentialKernel u ^ 2)
        (Set.Ioi 0) volume := by
    simpa only [one_mul] using
      hpRiemannThetaDifferentialKernel_sq_exp_weighted_integrableOn 1
  have hcont :
      Continuous
        (fun u : ℝ => u * hpRiemannThetaDifferentialKernel u ^ 2) :=
    continuous_id.mul (hpRiemannThetaDifferentialKernel_continuous.pow 2)
  apply hG.mono' hcont.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have hsq : 0 ≤ hpRiemannThetaDifferentialKernel u ^ 2 :=
    sq_nonneg _
  have huexp : u ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hu0 hsq)]
  exact mul_le_mul_of_nonneg_right huexp hsq

#print axioms hpRiemannThetaDifferentialKernel_continuous
#print axioms hpRiemannThetaDifferentialKernel_sq_exp_weighted_tendsto_zero
#print axioms hpRiemannThetaDifferentialKernel_sq_exp_weighted_integrableOn
#print axioms hpRiemannThetaDifferentialKernel_sq_integrableOn
#print axioms hpRiemannThetaDifferentialKernel_hankel_weight_integrableOn

end HodgeProofHP
