import HodgeProofHP.Stage4ThetaPhiMomentIntegrability

/-!
Integrability of the fourth moment of the differential theta kernel,
including arbitrary real exponential weights.
-/

noncomputable section

open MeasureTheory Set

namespace HodgeProofHP

theorem hpThetaPhi_fourthPower_le_exp_four_mul
    (u : ℝ) (hu : 0 ≤ u) :
    u ^ 4 ≤ Real.exp (4 * u) := by
  have huexp : u ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    linarith
  have hsq : u ^ 2 ≤ (Real.exp u) ^ 2 := by
    simpa only [pow_two] using
      (mul_le_mul huexp huexp hu
        (le_of_lt (Real.exp_pos u)))
  have hfour :
      u ^ 2 * u ^ 2 ≤
        (Real.exp u) ^ 2 * (Real.exp u) ^ 2 :=
    mul_le_mul hsq hsq (sq_nonneg u)
      (sq_nonneg (Real.exp u))
  have hexp :
      Real.exp (4 * u) =
        (Real.exp u) ^ 2 * (Real.exp u) ^ 2 := by
    rw [show 4 * u = (u + u) + (u + u) by ring,
      Real.exp_add, Real.exp_add]
    ring
  calc
    u ^ 4 = u ^ 2 * u ^ 2 := by ring
    _ ≤ (Real.exp u) ^ 2 * (Real.exp u) ^ 2 := hfour
    _ = Real.exp (4 * u) := hexp.symm

theorem hpThetaPhi_fourthMoment_exp_integrableOn (c : ℝ) :
    IntegrableOn
      (fun u : ℝ =>
        u ^ 4 * Real.exp (c * u) *
          hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume := by
  have hG := hpThetaPhi_exp_weighted_integrableOn (c + 4)
  have hcont :
      Continuous
        (fun u : ℝ =>
          u ^ 4 * Real.exp (c * u) *
            hpRiemannThetaDifferentialKernel u) :=
    ((continuous_id.pow 4).mul
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).mul
      hpRiemannThetaDifferentialKernel_continuous
  apply hG.norm.mono' hcont.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have hu4 : 0 ≤ u ^ 4 := by positivity
  have hweight :
      u ^ 4 * Real.exp (c * u) ≤
        Real.exp ((c + 4) * u) := by
    calc
      u ^ 4 * Real.exp (c * u) ≤
          Real.exp (4 * u) * Real.exp (c * u) :=
        mul_le_mul_of_nonneg_right
          (hpThetaPhi_fourthPower_le_exp_four_mul u hu0)
          (le_of_lt (Real.exp_pos (c * u)))
      _ = Real.exp ((c + 4) * u) := by
        rw [← Real.exp_add]
        congr 1
        ring
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hu4,
    abs_of_pos (Real.exp_pos (c * u)),
    abs_of_pos (Real.exp_pos ((c + 4) * u))]
  exact mul_le_mul_of_nonneg_right hweight
    (abs_nonneg (hpRiemannThetaDifferentialKernel u))

theorem hpThetaPhi_fourthMoment_integrableOn :
    IntegrableOn
      (fun u : ℝ => u ^ 4 * hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume := by
  simpa using hpThetaPhi_fourthMoment_exp_integrableOn (0 : ℝ)

#print axioms hpThetaPhi_fourthPower_le_exp_four_mul
#print axioms hpThetaPhi_fourthMoment_exp_integrableOn
#print axioms hpThetaPhi_fourthMoment_integrableOn

end HodgeProofHP
