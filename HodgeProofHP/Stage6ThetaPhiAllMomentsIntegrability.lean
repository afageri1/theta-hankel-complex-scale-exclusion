import HodgeProofHP.Stage4ThetaPhiMomentIntegrability
import HodgeProofHP.Stage5ThetaJensenFoundations
import Mathlib.Tactic

/-!
# All polynomial moments of the differential theta kernel

Extend the existing arbitrary exponential-weight integrability theorem
to every natural power, including arbitrary real exponential weights.
This supplies an analytic prerequisite for an all-orders xi expansion.
It does not assert that expansion or a general Jensen criterion.
-/

noncomputable section

open MeasureTheory Set

namespace HodgeProofHP

theorem hpThetaPhi_natPower_le_exp_mul
    (m : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    u ^ m ≤ Real.exp ((m : ℝ) * u) := by
  have huexp : u ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    linarith
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        u ^ (m + 1) = u ^ m * u := pow_succ u m
        _ ≤ Real.exp ((m : ℝ) * u) * Real.exp u :=
          mul_le_mul ih huexp hu (Real.exp_pos _).le
        _ = Real.exp (((m + 1 : ℕ) : ℝ) * u) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring

theorem hpThetaPhi_natMoment_exp_integrableOn (m : ℕ) (c : ℝ) :
    IntegrableOn
      (fun u : ℝ =>
        u ^ m * Real.exp (c * u) *
          hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume := by
  have hG := hpThetaPhi_exp_weighted_integrableOn (c + (m : ℝ))
  have hcont :
      Continuous
        (fun u : ℝ =>
          u ^ m * Real.exp (c * u) *
            hpRiemannThetaDifferentialKernel u) :=
    ((continuous_id.pow m).mul
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).mul
      hpRiemannThetaDifferentialKernel_continuous
  apply hG.norm.mono' hcont.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have hupow : 0 ≤ u ^ m := pow_nonneg hu0 m
  have hweight :
      u ^ m * Real.exp (c * u) ≤
        Real.exp ((c + (m : ℝ)) * u) := by
    calc
      u ^ m * Real.exp (c * u) ≤
          Real.exp ((m : ℝ) * u) * Real.exp (c * u) :=
        mul_le_mul_of_nonneg_right
          (hpThetaPhi_natPower_le_exp_mul m u hu0)
          (Real.exp_pos _).le
      _ = Real.exp ((c + (m : ℝ)) * u) := by
        rw [← Real.exp_add]
        congr 1
        ring
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hupow,
    abs_of_pos (Real.exp_pos (c * u)),
    abs_of_pos (Real.exp_pos ((c + (m : ℝ)) * u))]
  exact mul_le_mul_of_nonneg_right hweight
    (abs_nonneg (hpRiemannThetaDifferentialKernel u))

theorem hpThetaPhi_natMoment_integrableOn (m : ℕ) :
    IntegrableOn
      (fun u : ℝ => u ^ m * hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume := by
  simpa using hpThetaPhi_natMoment_exp_integrableOn m (0 : ℝ)

theorem hpThetaPhi_evenMoment_integrableOn (n : ℕ) :
    IntegrableOn
      (fun u : ℝ => u ^ (2 * n) * hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume :=
  hpThetaPhi_natMoment_integrableOn (2 * n)

#print axioms hpThetaPhi_natPower_le_exp_mul
#print axioms hpThetaPhi_natMoment_exp_integrableOn
#print axioms hpThetaPhi_natMoment_integrableOn
#print axioms hpThetaPhi_evenMoment_integrableOn

end HodgeProofHP
