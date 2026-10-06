import HodgeProofHP.Stage4ThetaTrigonometricBoundaryDecay
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
Integrability of exponential-weighted theta profiles on the positive half-line.
-/

noncomputable section

namespace HodgeProofHP

open Filter MeasureTheory
open scoped Topology

theorem hpTheta_weighted_isBigO_exp_neg_of_decay
    (f : ℝ → ℝ)
    (hf : ∀ c : ℝ,
      Tendsto (fun u : ℝ => Real.exp (c * u) * f u)
        atTop (𝓝 0))
    (c : ℝ) :
    Asymptotics.IsBigO atTop
      (fun u : ℝ => Real.exp (c * u) * f u)
      (fun u : ℝ => Real.exp (-u)) := by
  have hnormlim :
      Tendsto
        (fun u : ℝ => ‖Real.exp ((c + 1) * u) * f u‖)
        atTop (𝓝 0) := by
    simpa only [norm_zero] using (hf (c + 1)).norm
  have hsmall :
      ∀ᶠ u : ℝ in atTop,
        ‖Real.exp ((c + 1) * u) * f u‖ < 1 :=
    hnormlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [hsmall] with u hu
  have heq :
      Real.exp (-u) * (Real.exp ((c + 1) * u) * f u) =
        Real.exp (c * u) * f u := by
    rw [← mul_assoc, ← Real.exp_add]
    have hexponent : -u + (c + 1) * u = c * u := by ring
    rw [hexponent]
  have hmul :=
    mul_le_mul_of_nonneg_left hu.le (Real.exp_pos (-u)).le
  have hbound :
      ‖Real.exp (c * u) * f u‖ ≤ Real.exp (-u) := by
    calc
      ‖Real.exp (c * u) * f u‖ =
          ‖Real.exp (-u) * (Real.exp ((c + 1) * u) * f u)‖ :=
        congrArg norm heq.symm
      _ = Real.exp (-u) *
          ‖Real.exp ((c + 1) * u) * f u‖ := by
        rw [norm_mul, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos (-u))]
      _ ≤ Real.exp (-u) := by
        simpa only [mul_one] using hmul
  simpa only [one_mul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (-u))] using hbound

theorem hpTheta_weighted_integrableOn_of_continuous_decay
    (f : ℝ → ℝ) (hcont : Continuous f)
    (hf : ∀ c : ℝ,
      Tendsto (fun u : ℝ => Real.exp (c * u) * f u)
        atTop (𝓝 0))
    (c : ℝ) :
    IntegrableOn
      (fun u : ℝ => Real.exp (c * u) * f u)
      (Set.Ioi 0) volume := by
  have hweight :
      Continuous (fun u : ℝ => Real.exp (c * u) * f u) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hcont
  have hO :
      Asymptotics.IsBigO atTop
        (fun u : ℝ => Real.exp (c * u) * f u)
        (fun u : ℝ => Real.exp (-(1 : ℝ) * u)) := by
    simpa only [neg_one_mul] using
      hpTheta_weighted_isBigO_exp_neg_of_decay f hf c
  exact integrable_of_isBigO_exp_neg
    (by norm_num : (0 : ℝ) < 1) hweight.continuousOn hO

theorem hpRiemannThetaLogProfile_exp_weighted_integrableOn
    (c : ℝ) :
    IntegrableOn
      (fun u : ℝ => Real.exp (c * u) * hpRiemannThetaLogProfile u)
      (Set.Ioi 0) volume := by
  exact hpTheta_weighted_integrableOn_of_continuous_decay
    hpRiemannThetaLogProfile
    hpRiemannThetaLogProfile_continuous
    hpRiemannThetaLogProfile_exp_weighted_tendsto_zero c

theorem hpRiemannThetaLogProfile_deriv_exp_weighted_integrableOn
    (c : ℝ) :
    IntegrableOn
      (fun u : ℝ =>
        Real.exp (c * u) * deriv hpRiemannThetaLogProfile u)
      (Set.Ioi 0) volume := by
  exact hpTheta_weighted_integrableOn_of_continuous_decay
    (deriv hpRiemannThetaLogProfile)
    hpRiemannThetaLogProfile_deriv_continuous
    hpRiemannThetaLogProfile_deriv_exp_weighted_tendsto_zero c

theorem hpRiemannThetaLogProfile_integrableOn :
    IntegrableOn hpRiemannThetaLogProfile (Set.Ioi 0) volume := by
  simpa only [zero_mul, Real.exp_zero, one_mul] using
    hpRiemannThetaLogProfile_exp_weighted_integrableOn 0

theorem hpRiemannThetaLogProfile_deriv_integrableOn :
    IntegrableOn (deriv hpRiemannThetaLogProfile)
      (Set.Ioi 0) volume := by
  simpa only [zero_mul, Real.exp_zero, one_mul] using
    hpRiemannThetaLogProfile_deriv_exp_weighted_integrableOn 0

#print axioms hpTheta_weighted_isBigO_exp_neg_of_decay
#print axioms hpTheta_weighted_integrableOn_of_continuous_decay
#print axioms hpRiemannThetaLogProfile_exp_weighted_integrableOn
#print axioms hpRiemannThetaLogProfile_deriv_exp_weighted_integrableOn
#print axioms hpRiemannThetaLogProfile_integrableOn
#print axioms hpRiemannThetaLogProfile_deriv_integrableOn

end HodgeProofHP
