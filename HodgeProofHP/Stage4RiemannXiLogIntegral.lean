import HodgeProofHP.Stage4RiemannXiSingleIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.NormNum

/-!
The substitution x = exp (2 * u) in the symmetric xi integral.
The logarithmic integrand includes the Jacobian 2 * exp (2 * u).
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

def hpRiemannThetaLogIntegrand (s : ℂ) (u : ℝ) : ℂ :=
  (2 * Real.exp (2 * u) : ℝ) •
    hpRiemannThetaSymmetricMellinIntegrand s
      (Real.exp (2 * u))

theorem hpRiemannTheta_log_integral_eq_upper
    (s : ℂ) :
    (∫ u : ℝ in Set.Ioi 0,
      hpRiemannThetaLogIntegrand s u) =
    ∫ x : ℝ in Set.Ioi 1,
      hpRiemannThetaSymmetricMellinIntegrand s x := by
  let g : ℝ → ℂ := hpRiemannThetaSymmetricMellinIntegrand s
  let h : ℝ → ℂ := fun u => Real.exp u • g (Real.exp u)
  calc
    (∫ u : ℝ in Set.Ioi 0,
        hpRiemannThetaLogIntegrand s u) =
        (2 : ℝ) •
          ∫ u : ℝ in Set.Ioi 0, h (2 * u) := by
      change
        (∫ u : ℝ in Set.Ioi 0,
          (2 * Real.exp (2 * u) : ℝ) • g (Real.exp (2 * u))) =
        (2 : ℝ) •
          ∫ u : ℝ in Set.Ioi 0,
            Real.exp (2 * u) • g (Real.exp (2 * u))
      simp only [mul_smul]
      rw [integral_smul]
    _ = ∫ u : ℝ in Set.Ioi 0, h u := by
      simpa only [mul_zero] using
        (integral_comp_mul_left_Ioi' h 0
          (b := (2 : ℝ)) (by norm_num))
    _ = ∫ x : ℝ in Set.Ioi 1,
        hpRiemannThetaSymmetricMellinIntegrand s x := by
      simpa only [Real.exp_zero] using
        (integral_comp_exp_Ioi g 0)

theorem hpRiemannTheta_log_integrable
    (s : ℂ) :
    IntegrableOn (hpRiemannThetaLogIntegrand s) (Set.Ioi 0) := by
  let g : ℝ → ℂ := hpRiemannThetaSymmetricMellinIntegrand s
  have hg : IntegrableOn g (Set.Ioi 1) :=
    hpRiemannTheta_symmetric_mellin_integrable s
  have he :
      IntegrableOn
        (fun u : ℝ => Real.exp u • g (Real.exp u))
        (Set.Ioi 0) := by
    apply (integrableOn_comp_exp_Ioi g 0).2
    simpa only [Real.exp_zero] using hg
  have hd :
      IntegrableOn
        (fun u : ℝ =>
          Real.exp (2 * u) • g (Real.exp (2 * u)))
        (Set.Ioi 0) := by
    apply
      (integrableOn_Ioi_comp_mul_left_iff
        (fun u : ℝ => Real.exp u • g (Real.exp u))
        0 (a := (2 : ℝ)) (by norm_num)).2
    simpa only [mul_zero] using he
  change IntegrableOn
    (fun u : ℝ =>
      (2 * Real.exp (2 * u) : ℝ) • g (Real.exp (2 * u)))
    (Set.Ioi 0)
  simpa only [IntegrableOn, mul_smul] using (MeasureTheory.Integrable.fun_smul (2 : ℝ) hd)

theorem hpRiemannTheta_log_norm_integrable
    (s : ℂ) :
    IntegrableOn
      (fun u : ℝ => ‖hpRiemannThetaLogIntegrand s u‖)
      (Set.Ioi 0) := by
  exact (hpRiemannTheta_log_integrable s).norm

theorem hpRiemannXi_eq_log_integral
    (s : ℂ) :
    hpRiemannXi s =
      (s * (s - 1) / 4) *
        (∫ u : ℝ in Set.Ioi 0,
          hpRiemannThetaLogIntegrand s u) +
      1 / 2 := by
  rw [hpRiemannXi_eq_single_symmetric_integral,
    ← hpRiemannTheta_log_integral_eq_upper]

theorem hpRiemannXiCritical_eq_log_integral
    (t : ℂ) :
    hpRiemannXiCritical t =
      (((1 / 2 : ℂ) + Complex.I * t) *
        (((1 / 2 : ℂ) + Complex.I * t) - 1) / 4) *
        (∫ u : ℝ in Set.Ioi 0,
          hpRiemannThetaLogIntegrand
            ((1 / 2 : ℂ) + Complex.I * t) u) +
      1 / 2 := by
  exact hpRiemannXi_eq_log_integral
    ((1 / 2 : ℂ) + Complex.I * t)

end HodgeProofHP

#print axioms HodgeProofHP.hpRiemannTheta_log_integral_eq_upper
#print axioms HodgeProofHP.hpRiemannTheta_log_integrable
#print axioms HodgeProofHP.hpRiemannTheta_log_norm_integrable
#print axioms HodgeProofHP.hpRiemannXi_eq_log_integral
#print axioms HodgeProofHP.hpRiemannXiCritical_eq_log_integral
