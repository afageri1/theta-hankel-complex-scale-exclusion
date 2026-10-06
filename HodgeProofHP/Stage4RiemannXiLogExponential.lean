import HodgeProofHP.Stage4RiemannXiLogIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
Rewrite the logarithmic theta integrand using complex exponentials.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpOfRealExp_cpow (r : ℝ) (z : ℂ) :
    (↑(Real.exp r) : ℂ) ^ z =
      Complex.exp ((r : ℂ) * z) := by
  have hne : (↑(Real.exp r) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero r
  rw [Complex.cpow_def_of_ne_zero hne,
    ← Complex.ofReal_log (le_of_lt (Real.exp_pos r)),
    Real.log_exp]

/-- Exponential form of the logarithmic theta integrand. -/
def hpRiemannThetaLogExponentialIntegrand
    (s : ℂ) (u : ℝ) : ℂ :=
  (2 * Real.exp (2 * u) : ℝ) •
    ((Complex.exp ((↑(2 * u) : ℂ) * ((1 - s) / 2 - 1)) +
      Complex.exp ((↑(2 * u) : ℂ) * (s / 2 - 1))) •
      (↑(hpRiemannThetaKernel (Real.exp (2 * u))) : ℂ))

theorem hpRiemannTheta_log_eq_exponential
    (s : ℂ) (u : ℝ) :
    hpRiemannThetaLogIntegrand s u =
      hpRiemannThetaLogExponentialIntegrand s u := by
  simp only [hpRiemannThetaLogIntegrand,
    hpRiemannThetaSymmetricMellinIntegrand,
    hpRiemannThetaLogExponentialIntegrand,
    hpOfRealExp_cpow]

theorem hpRiemannTheta_log_function_eq_exponential (s : ℂ) :
    hpRiemannThetaLogIntegrand s =
      hpRiemannThetaLogExponentialIntegrand s := by
  funext u
  exact hpRiemannTheta_log_eq_exponential s u

theorem hpRiemannTheta_log_exponential_integrable (s : ℂ) :
    IntegrableOn
      (hpRiemannThetaLogExponentialIntegrand s)
      (Set.Ioi 0) := by
  have h := hpRiemannTheta_log_integrable s
  rw [hpRiemannTheta_log_function_eq_exponential s] at h
  exact h

theorem hpRiemannTheta_log_exponential_norm_integrable
    (s : ℂ) :
    IntegrableOn
      (fun u => ‖hpRiemannThetaLogExponentialIntegrand s u‖)
      (Set.Ioi 0) := by
  exact (hpRiemannTheta_log_exponential_integrable s).norm

theorem hpRiemannXi_eq_log_exponential_integral (s : ℂ) :
    hpRiemannXi s =
      (s * (s - 1) / 4) *
        (∫ u in Set.Ioi (0 : ℝ),
          hpRiemannThetaLogExponentialIntegrand s u) +
      1 / 2 := by
  have h := hpRiemannXi_eq_log_integral s
  rw [hpRiemannTheta_log_function_eq_exponential s] at h
  exact h

theorem hpRiemannXiCritical_eq_log_exponential_integral
    (t : ℂ) :
    hpRiemannXiCritical t =
      ((1 / 2 + Complex.I * t) *
        ((1 / 2 + Complex.I * t) - 1) / 4) *
        (∫ u in Set.Ioi (0 : ℝ),
          hpRiemannThetaLogExponentialIntegrand
            (1 / 2 + Complex.I * t) u) +
      1 / 2 := by
  exact hpRiemannXi_eq_log_exponential_integral
    (1 / 2 + Complex.I * t)

#print axioms hpOfRealExp_cpow
#print axioms hpRiemannTheta_log_eq_exponential
#print axioms hpRiemannTheta_log_exponential_integrable
#print axioms hpRiemannTheta_log_exponential_norm_integrable
#print axioms hpRiemannXi_eq_log_exponential_integral
#print axioms hpRiemannXiCritical_eq_log_exponential_integral

end HodgeProofHP
