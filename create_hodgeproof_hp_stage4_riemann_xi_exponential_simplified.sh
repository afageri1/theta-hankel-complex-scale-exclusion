#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4RiemannXiExponentialSimplified.lean <<'LEAN'
import HodgeProofHP.Stage4RiemannXiLogExponential
import Mathlib.Tactic.Ring

/-!
Combine the exponential Jacobian with the logarithmic theta integrand.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpThetaLog_exp_weight (u : ℝ) (a : ℂ) :
    (↑(Real.exp (2 * u)) : ℂ) *
        Complex.exp ((↑(2 * u) : ℂ) * (a / 2 - 1)) =
      Complex.exp (a * (u : ℂ)) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

theorem hpThetaLog_weighted_exp_sum
    (u : ℝ) (a b k : ℂ) :
    (2 * Real.exp (2 * u) : ℝ) •
        ((Complex.exp ((↑(2 * u) : ℂ) * (a / 2 - 1)) +
          Complex.exp ((↑(2 * u) : ℂ) * (b / 2 - 1))) • k) =
      2 * (Complex.exp (a * (u : ℂ)) +
        Complex.exp (b * (u : ℂ))) * k := by
  have hsum :
      (↑(Real.exp (2 * u)) : ℂ) *
          (Complex.exp ((↑(2 * u) : ℂ) * (a / 2 - 1)) +
            Complex.exp ((↑(2 * u) : ℂ) * (b / 2 - 1))) =
        Complex.exp (a * (u : ℂ)) +
          Complex.exp (b * (u : ℂ)) := by
    rw [mul_add, hpThetaLog_exp_weight u a,
      hpThetaLog_exp_weight u b]
  simp only [Complex.real_smul, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_ofNat] at hsum ⊢
  rw [← hsum]
  ring

/-- Simplified exponential theta integrand. -/
def hpRiemannThetaExponentialIntegrand
    (s : ℂ) (u : ℝ) : ℂ :=
  2 * (Complex.exp ((1 - s) * (u : ℂ)) +
    Complex.exp (s * (u : ℂ))) *
    (↑(hpRiemannThetaKernel (Real.exp (2 * u))) : ℂ)

theorem hpRiemannTheta_log_exponential_eq_simplified
    (s : ℂ) (u : ℝ) :
    hpRiemannThetaLogExponentialIntegrand s u =
      hpRiemannThetaExponentialIntegrand s u := by
  unfold hpRiemannThetaLogExponentialIntegrand
    hpRiemannThetaExponentialIntegrand
  exact hpThetaLog_weighted_exp_sum u (1 - s) s
    (↑(hpRiemannThetaKernel (Real.exp (2 * u))) : ℂ)

theorem hpRiemannTheta_exponential_function_eq (s : ℂ) :
    hpRiemannThetaLogExponentialIntegrand s =
      hpRiemannThetaExponentialIntegrand s := by
  funext u
  exact hpRiemannTheta_log_exponential_eq_simplified s u

theorem hpRiemannTheta_exponential_integrable (s : ℂ) :
    IntegrableOn (hpRiemannThetaExponentialIntegrand s)
      (Set.Ioi 0) := by
  have h := hpRiemannTheta_log_exponential_integrable s
  rw [hpRiemannTheta_exponential_function_eq s] at h
  exact h

theorem hpRiemannTheta_exponential_norm_integrable (s : ℂ) :
    IntegrableOn
      (fun u => ‖hpRiemannThetaExponentialIntegrand s u‖)
      (Set.Ioi 0) := by
  exact (hpRiemannTheta_exponential_integrable s).norm

theorem hpRiemannXi_eq_exponential_integral (s : ℂ) :
    hpRiemannXi s =
      (s * (s - 1) / 4) *
        (∫ u in Set.Ioi (0 : ℝ),
          hpRiemannThetaExponentialIntegrand s u) +
      1 / 2 := by
  have h := hpRiemannXi_eq_log_exponential_integral s
  rw [hpRiemannTheta_exponential_function_eq s] at h
  exact h

theorem hpRiemannXiCritical_eq_exponential_integral (t : ℂ) :
    hpRiemannXiCritical t =
      ((1 / 2 + Complex.I * t) *
        ((1 / 2 + Complex.I * t) - 1) / 4) *
        (∫ u in Set.Ioi (0 : ℝ),
          hpRiemannThetaExponentialIntegrand
            (1 / 2 + Complex.I * t) u) +
      1 / 2 := by
  exact hpRiemannXi_eq_exponential_integral
    (1 / 2 + Complex.I * t)

#print axioms hpThetaLog_exp_weight
#print axioms hpThetaLog_weighted_exp_sum
#print axioms hpRiemannTheta_log_exponential_eq_simplified
#print axioms hpRiemannTheta_exponential_integrable
#print axioms hpRiemannTheta_exponential_norm_integrable
#print axioms hpRiemannXi_eq_exponential_integral
#print axioms hpRiemannXiCritical_eq_exponential_integral

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage4RiemannXiLogExponential
lake env lean HodgeProofHP/Stage4RiemannXiExponentialSimplified.lean
lake build HodgeProofHP.Stage4RiemannXiExponentialSimplified
