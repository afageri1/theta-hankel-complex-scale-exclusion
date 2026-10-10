#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4RiemannXiCosineIntegral.lean <<'LEAN'
import HodgeProofHP.Stage4RiemannXiExponentialSimplified
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
A cosine integral representation of the critical Riemann xi function.
The parameter is allowed to be complex.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpThetaCritical_exp_sum (t : ℂ) (u : ℝ) :
    Complex.exp ((1 - (1 / 2 + Complex.I * t)) * (u : ℂ)) +
        Complex.exp ((1 / 2 + Complex.I * t) * (u : ℂ)) =
      2 * (↑(Real.exp (u / 2)) : ℂ) *
        Complex.cos (t * (u : ℂ)) := by
  have hminus :
      (1 - (1 / 2 + Complex.I * t)) * (u : ℂ) =
        (↑(u / 2) : ℂ) + (-(t * (u : ℂ))) * Complex.I := by
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  have hplus :
      (1 / 2 + Complex.I * t) * (u : ℂ) =
        (↑(u / 2) : ℂ) + (t * (u : ℂ)) * Complex.I := by
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  rw [hminus, hplus, Complex.exp_add, Complex.exp_add,
    ← Complex.cos_sub_sin_I, ← Complex.cos_add_sin_I,
    ← Complex.ofReal_exp]
  ring

/-- The cosine integrand before integration by parts. -/
def hpRiemannThetaCosineIntegrand
    (t : ℂ) (u : ℝ) : ℂ :=
  (↑(Real.exp (u / 2)) : ℂ) *
    (↑(hpRiemannThetaKernel (Real.exp (2 * u))) : ℂ) *
    Complex.cos (t * (u : ℂ))

theorem hpRiemannTheta_critical_exponential_eq_four_cosine
    (t : ℂ) (u : ℝ) :
    hpRiemannThetaExponentialIntegrand
        (1 / 2 + Complex.I * t) u =
      4 * hpRiemannThetaCosineIntegrand t u := by
  unfold hpRiemannThetaExponentialIntegrand
    hpRiemannThetaCosineIntegrand
  rw [hpThetaCritical_exp_sum]
  ring

theorem hpRiemannTheta_cosine_recover (t : ℂ) (u : ℝ) :
    (1 / 4 : ℂ) •
        hpRiemannThetaExponentialIntegrand
          (1 / 2 + Complex.I * t) u =
      hpRiemannThetaCosineIntegrand t u := by
  rw [smul_eq_mul,
    hpRiemannTheta_critical_exponential_eq_four_cosine]
  ring

theorem hpRiemannTheta_cosine_integrable (t : ℂ) :
    IntegrableOn (hpRiemannThetaCosineIntegrand t)
      (Set.Ioi 0) := by
  have hi := hpRiemannTheta_exponential_integrable
    (1 / 2 + Complex.I * t)
  have hs := MeasureTheory.Integrable.fun_smul (1 / 4 : ℂ) hi
  simpa only [IntegrableOn, hpRiemannTheta_cosine_recover] using hs

theorem hpRiemannTheta_cosine_norm_integrable (t : ℂ) :
    IntegrableOn
      (fun u => ‖hpRiemannThetaCosineIntegrand t u‖)
      (Set.Ioi 0) := by
  exact (hpRiemannTheta_cosine_integrable t).norm

theorem hpRiemannTheta_critical_exponential_integral_eq
    (t : ℂ) :
    (∫ u in Set.Ioi (0 : ℝ),
      hpRiemannThetaExponentialIntegrand
        (1 / 2 + Complex.I * t) u) =
      4 * (∫ u in Set.Ioi (0 : ℝ),
        hpRiemannThetaCosineIntegrand t u) := by
  have heq :
      hpRiemannThetaExponentialIntegrand
          (1 / 2 + Complex.I * t) =
        fun u => (4 : ℂ) • hpRiemannThetaCosineIntegrand t u := by
    funext u
    rw [smul_eq_mul]
    exact hpRiemannTheta_critical_exponential_eq_four_cosine t u
  rw [heq, integral_smul, smul_eq_mul]

theorem hpRiemannXiCritical_coefficient (t : ℂ) :
    (1 / 2 + Complex.I * t) *
        ((1 / 2 + Complex.I * t) - 1) =
      -(t ^ 2 + 1 / 4) := by
  calc
    (1 / 2 + Complex.I * t) *
        ((1 / 2 + Complex.I * t) - 1) =
      Complex.I ^ 2 * t ^ 2 - 1 / 4 := by
        ring
    _ = -(t ^ 2 + 1 / 4) := by
      rw [Complex.I_sq]
      ring

theorem hpRiemannXiCritical_eq_cosine_integral (t : ℂ) :
    hpRiemannXiCritical t =
      1 / 2 - (t ^ 2 + 1 / 4) *
        (∫ u in Set.Ioi (0 : ℝ),
          hpRiemannThetaCosineIntegrand t u) := by
  rw [hpRiemannXiCritical_eq_exponential_integral,
    hpRiemannTheta_critical_exponential_integral_eq,
    hpRiemannXiCritical_coefficient]
  ring

#print axioms hpThetaCritical_exp_sum
#print axioms hpRiemannTheta_critical_exponential_eq_four_cosine
#print axioms hpRiemannTheta_cosine_integrable
#print axioms hpRiemannTheta_cosine_norm_integrable
#print axioms hpRiemannTheta_critical_exponential_integral_eq
#print axioms hpRiemannXiCritical_coefficient
#print axioms hpRiemannXiCritical_eq_cosine_integral

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage4RiemannXiExponentialSimplified
lake env lean HodgeProofHP/Stage4RiemannXiCosineIntegral.lean
lake build HodgeProofHP.Stage4RiemannXiCosineIntegral
