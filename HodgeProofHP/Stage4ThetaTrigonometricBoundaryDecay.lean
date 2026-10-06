import HodgeProofHP.Stage4ThetaProfileWeightedDecay
import Mathlib.Analysis.Complex.Trigonometric

/-!
Vanishing trigonometric boundary terms for the logarithmic theta profile.
The frequency parameter may be complex.
-/

noncomputable section

namespace HodgeProofHP

open Filter
open scoped Topology

theorem hpTheta_mul_complex_exp_tendsto_zero
    (f : ℝ → ℝ)
    (hf : ∀ c : ℝ,
      Tendsto (fun u : ℝ => Real.exp (c * u) * f u)
        atTop (𝓝 0))
    (a : ℂ) :
    Tendsto
      (fun u : ℝ => (f u : ℂ) * Complex.exp (a * (u : ℂ)))
      atTop (𝓝 0) := by
  have hnorm :
      ∀ u : ℝ,
        ‖(f u : ℂ) * Complex.exp (a * (u : ℂ))‖ =
          ‖Real.exp (a.re * u) * f u‖ := by
    intro u
    simp [norm_mul, Complex.norm_exp, Real.norm_eq_abs, mul_comm]
  have hmajor :
      Tendsto
        (fun u : ℝ => ‖Real.exp (a.re * u) * f u‖)
        atTop (𝓝 0) := by
    simpa only [norm_zero] using (hf a.re).norm
  apply squeeze_zero_norm' _ hmajor
  filter_upwards [] with u
  exact (hnorm u).le

theorem hpTheta_mul_complex_cos_tendsto_zero
    (f : ℝ → ℝ)
    (hf : ∀ c : ℝ,
      Tendsto (fun u : ℝ => Real.exp (c * u) * f u)
        atTop (𝓝 0))
    (t : ℂ) :
    Tendsto
      (fun u : ℝ => (f u : ℂ) * Complex.cos (t * (u : ℂ)))
      atTop (𝓝 0) := by
  have hplus := hpTheta_mul_complex_exp_tendsto_zero f hf (t * Complex.I)
  have hminus := hpTheta_mul_complex_exp_tendsto_zero f hf (-t * Complex.I)
  have hsum :
      Tendsto
        (fun u : ℝ =>
          ((f u : ℂ) * Complex.exp ((t * Complex.I) * (u : ℂ)) +
            (f u : ℂ) * Complex.exp ((-t * Complex.I) * (u : ℂ))) / 2)
        atTop (𝓝 0) := by
    simpa only [zero_add, zero_div] using
      (hplus.add hminus).div_const (2 : ℂ)
  have hfun :
      (fun u : ℝ => (f u : ℂ) * Complex.cos (t * (u : ℂ))) =
      (fun u : ℝ =>
        ((f u : ℂ) * Complex.exp ((t * Complex.I) * (u : ℂ)) +
          (f u : ℂ) * Complex.exp ((-t * Complex.I) * (u : ℂ))) / 2) := by
    funext u
    have hpos :
        (t * (u : ℂ)) * Complex.I =
          (t * Complex.I) * (u : ℂ) := by ring
    have hneg :
        -(t * (u : ℂ)) * Complex.I =
          (-t * Complex.I) * (u : ℂ) := by ring
    rw [Complex.cos, hpos, hneg]
    ring
  rw [hfun]
  exact hsum

theorem hpTheta_mul_complex_sin_tendsto_zero
    (f : ℝ → ℝ)
    (hf : ∀ c : ℝ,
      Tendsto (fun u : ℝ => Real.exp (c * u) * f u)
        atTop (𝓝 0))
    (t : ℂ) :
    Tendsto
      (fun u : ℝ => (f u : ℂ) * Complex.sin (t * (u : ℂ)))
      atTop (𝓝 0) := by
  have hplus := hpTheta_mul_complex_exp_tendsto_zero f hf (t * Complex.I)
  have hminus := hpTheta_mul_complex_exp_tendsto_zero f hf (-t * Complex.I)
  have hdiff :
      Tendsto
        (fun u : ℝ =>
          (((f u : ℂ) * Complex.exp ((-t * Complex.I) * (u : ℂ)) -
            (f u : ℂ) * Complex.exp ((t * Complex.I) * (u : ℂ))) *
              Complex.I) / 2)
        atTop (𝓝 0) := by
    simpa only [sub_zero, zero_mul, zero_div] using
      ((hminus.sub hplus).mul_const Complex.I).div_const (2 : ℂ)
  have hfun :
      (fun u : ℝ => (f u : ℂ) * Complex.sin (t * (u : ℂ))) =
      (fun u : ℝ =>
        (((f u : ℂ) * Complex.exp ((-t * Complex.I) * (u : ℂ)) -
          (f u : ℂ) * Complex.exp ((t * Complex.I) * (u : ℂ))) *
            Complex.I) / 2) := by
    funext u
    have hpos :
        (t * (u : ℂ)) * Complex.I =
          (t * Complex.I) * (u : ℂ) := by ring
    have hneg :
        -(t * (u : ℂ)) * Complex.I =
          (-t * Complex.I) * (u : ℂ) := by ring
    rw [Complex.sin, hpos, hneg]
    ring
  rw [hfun]
  exact hdiff

theorem hpRiemannThetaLogProfile_cos_boundary_tendsto_zero
    (t : ℂ) :
    Tendsto
      (fun u : ℝ =>
        (hpRiemannThetaLogProfile u : ℂ) *
          Complex.cos (t * (u : ℂ)))
      atTop (𝓝 0) := by
  exact hpTheta_mul_complex_cos_tendsto_zero
    hpRiemannThetaLogProfile
    hpRiemannThetaLogProfile_exp_weighted_tendsto_zero t

theorem hpRiemannThetaLogProfile_sin_boundary_tendsto_zero
    (t : ℂ) :
    Tendsto
      (fun u : ℝ =>
        (hpRiemannThetaLogProfile u : ℂ) *
          Complex.sin (t * (u : ℂ)))
      atTop (𝓝 0) := by
  exact hpTheta_mul_complex_sin_tendsto_zero
    hpRiemannThetaLogProfile
    hpRiemannThetaLogProfile_exp_weighted_tendsto_zero t

theorem hpRiemannThetaLogProfile_deriv_cos_boundary_tendsto_zero
    (t : ℂ) :
    Tendsto
      (fun u : ℝ =>
        ((deriv hpRiemannThetaLogProfile u : ℝ) : ℂ) *
          Complex.cos (t * (u : ℂ)))
      atTop (𝓝 0) := by
  exact hpTheta_mul_complex_cos_tendsto_zero
    (deriv hpRiemannThetaLogProfile)
    hpRiemannThetaLogProfile_deriv_exp_weighted_tendsto_zero t

theorem hpRiemannThetaLogProfile_deriv_sin_boundary_tendsto_zero
    (t : ℂ) :
    Tendsto
      (fun u : ℝ =>
        ((deriv hpRiemannThetaLogProfile u : ℝ) : ℂ) *
          Complex.sin (t * (u : ℂ)))
      atTop (𝓝 0) := by
  exact hpTheta_mul_complex_sin_tendsto_zero
    (deriv hpRiemannThetaLogProfile)
    hpRiemannThetaLogProfile_deriv_exp_weighted_tendsto_zero t

#print axioms hpTheta_mul_complex_exp_tendsto_zero
#print axioms hpTheta_mul_complex_cos_tendsto_zero
#print axioms hpTheta_mul_complex_sin_tendsto_zero
#print axioms hpRiemannThetaLogProfile_cos_boundary_tendsto_zero
#print axioms hpRiemannThetaLogProfile_sin_boundary_tendsto_zero
#print axioms hpRiemannThetaLogProfile_deriv_cos_boundary_tendsto_zero
#print axioms hpRiemannThetaLogProfile_deriv_sin_boundary_tendsto_zero

end HodgeProofHP
