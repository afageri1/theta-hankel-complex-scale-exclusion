import HodgeProofHP.Stage4ThetaPhiParameterDerivatives
import Mathlib.Analysis.Complex.Trigonometric

/-!
Uniform bounds for the complex parameter derivatives
of the differential-theta cosine integrand.
-/

noncomputable section

namespace HodgeProofHP

theorem hpThetaPhi_complex_exp_norm_le (w : ℂ) :
    ‖Complex.exp w‖ ≤ Real.exp ‖w‖ := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr (Complex.re_le_norm w)

theorem hpThetaPhi_complex_cos_norm_le (w : ℂ) :
    ‖Complex.cos w‖ ≤ Real.exp ‖w‖ := by
  have hp :
      ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp ‖w‖ := by
    simpa only [norm_mul, Complex.norm_I, mul_one] using
      hpThetaPhi_complex_exp_norm_le (w * Complex.I)
  have hn :
      ‖Complex.exp (-w * Complex.I)‖ ≤ Real.exp ‖w‖ := by
    simpa only [norm_mul, norm_neg, Complex.norm_I, mul_one] using
      hpThetaPhi_complex_exp_norm_le (-w * Complex.I)
  change
    ‖(Complex.exp (w * Complex.I) +
      Complex.exp (-w * Complex.I)) / 2‖ ≤ Real.exp ‖w‖
  simp only [norm_div, Complex.norm_two]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  have hsum := norm_add_le
    (Complex.exp (w * Complex.I))
    (Complex.exp (-w * Complex.I))
  linarith

theorem hpThetaPhi_complex_sin_norm_le (w : ℂ) :
    ‖Complex.sin w‖ ≤ Real.exp ‖w‖ := by
  have hp :
      ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp ‖w‖ := by
    simpa only [norm_mul, Complex.norm_I, mul_one] using
      hpThetaPhi_complex_exp_norm_le (w * Complex.I)
  have hn :
      ‖Complex.exp (-w * Complex.I)‖ ≤ Real.exp ‖w‖ := by
    simpa only [norm_mul, norm_neg, Complex.norm_I, mul_one] using
      hpThetaPhi_complex_exp_norm_le (-w * Complex.I)
  change
    ‖(Complex.exp (-w * Complex.I) -
      Complex.exp (w * Complex.I)) * Complex.I / 2‖ ≤
      Real.exp ‖w‖
  simp only [norm_div, norm_mul, Complex.norm_I,
    Complex.norm_two, mul_one]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  have hsum := norm_sub_le
    (Complex.exp (-w * Complex.I))
    (Complex.exp (w * Complex.I))
  linarith

theorem hpThetaPhi_parameter_exp_bound
    (z : ℂ) (u c : ℝ) (hu : 0 ≤ u) (hz : ‖z‖ ≤ c) :
    Real.exp ‖z * (u : ℂ)‖ ≤ Real.exp (c * u) := by
  apply Real.exp_le_exp.mpr
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu]
  exact mul_le_mul_of_nonneg_right hz hu

theorem hpThetaPhiCosIntegrandFirst_norm_le
    (z : ℂ) (u c : ℝ) (hu : 0 ≤ u) (hz : ‖z‖ ≤ c) :
    ‖hpThetaPhiCosIntegrandFirst z u‖ ≤
      ‖u * Real.exp (c * u) *
        hpRiemannThetaDifferentialKernel u‖ := by
  have hs :
      ‖Complex.sin (z * (u : ℂ))‖ ≤ Real.exp (c * u) :=
    (hpThetaPhi_complex_sin_norm_le (z * (u : ℂ))).trans
      (hpThetaPhi_parameter_exp_bound z u c hu hz)
  calc
    ‖hpThetaPhiCosIntegrandFirst z u‖ =
        |hpRiemannThetaDifferentialKernel u| * u *
          ‖Complex.sin (z * (u : ℂ))‖ := by
      simp only [hpThetaPhiCosIntegrandFirst, norm_mul, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
    _ ≤ |hpRiemannThetaDifferentialKernel u| * u *
            Real.exp (c * u) :=
      mul_le_mul_of_nonneg_left hs
        (mul_nonneg (abs_nonneg _) hu)
    _ = ‖u * Real.exp (c * u) *
          hpRiemannThetaDifferentialKernel u‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hu,
        abs_of_pos (Real.exp_pos (c * u))]
      ring

theorem hpThetaPhiCosIntegrandSecond_norm_le
    (z : ℂ) (u c : ℝ) (hu : 0 ≤ u) (hz : ‖z‖ ≤ c) :
    ‖hpThetaPhiCosIntegrandSecond z u‖ ≤
      ‖u ^ 2 * Real.exp (c * u) *
        hpRiemannThetaDifferentialKernel u‖ := by
  have hc :
      ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp (c * u) :=
    (hpThetaPhi_complex_cos_norm_le (z * (u : ℂ))).trans
      (hpThetaPhi_parameter_exp_bound z u c hu hz)
  calc
    ‖hpThetaPhiCosIntegrandSecond z u‖ =
        |hpRiemannThetaDifferentialKernel u| * u ^ 2 *
          ‖Complex.cos (z * (u : ℂ))‖ := by
      simp only [hpThetaPhiCosIntegrandSecond, norm_mul, norm_neg,
        norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hu]
    _ ≤ |hpRiemannThetaDifferentialKernel u| * u ^ 2 *
            Real.exp (c * u) :=
      mul_le_mul_of_nonneg_left hc
        (mul_nonneg (abs_nonneg _) (sq_nonneg u))
    _ = ‖u ^ 2 * Real.exp (c * u) *
          hpRiemannThetaDifferentialKernel u‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (sq_nonneg u),
        abs_of_pos (Real.exp_pos (c * u))]
      ring

#print axioms hpThetaPhi_complex_exp_norm_le
#print axioms hpThetaPhi_complex_cos_norm_le
#print axioms hpThetaPhi_complex_sin_norm_le
#print axioms hpThetaPhi_parameter_exp_bound
#print axioms hpThetaPhiCosIntegrandFirst_norm_le
#print axioms hpThetaPhiCosIntegrandSecond_norm_le

end HodgeProofHP
