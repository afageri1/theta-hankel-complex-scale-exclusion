import HodgeProofHP.Stage4ThetaPhiThirdMomentIntegrability
import HodgeProofHP.Stage4ThetaPhiSecondIntegralDerivative

/-!
Third and fourth complex parameter derivatives of the theta cosine
integrand, with continuity and exponential domination bounds.
-/

noncomputable section

namespace HodgeProofHP

def hpThetaPhiCosIntegrandThird (z : ℂ) (u : ℝ) : ℂ :=
  (hpRiemannThetaDifferentialKernel u : ℂ) * (u : ℂ) ^ 3 *
    Complex.sin (z * (u : ℂ))

def hpThetaPhiCosIntegrandFourth (z : ℂ) (u : ℝ) : ℂ :=
  (hpRiemannThetaDifferentialKernel u : ℂ) * (u : ℂ) ^ 4 *
    Complex.cos (z * (u : ℂ))

theorem hpThetaPhiCosIntegrandSecond_hasDerivAt
    (z : ℂ) (u : ℝ) :
    HasDerivAt
      (fun w : ℂ => hpThetaPhiCosIntegrandSecond w u)
      (hpThetaPhiCosIntegrandThird z u) z := by
  have harg :
      HasDerivAt (fun w : ℂ => w * (u : ℂ)) (u : ℂ) z := by
    simpa using (hasDerivAt_id z).mul_const (u : ℂ)
  have hcos :
      HasDerivAt
        (fun w : ℂ => Complex.cos (w * (u : ℂ)))
        (-Complex.sin (z * (u : ℂ)) * (u : ℂ)) z := by
    simpa only [Function.comp_def] using
      (Complex.hasDerivAt_cos (z * (u : ℂ))).comp z harg
  change HasDerivAt
    (fun w : ℂ =>
      (-(hpRiemannThetaDifferentialKernel u : ℂ) * (u : ℂ) ^ 2) *
        Complex.cos (w * (u : ℂ)))
    ((hpRiemannThetaDifferentialKernel u : ℂ) * (u : ℂ) ^ 3 *
      Complex.sin (z * (u : ℂ))) z
  convert hcos.const_mul
    (-(hpRiemannThetaDifferentialKernel u : ℂ) * (u : ℂ) ^ 2)
    using 1 <;> ring

theorem hpThetaPhiCosIntegrandThird_hasDerivAt
    (z : ℂ) (u : ℝ) :
    HasDerivAt
      (fun w : ℂ => hpThetaPhiCosIntegrandThird w u)
      (hpThetaPhiCosIntegrandFourth z u) z := by
  have harg :
      HasDerivAt (fun w : ℂ => w * (u : ℂ)) (u : ℂ) z := by
    simpa using (hasDerivAt_id z).mul_const (u : ℂ)
  have hsin :
      HasDerivAt
        (fun w : ℂ => Complex.sin (w * (u : ℂ)))
        (Complex.cos (z * (u : ℂ)) * (u : ℂ)) z := by
    simpa only [Function.comp_def] using
      (Complex.hasDerivAt_sin (z * (u : ℂ))).comp z harg
  change HasDerivAt
    (fun w : ℂ =>
      ((hpRiemannThetaDifferentialKernel u : ℂ) * (u : ℂ) ^ 3) *
        Complex.sin (w * (u : ℂ)))
    ((hpRiemannThetaDifferentialKernel u : ℂ) * (u : ℂ) ^ 4 *
      Complex.cos (z * (u : ℂ))) z
  convert hsin.const_mul
    ((hpRiemannThetaDifferentialKernel u : ℂ) * (u : ℂ) ^ 3)
    using 1 <;> ring

theorem hpThetaPhiCosIntegrandThird_continuous (z : ℂ) :
    Continuous (hpThetaPhiCosIntegrandThird z) := by
  have hphi :
      Continuous
        (fun u : ℝ => (hpRiemannThetaDifferentialKernel u : ℂ)) :=
    Complex.continuous_ofReal.comp
      hpRiemannThetaDifferentialKernel_continuous
  exact (hphi.mul (Complex.continuous_ofReal.pow 3)).mul
    (Complex.continuous_sin.comp
      (continuous_const.mul Complex.continuous_ofReal))

theorem hpThetaPhiCosIntegrandFourth_continuous (z : ℂ) :
    Continuous (hpThetaPhiCosIntegrandFourth z) := by
  have hphi :
      Continuous
        (fun u : ℝ => (hpRiemannThetaDifferentialKernel u : ℂ)) :=
    Complex.continuous_ofReal.comp
      hpRiemannThetaDifferentialKernel_continuous
  exact (hphi.mul (Complex.continuous_ofReal.pow 4)).mul
    (Complex.continuous_cos.comp
      (continuous_const.mul Complex.continuous_ofReal))

theorem hpThetaPhiCosIntegrandThird_norm_le
    (z : ℂ) (u c : ℝ) (hu : 0 ≤ u) (hz : ‖z‖ ≤ c) :
    ‖hpThetaPhiCosIntegrandThird z u‖ ≤
      ‖u ^ 3 * Real.exp (c * u) *
        hpRiemannThetaDifferentialKernel u‖ := by
  have hs :
      ‖Complex.sin (z * (u : ℂ))‖ ≤ Real.exp (c * u) :=
    (hpThetaPhi_complex_sin_norm_le (z * (u : ℂ))).trans
      (hpThetaPhi_parameter_exp_bound z u c hu hz)
  have hu3 : 0 ≤ u ^ 3 := pow_nonneg hu 3
  calc
    ‖hpThetaPhiCosIntegrandThird z u‖ =
        |hpRiemannThetaDifferentialKernel u| * u ^ 3 *
          ‖Complex.sin (z * (u : ℂ))‖ := by
      simp only [hpThetaPhiCosIntegrandThird, norm_mul,
        norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hu]
    _ ≤ |hpRiemannThetaDifferentialKernel u| * u ^ 3 *
          Real.exp (c * u) :=
      mul_le_mul_of_nonneg_left hs
        (mul_nonneg (abs_nonneg _) hu3)
    _ = ‖u ^ 3 * Real.exp (c * u) *
          hpRiemannThetaDifferentialKernel u‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg hu3,
        abs_of_pos (Real.exp_pos (c * u))]
      ring

theorem hpThetaPhiCosIntegrandFourth_norm_le
    (z : ℂ) (u c : ℝ) (hu : 0 ≤ u) (hz : ‖z‖ ≤ c) :
    ‖hpThetaPhiCosIntegrandFourth z u‖ ≤
      ‖u ^ 4 * Real.exp (c * u) *
        hpRiemannThetaDifferentialKernel u‖ := by
  have hc :
      ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp (c * u) :=
    (hpThetaPhi_complex_cos_norm_le (z * (u : ℂ))).trans
      (hpThetaPhi_parameter_exp_bound z u c hu hz)
  have hu4 : 0 ≤ u ^ 4 := pow_nonneg hu 4
  calc
    ‖hpThetaPhiCosIntegrandFourth z u‖ =
        |hpRiemannThetaDifferentialKernel u| * u ^ 4 *
          ‖Complex.cos (z * (u : ℂ))‖ := by
      simp only [hpThetaPhiCosIntegrandFourth, norm_mul,
        norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hu]
    _ ≤ |hpRiemannThetaDifferentialKernel u| * u ^ 4 *
          Real.exp (c * u) :=
      mul_le_mul_of_nonneg_left hc
        (mul_nonneg (abs_nonneg _) hu4)
    _ = ‖u ^ 4 * Real.exp (c * u) *
          hpRiemannThetaDifferentialKernel u‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg hu4,
        abs_of_pos (Real.exp_pos (c * u))]
      ring

theorem hpThetaPhiCosIntegrandThird_zero (u : ℝ) :
    hpThetaPhiCosIntegrandThird 0 u = 0 := by
  simp [hpThetaPhiCosIntegrandThird]

theorem hpThetaPhiCosIntegrandFourth_zero (u : ℝ) :
    hpThetaPhiCosIntegrandFourth 0 u =
      ((u ^ 4 * hpRiemannThetaDifferentialKernel u : ℝ) : ℂ) := by
  simp only [hpThetaPhiCosIntegrandFourth, zero_mul,
    Complex.cos_zero, mul_one,
    Complex.ofReal_mul, Complex.ofReal_pow]
  ring

#print axioms hpThetaPhiCosIntegrandSecond_hasDerivAt
#print axioms hpThetaPhiCosIntegrandThird_hasDerivAt
#print axioms hpThetaPhiCosIntegrandThird_continuous
#print axioms hpThetaPhiCosIntegrandFourth_continuous
#print axioms hpThetaPhiCosIntegrandThird_norm_le
#print axioms hpThetaPhiCosIntegrandFourth_norm_le
#print axioms hpThetaPhiCosIntegrandThird_zero
#print axioms hpThetaPhiCosIntegrandFourth_zero

end HodgeProofHP
