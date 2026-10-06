import HodgeProofHP.Stage4ThetaPhiDerivativeDomination

/-!
Complex parameter derivatives of the differential-theta
cosine integrand, before differentiation under the integral.
-/

noncomputable section

namespace HodgeProofHP

def hpThetaPhiCosIntegrand (z : ℂ) (u : ℝ) : ℂ :=
  (hpRiemannThetaDifferentialKernel u : ℂ) *
    Complex.cos (z * (u : ℂ))

def hpThetaPhiCosIntegrandFirst (z : ℂ) (u : ℝ) : ℂ :=
  -(hpRiemannThetaDifferentialKernel u : ℂ) * (u : ℂ) *
    Complex.sin (z * (u : ℂ))

def hpThetaPhiCosIntegrandSecond (z : ℂ) (u : ℝ) : ℂ :=
  -(hpRiemannThetaDifferentialKernel u : ℂ) * (u : ℂ) ^ 2 *
    Complex.cos (z * (u : ℂ))

theorem hpThetaPhiCosIntegrand_hasDerivAt (z : ℂ) (u : ℝ) :
    HasDerivAt
      (fun w : ℂ => hpThetaPhiCosIntegrand w u)
      (hpThetaPhiCosIntegrandFirst z u) z := by
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
      (hpRiemannThetaDifferentialKernel u : ℂ) *
        Complex.cos (w * (u : ℂ)))
    (-(hpRiemannThetaDifferentialKernel u : ℂ) * (u : ℂ) *
      Complex.sin (z * (u : ℂ))) z
  convert hcos.const_mul
    (hpRiemannThetaDifferentialKernel u : ℂ) using 1 <;> ring

theorem hpThetaPhiCosIntegrandFirst_hasDerivAt
    (z : ℂ) (u : ℝ) :
    HasDerivAt
      (fun w : ℂ => hpThetaPhiCosIntegrandFirst w u)
      (hpThetaPhiCosIntegrandSecond z u) z := by
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
      (-(hpRiemannThetaDifferentialKernel u : ℂ) * (u : ℂ)) *
        Complex.sin (w * (u : ℂ)))
    (-(hpRiemannThetaDifferentialKernel u : ℂ) * (u : ℂ) ^ 2 *
      Complex.cos (z * (u : ℂ))) z
  convert hsin.const_mul
    (-(hpRiemannThetaDifferentialKernel u : ℂ) * (u : ℂ))
    using 1 <;> ring

theorem hpThetaPhiCosIntegrandFirst_zero (u : ℝ) :
    hpThetaPhiCosIntegrandFirst 0 u = 0 := by
  simp [hpThetaPhiCosIntegrandFirst]

theorem hpThetaPhiCosIntegrandSecond_zero (u : ℝ) :
    hpThetaPhiCosIntegrandSecond 0 u =
      -((u : ℂ) ^ 2 *
        (hpRiemannThetaDifferentialKernel u : ℂ)) := by
  simp only [hpThetaPhiCosIntegrandSecond, zero_mul,
    Complex.cos_zero, mul_one]
  ring

#print axioms hpThetaPhiCosIntegrand_hasDerivAt
#print axioms hpThetaPhiCosIntegrandFirst_hasDerivAt
#print axioms hpThetaPhiCosIntegrandFirst_zero
#print axioms hpThetaPhiCosIntegrandSecond_zero

end HodgeProofHP
