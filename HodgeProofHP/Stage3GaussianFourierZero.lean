import HodgeProofHP.Stage3GaussianExponentialIntegralZero
import Mathlib.Analysis.Fourier.FourierTransform

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpGaussianWeightedL2Function_fourier_eq_zero
    (v : HPSpace)
    (hv : v ∈ hpHermiteL2Span.orthogonal)
    (w : ℝ) :
    FourierTransform.fourier
      (hpGaussianWeightedL2Function v) w = 0 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hphase (x : ℝ) :
      ((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I =
        (((-2 * Real.pi * w : ℝ) : ℂ) * Complex.I) *
          (x : ℂ) := by
    push_cast
    ring
  simp_rw [hphase, smul_eq_mul]
  exact
    hpGaussianWeightedL2Function_exponential_integral_eq_zero
      v hv (((-2 * Real.pi * w : ℝ) : ℂ) * Complex.I)

theorem hpGaussianWeightedL2Function_fourier_eq_zero_function
    (v : HPSpace)
    (hv : v ∈ hpHermiteL2Span.orthogonal) :
    FourierTransform.fourier
      (hpGaussianWeightedL2Function v) = 0 := by
  funext w
  exact hpGaussianWeightedL2Function_fourier_eq_zero v hv w

end HodgeProofHP

#print axioms HodgeProofHP.hpGaussianWeightedL2Function_fourier_eq_zero
#print axioms HodgeProofHP.hpGaussianWeightedL2Function_fourier_eq_zero_function
