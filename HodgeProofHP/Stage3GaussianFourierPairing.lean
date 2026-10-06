import HodgeProofHP.Stage3GaussianWeightedL2

/-!
Fourier integral pairing for integrable functions on ℝ, and its
vanishing for Gaussian-weighted vectors orthogonal to the Hermite span.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace HodgeProofHP

theorem hpIntegral_fourier_mul_eq
    (f g : ℝ → ℂ)
    (hf : Integrable f volume)
    (hg : Integrable g volume) :
    (∫ x : ℝ, FourierTransform.fourier f x * g x) =
      ∫ x : ℝ, f x * FourierTransform.fourier g x := by
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change inner ℝ y x = inner ℝ x y
    exact (real_inner_comm y x).symm
  have hL :
      Continuous
        (fun p : ℝ × ℝ => (innerₗ ℝ p.1) p.2) := by
    change Continuous (fun p : ℝ × ℝ => inner ℝ p.1 p.2)
    fun_prop
  have h :=
    VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (e := Real.fourierChar)
      (μ := volume) (ν := volume) (L := innerₗ ℝ)
      (ContinuousLinearMap.mul ℂ ℂ)
      Real.continuous_fourierChar hL hf hg
  rw [hflip] at h
  change
    (∫ x : ℝ, FourierTransform.fourier f x * g x) =
      (∫ x : ℝ, f x * FourierTransform.fourier g x) at h
  exact h

theorem hpGaussianWeightedL2Function_fourier_pairing_eq_zero
    (v : HPSpace)
    (hv : v ∈ hpHermiteL2Span.orthogonal)
    (g : ℝ → ℂ)
    (hg : Integrable g volume) :
    (∫ x : ℝ, hpGaussianWeightedL2Function v x *
      FourierTransform.fourier g x) = 0 := by
  rw [← hpIntegral_fourier_mul_eq
    (hpGaussianWeightedL2Function v) g
    (hpGaussianWeightedL2Function_integrable v) hg]
  simp only [
    hpGaussianWeightedL2Function_fourier_eq_zero v hv,
    zero_mul, integral_zero]

theorem hpGaussianWeightedL2Function_schwartz_fourier_pairing_eq_zero
    (v : HPSpace)
    (hv : v ∈ hpHermiteL2Span.orthogonal)
    (g : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, hpGaussianWeightedL2Function v x *
      FourierTransform.fourier (g : ℝ → ℂ) x) = 0 :=
  hpGaussianWeightedL2Function_fourier_pairing_eq_zero
    v hv (g : ℝ → ℂ) g.integrable

end HodgeProofHP

#print axioms HodgeProofHP.hpIntegral_fourier_mul_eq
#print axioms HodgeProofHP.hpGaussianWeightedL2Function_fourier_pairing_eq_zero
#print axioms HodgeProofHP.hpGaussianWeightedL2Function_schwartz_fourier_pairing_eq_zero
