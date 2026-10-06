import HodgeProofHP.Stage3ClosureDomainSpec
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
The Gaussian ground-state function and its first integrability fact.
This file makes no eigenvector or spectral claim.
-/

namespace HodgeProofHP

noncomputable def hpGaussianGroundFunction (x : ℝ) : ℂ :=
  Complex.exp (-(1 / 2 : ℂ) * (x : ℂ) ^ 2)

private theorem hpGaussianGroundFunction_integrable :
    MeasureTheory.Integrable hpGaussianGroundFunction MeasureTheory.volume := by
  exact integrable_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)

theorem hpGaussianGroundFunction_memLp :
    MeasureTheory.MemLp hpGaussianGroundFunction 2 MeasureTheory.volume := by
  have hmeas : MeasureTheory.AEStronglyMeasurable
      hpGaussianGroundFunction MeasureTheory.volume :=
    (show Continuous hpGaussianGroundFunction by
      unfold hpGaussianGroundFunction
      fun_prop).aestronglyMeasurable
  apply (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).2
  have hsq (x : ℝ) :
      ‖hpGaussianGroundFunction x‖ ^ 2 = Real.exp (-(1 : ℝ) * x ^ 2) := by
    rw [hpGaussianGroundFunction, norm_cexp_neg_mul_sq]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num <;> ring
  simpa only [hsq] using
    (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num))

#print axioms hpGaussianGroundFunction_memLp

#check Polynomial.deriv_gaussian_eq_hermite_mul_gaussian
#check MeasureTheory.MemLp
#check SchwartzMap.toLp

end HodgeProofHP
