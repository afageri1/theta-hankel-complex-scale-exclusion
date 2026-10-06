import HodgeProofHP.Stage4ThetaHankelSpectralProductEntire
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
First derivatives of even entire functions, applied to the theta spectral
product and its finite approximations.
-/

namespace HodgeProofHP

theorem hpTheta_even_differentiable_deriv_odd
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (heven : ∀ z : ℂ, f (-z) = f z) (z : ℂ) :
    deriv f (-z) = -deriv f z := by
  have hneg : HasDerivAt (fun w : ℂ => -w) (-1) z := by
    convert (hasDerivAt_id z).neg using 1 <;> rfl
  have hcomp :
      HasDerivAt (fun w : ℂ => f (-w))
        (-deriv f (-z)) z := by
    simpa only [Function.comp_def, mul_neg_one] using
      ((hf (-z)).hasDerivAt.comp_of_eq z hneg rfl)
  have hfun : (fun w : ℂ => f (-w)) = f := by
    funext w
    exact heven w
  rw [hfun] at hcomp
  have heq := hcomp.unique (hf z).hasDerivAt
  linear_combination -heq

theorem hpTheta_even_differentiable_deriv_zero
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (heven : ∀ z : ℂ, f (-z) = f z) :
    deriv f 0 = 0 := by
  have h := hpTheta_even_differentiable_deriv_odd f hf heven 0
  simp only [neg_zero] at h
  linear_combination (1 / 2 : ℂ) * h

theorem hpThetaHankelSpectralProduct_deriv_odd (z : ℂ) :
    deriv hpThetaHankelSpectralProduct (-z) =
      -deriv hpThetaHankelSpectralProduct z :=
  hpTheta_even_differentiable_deriv_odd
    hpThetaHankelSpectralProduct
    hpThetaHankelSpectralProduct_differentiable
    hpThetaHankelSpectralProduct_even z

theorem hpThetaHankelSpectralProduct_deriv_zero :
    deriv hpThetaHankelSpectralProduct 0 = 0 :=
  hpTheta_even_differentiable_deriv_zero
    hpThetaHankelSpectralProduct
    hpThetaHankelSpectralProduct_differentiable
    hpThetaHankelSpectralProduct_even

theorem hpThetaHankelFiniteSpectralProduct_deriv_zero
    (F : Finset HPThetaHankelSpectralIndex) :
    deriv (hpThetaHankelFiniteSpectralProduct F) 0 = 0 :=
  hpTheta_even_differentiable_deriv_zero
    (hpThetaHankelFiniteSpectralProduct F)
    (hpThetaHankelFiniteSpectralProduct_differentiable F)
    (fun z => hpThetaHankelFiniteSpectralProduct_even F z)

theorem hpThetaHankelSpectralProduct_hasDerivAt_zero :
    HasDerivAt hpThetaHankelSpectralProduct 0 0 := by
  simpa only [hpThetaHankelSpectralProduct_deriv_zero] using
    (hpThetaHankelSpectralProduct_differentiable 0).hasDerivAt

#print axioms hpTheta_even_differentiable_deriv_odd
#print axioms hpThetaHankelSpectralProduct_deriv_odd
#print axioms hpThetaHankelSpectralProduct_deriv_zero
#print axioms hpThetaHankelFiniteSpectralProduct_deriv_zero
#print axioms hpThetaHankelSpectralProduct_hasDerivAt_zero

end HodgeProofHP
