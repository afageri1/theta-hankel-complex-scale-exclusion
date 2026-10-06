import HodgeProofHP.Stage4ThetaHankelSpectralProductFirstDerivative
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
Differentiability of first derivatives and locally uniform convergence of
second derivatives of the finite spectral products.
-/

namespace HodgeProofHP

theorem hpThetaHankelFiniteSpectralProduct_deriv_differentiable
    (F : Finset HPThetaHankelSpectralIndex) :
    Differentiable ℂ (deriv (hpThetaHankelFiniteSpectralProduct F)) :=
  (hpThetaHankelFiniteSpectralProduct_differentiable F).deriv

theorem hpThetaHankelSpectralProduct_deriv_differentiable :
    Differentiable ℂ (deriv hpThetaHankelSpectralProduct) :=
  hpThetaHankelSpectralProduct_differentiable.deriv

theorem hpThetaHankelFiniteSpectralProduct_secondDeriv_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn
      (fun F : Finset HPThetaHankelSpectralIndex =>
        deriv (deriv (hpThetaHankelFiniteSpectralProduct F)))
      (deriv (deriv hpThetaHankelSpectralProduct))
      Filter.atTop (Set.univ : Set ℂ) := by
  have hF :
      ∀ᶠ F : Finset HPThetaHankelSpectralIndex in Filter.atTop,
        DifferentiableOn ℂ
          (deriv (hpThetaHankelFiniteSpectralProduct F))
          (Set.univ : Set ℂ) :=
    Filter.Eventually.of_forall (fun F =>
      (hpThetaHankelFiniteSpectralProduct_deriv_differentiable F).differentiableOn)
  simpa only [Function.comp_def] using
    hpThetaHankelFiniteSpectralProduct_deriv_tendstoLocallyUniformlyOn.deriv
      hF isOpen_univ

theorem hpThetaHankelFiniteSpectralProduct_secondDeriv_zero_tendsto :
    Filter.Tendsto
      (fun F : Finset HPThetaHankelSpectralIndex =>
        deriv (deriv (hpThetaHankelFiniteSpectralProduct F)) 0)
      Filter.atTop
      (nhds (deriv (deriv hpThetaHankelSpectralProduct) 0)) := by
  exact
    hpThetaHankelFiniteSpectralProduct_secondDeriv_tendstoLocallyUniformlyOn.tendsto_at
      (Set.mem_univ (0 : ℂ))

#print axioms hpThetaHankelFiniteSpectralProduct_deriv_differentiable
#print axioms hpThetaHankelSpectralProduct_deriv_differentiable
#print axioms hpThetaHankelFiniteSpectralProduct_secondDeriv_tendstoLocallyUniformlyOn
#print axioms hpThetaHankelFiniteSpectralProduct_secondDeriv_zero_tendsto

end HodgeProofHP
