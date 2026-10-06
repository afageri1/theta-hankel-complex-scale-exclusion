import HodgeProofHP.Stage4ThetaHankelSpectralScalingNecessary
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
Iterated complex derivatives and convergence of derivatives
of finite spectral products, including the fourth derivative.

No fourth-coefficient identity or Xi correspondence is assumed.
-/

namespace HodgeProofHP

noncomputable def hpThetaIteratedComplexDeriv :
    ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | 0, f => f
  | n + 1, f => deriv (hpThetaIteratedComplexDeriv n f)

theorem hpThetaIteratedComplexDeriv_differentiable
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (n : ℕ) :
    Differentiable ℂ (hpThetaIteratedComplexDeriv n f) := by
  induction n with
  | zero =>
      exact hf
  | succ n ih =>
      change Differentiable ℂ
        (deriv (hpThetaIteratedComplexDeriv n f))
      exact ih.deriv

theorem hpThetaHankelFiniteSpectralProduct_iteratedDeriv_tendstoLocallyUniformlyOn
    (n : ℕ) :
    TendstoLocallyUniformlyOn
      (fun F : Finset HPThetaHankelSpectralIndex =>
        hpThetaIteratedComplexDeriv n
          (hpThetaHankelFiniteSpectralProduct F))
      (hpThetaIteratedComplexDeriv n hpThetaHankelSpectralProduct)
      Filter.atTop
      (Set.univ : Set ℂ) := by
  induction n with
  | zero =>
      exact
        hpThetaHankelFiniteSpectralProduct_tendstoLocallyUniformlyOn
  | succ n ih =>
      have hF :
          ∀ᶠ F : Finset HPThetaHankelSpectralIndex in Filter.atTop,
            DifferentiableOn ℂ
              (hpThetaIteratedComplexDeriv n
                (hpThetaHankelFiniteSpectralProduct F))
              (Set.univ : Set ℂ) :=
        Filter.Eventually.of_forall (fun F =>
          (hpThetaIteratedComplexDeriv_differentiable
            (hpThetaHankelFiniteSpectralProduct F)
            (hpThetaHankelFiniteSpectralProduct_differentiable F)
            n).differentiableOn)
      change TendstoLocallyUniformlyOn
        (fun F : Finset HPThetaHankelSpectralIndex =>
          deriv (hpThetaIteratedComplexDeriv n
            (hpThetaHankelFiniteSpectralProduct F)))
        (deriv (hpThetaIteratedComplexDeriv n
          hpThetaHankelSpectralProduct))
        Filter.atTop
        (Set.univ : Set ℂ)
      simpa only [Function.comp_def] using
        ih.deriv hF isOpen_univ

theorem hpThetaHankelFiniteSpectralProduct_iteratedDeriv_zero_tendsto
    (n : ℕ) :
    Filter.Tendsto
      (fun F : Finset HPThetaHankelSpectralIndex =>
        hpThetaIteratedComplexDeriv n
          (hpThetaHankelFiniteSpectralProduct F) 0)
      Filter.atTop
      (nhds (hpThetaIteratedComplexDeriv n
        hpThetaHankelSpectralProduct 0)) := by
  exact
    (hpThetaHankelFiniteSpectralProduct_iteratedDeriv_tendstoLocallyUniformlyOn n).tendsto_at
      (Set.mem_univ (0 : ℂ))

theorem hpThetaHankelSpectralProduct_fourthDeriv_differentiable :
    Differentiable ℂ
      (hpThetaIteratedComplexDeriv 4 hpThetaHankelSpectralProduct) := by
  exact hpThetaIteratedComplexDeriv_differentiable
    hpThetaHankelSpectralProduct
    hpThetaHankelSpectralProduct_differentiable
    4

theorem hpThetaHankelFiniteSpectralProduct_fourthDeriv_zero_tendsto :
    Filter.Tendsto
      (fun F : Finset HPThetaHankelSpectralIndex =>
        hpThetaIteratedComplexDeriv 4
          (hpThetaHankelFiniteSpectralProduct F) 0)
      Filter.atTop
      (nhds (hpThetaIteratedComplexDeriv 4
        hpThetaHankelSpectralProduct 0)) := by
  exact hpThetaHankelFiniteSpectralProduct_iteratedDeriv_zero_tendsto 4

#print axioms hpThetaIteratedComplexDeriv_differentiable
#print axioms hpThetaHankelFiniteSpectralProduct_iteratedDeriv_tendstoLocallyUniformlyOn
#print axioms hpThetaHankelFiniteSpectralProduct_iteratedDeriv_zero_tendsto
#print axioms hpThetaHankelSpectralProduct_fourthDeriv_differentiable
#print axioms hpThetaHankelFiniteSpectralProduct_fourthDeriv_zero_tendsto

end HodgeProofHP
