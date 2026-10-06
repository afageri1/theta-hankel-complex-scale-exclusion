import HodgeProofHP.Stage4ThetaHankelSpectralProductBasics
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
Differentiability of finite spectral products and their uniform convergence
on closed balls. This module does not assert a correspondence with Xi.
-/

namespace HodgeProofHP

theorem hpThetaHankelSpectralProductFactor_differentiable
    (i : HPThetaHankelSpectralIndex) :
    Differentiable ℂ (hpThetaHankelSpectralProductFactor i) := by
  unfold hpThetaHankelSpectralProductFactor
  fun_prop

theorem hpThetaHankelFiniteSpectralProduct_differentiable
    (F : Finset HPThetaHankelSpectralIndex) :
    Differentiable ℂ (hpThetaHankelFiniteSpectralProduct F) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      change Differentiable ℂ
        (fun z : ℂ => ∏ i ∈ (∅ : Finset HPThetaHankelSpectralIndex),
          hpThetaHankelSpectralProductFactor i z)
      simpa only [Finset.prod_empty]
        using (differentiable_const (1 : ℂ))
  | @insert i F hi ih =>
      have h :=
        (hpThetaHankelSpectralProductFactor_differentiable i).mul ih
      change Differentiable ℂ
        (fun z : ℂ => ∏ j ∈ insert i F,
          hpThetaHankelSpectralProductFactor j z)
      simp only [Finset.prod_insert hi]
      change Differentiable ℂ
        (hpThetaHankelSpectralProductFactor i *
          hpThetaHankelFiniteSpectralProduct F)
      exact h

theorem hpThetaHankelFiniteSpectralProduct_continuous
    (F : Finset HPThetaHankelSpectralIndex) :
    Continuous (hpThetaHankelFiniteSpectralProduct F) :=
  (hpThetaHankelFiniteSpectralProduct_differentiable F).continuous

theorem hpThetaHankelFiniteSpectralProduct_tendstoUniformlyOn_closedBall
    (r : ℝ) (hr : 0 ≤ r) :
    TendstoUniformlyOn
      (fun F : Finset HPThetaHankelSpectralIndex =>
        hpThetaHankelFiniteSpectralProduct F)
      hpThetaHankelSpectralProduct
      Filter.atTop
      (Metric.closedBall (0 : ℂ) r) := by
  have h :=
    hpThetaHankelSpectralProduct_hasProdUniformlyOn_closedBall r hr
  change TendstoUniformlyOn
    (fun F : Finset HPThetaHankelSpectralIndex =>
      fun z : ℂ => ∏ i ∈ F,
        hpThetaHankelSpectralProductFactor i z)
    hpThetaHankelSpectralProduct Filter.atTop
    (Metric.closedBall (0 : ℂ) r)
  exact h.tendstoUniformlyOn

#print axioms hpThetaHankelSpectralProductFactor_differentiable
#print axioms hpThetaHankelFiniteSpectralProduct_differentiable
#print axioms hpThetaHankelFiniteSpectralProduct_continuous
#print axioms hpThetaHankelFiniteSpectralProduct_tendstoUniformlyOn_closedBall

end HodgeProofHP
