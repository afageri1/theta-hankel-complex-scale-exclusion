import HodgeProofHP.Stage4ThetaHankelSpectralProductFourthDerivative

/-!
Necessary fourth-order conditions for equality of the scaled spectral
product with normalized Xi. The final identity eliminates the scale.
-/

namespace HodgeProofHP

theorem hpTheta_fourthDeriv_comp_scale_zero
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) :
    hpThetaIteratedComplexDeriv 4 (fun z => f (c * z)) 0 =
      c ^ 4 * hpThetaIteratedComplexDeriv 4 f 0 := by
  have hcf : ContDiff ℂ 4 f := hf.contDiff
  have h := iteratedDeriv_comp_const_mul (n := 4) hcf c
  have hzero := congrArg (fun g : ℂ → ℂ => g 0) h
  simpa only [hpThetaIteratedComplexDeriv_eq_iteratedDeriv,
    mul_zero] using hzero

theorem hpThetaHankelScaledSpectralProduct_fourthDeriv_zero
    (c : ℝ) :
    hpThetaIteratedComplexDeriv 4
      (hpThetaHankelScaledSpectralProduct c) 0 =
        12 * (c : ℂ) ^ 4 *
          ((hpThetaFirstTraceEnergy : ℂ) ^ 2 -
            hpThetaHankelSpectralSquareSum) := by
  unfold hpThetaHankelScaledSpectralProduct
  rw [hpTheta_fourthDeriv_comp_scale_zero
    hpThetaHankelSpectralProduct
    hpThetaHankelSpectralProduct_differentiable (c : ℂ)]
  rw [hpThetaHankelSpectralProduct_fourthDeriv_zero]
  ring

theorem hpThetaHankelScaledSpectralProduct_eq_normalizedXi_fourth_necessary
    (c : ℝ)
    (hmatch :
      hpThetaHankelScaledSpectralProduct c = hpThetaNormalizedXi) :
    (c : ℂ) ^ 4 *
        ((hpThetaFirstTraceEnergy : ℂ) ^ 2 -
          hpThetaHankelSpectralSquareSum) =
      hpThetaIteratedComplexDeriv 4 hpThetaNormalizedXi 0 / 12 := by
  have h := hpThetaHankelScaledSpectralProduct_fourthDeriv_zero c
  rw [hmatch] at h
  calc
    (c : ℂ) ^ 4 *
        ((hpThetaFirstTraceEnergy : ℂ) ^ 2 -
          hpThetaHankelSpectralSquareSum) =
      (12 * (c : ℂ) ^ 4 *
        ((hpThetaFirstTraceEnergy : ℂ) ^ 2 -
          hpThetaHankelSpectralSquareSum)) / 12 := by ring
    _ = hpThetaIteratedComplexDeriv 4 hpThetaNormalizedXi 0 / 12 := by
      rw [← h]

private theorem hpTheta_fourthScaling_eliminate
    (c e r q b : ℂ)
    (h2 : c ^ 2 * e = r)
    (h4 : c ^ 4 * (e ^ 2 - q) = b) :
    r ^ 2 * (e ^ 2 - q) = e ^ 2 * b := by
  rw [← h2, ← h4]
  ring

theorem hpThetaHankelScaledSpectralProduct_eq_normalizedXi_invariant_necessary
    (c : ℝ)
    (hmatch :
      hpThetaHankelScaledSpectralProduct c = hpThetaNormalizedXi) :
    ((-(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re) : ℝ) : ℂ) ^ 2 *
        ((hpThetaFirstTraceEnergy : ℂ) ^ 2 -
          hpThetaHankelSpectralSquareSum) =
      (hpThetaFirstTraceEnergy : ℂ) ^ 2 *
        (hpThetaIteratedComplexDeriv 4 hpThetaNormalizedXi 0 / 12) := by
  have h2real :=
    hpThetaHankelScaledSpectralProduct_eq_normalizedXi_necessary c hmatch
  have h2 :
      (c : ℂ) ^ 2 * (hpThetaFirstTraceEnergy : ℂ) =
        ((-(deriv (deriv hpRiemannXiCritical) 0).re /
          (2 * (hpRiemannXiCritical 0).re) : ℝ) : ℂ) := by
    exact_mod_cast h2real
  have h4 :=
    hpThetaHankelScaledSpectralProduct_eq_normalizedXi_fourth_necessary
      c hmatch
  exact hpTheta_fourthScaling_eliminate
    (c : ℂ) (hpThetaFirstTraceEnergy : ℂ)
    ((-(deriv (deriv hpRiemannXiCritical) 0).re /
      (2 * (hpRiemannXiCritical 0).re) : ℝ) : ℂ)
    hpThetaHankelSpectralSquareSum
    (hpThetaIteratedComplexDeriv 4 hpThetaNormalizedXi 0 / 12)
    h2 h4

theorem hpThetaHankelScaledSpectralProduct_ne_normalizedXi_of_fourth_invariant
    (hbad :
      ((-(deriv (deriv hpRiemannXiCritical) 0).re /
          (2 * (hpRiemannXiCritical 0).re) : ℝ) : ℂ) ^ 2 *
          ((hpThetaFirstTraceEnergy : ℂ) ^ 2 -
            hpThetaHankelSpectralSquareSum) ≠
        (hpThetaFirstTraceEnergy : ℂ) ^ 2 *
          (hpThetaIteratedComplexDeriv 4 hpThetaNormalizedXi 0 / 12))
    (c : ℝ) :
    hpThetaHankelScaledSpectralProduct c ≠ hpThetaNormalizedXi := by
  intro hmatch
  exact hbad
    (hpThetaHankelScaledSpectralProduct_eq_normalizedXi_invariant_necessary
      c hmatch)

#print axioms hpTheta_fourthDeriv_comp_scale_zero
#print axioms hpThetaHankelScaledSpectralProduct_fourthDeriv_zero
#print axioms hpThetaHankelScaledSpectralProduct_eq_normalizedXi_fourth_necessary
#print axioms hpThetaHankelScaledSpectralProduct_eq_normalizedXi_invariant_necessary
#print axioms hpThetaHankelScaledSpectralProduct_ne_normalizedXi_of_fourth_invariant

end HodgeProofHP
