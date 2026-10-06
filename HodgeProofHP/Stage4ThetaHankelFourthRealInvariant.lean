import HodgeProofHP.Stage4ThetaHankelFourthScalingNecessary
import Mathlib.Analysis.Complex.Basic

/-!
Real spectral square sum and a real necessary condition
for equality of scaled spectral products with normalized Xi.
-/

namespace HodgeProofHP

noncomputable def hpThetaHankelSpectralSquareEnergy : ℝ :=
  hpThetaHankelSpectralSquareSum.re

noncomputable def hpThetaNormalizedXiFourthTraceCoefficient : ℝ :=
  (hpThetaIteratedComplexDeriv 4 hpThetaNormalizedXi 0 / 12).re

private theorem hpThetaHankelSpectralValue_sq_re
    (i : HPThetaHankelSpectralIndex) :
    (i.1 ^ 2).re = i.1.re ^ 2 := by
  rw [hpThetaHankelSpectralValue_eq_cast_re i]
  norm_num [pow_two, Complex.mul_re, Complex.mul_im]

private theorem hpThetaHankelSpectralValue_sq_im
    (i : HPThetaHankelSpectralIndex) :
    (i.1 ^ 2).im = 0 := by
  rw [hpThetaHankelSpectralValue_eq_cast_re i]
  norm_num [pow_two, Complex.mul_re, Complex.mul_im]

theorem hpThetaHankelSpectralSquares_real_hasSum :
    HasSum (fun i : HPThetaHankelSpectralIndex => i.1.re ^ 2)
      hpThetaHankelSpectralSquareEnergy := by
  have h :=
    hpThetaHankelSpectralValues_sq_hasSum.map
      Complex.reCLM Complex.reCLM.continuous
  simpa only [Function.comp_def, Complex.reCLM_apply,
    hpThetaHankelSpectralValue_sq_re,
    hpThetaHankelSpectralSquareEnergy] using h

theorem hpThetaHankelSpectralSquares_real_summable :
    Summable (fun i : HPThetaHankelSpectralIndex => i.1.re ^ 2) :=
  hpThetaHankelSpectralSquares_real_hasSum.summable

theorem hpThetaHankelSpectralSquareSum_im_eq_zero :
    hpThetaHankelSpectralSquareSum.im = 0 := by
  have h :=
    hpThetaHankelSpectralValues_sq_hasSum.map
      Complex.imCLM Complex.imCLM.continuous
  have hz :
      HasSum (fun _ : HPThetaHankelSpectralIndex => (0 : ℝ))
        hpThetaHankelSpectralSquareSum.im := by
    simpa only [Function.comp_def, Complex.imCLM_apply,
      hpThetaHankelSpectralValue_sq_im] using h
  simpa using hz.tsum_eq.symm

theorem hpThetaHankelSpectralSquareSum_eq_cast_energy :
    hpThetaHankelSpectralSquareSum =
      (hpThetaHankelSpectralSquareEnergy : ℂ) := by
  apply Complex.ext
  · simp [hpThetaHankelSpectralSquareEnergy]
  · simp [hpThetaHankelSpectralSquareSum_im_eq_zero]

theorem hpThetaHankelSpectralSquareEnergy_nonneg :
    0 ≤ hpThetaHankelSpectralSquareEnergy := by
  rw [← hpThetaHankelSpectralSquares_real_hasSum.tsum_eq]
  exact tsum_nonneg (fun i => sq_nonneg i.1.re)

theorem hpThetaHankelScaledSpectralProduct_eq_normalizedXi_real_invariant
    (c : ℝ)
    (hmatch :
      hpThetaHankelScaledSpectralProduct c = hpThetaNormalizedXi) :
    (-(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re)) ^ 2 *
        (hpThetaFirstTraceEnergy ^ 2 -
          hpThetaHankelSpectralSquareEnergy) =
      hpThetaFirstTraceEnergy ^ 2 *
        hpThetaNormalizedXiFourthTraceCoefficient := by
  let r : ℝ :=
    -(deriv (deriv hpRiemannXiCritical) 0).re /
      (2 * (hpRiemannXiCritical 0).re)
  have h :=
    hpThetaHankelScaledSpectralProduct_eq_normalizedXi_invariant_necessary
      c hmatch
  change
    (r : ℂ) ^ 2 *
        ((hpThetaFirstTraceEnergy : ℂ) ^ 2 -
          hpThetaHankelSpectralSquareSum) =
      (hpThetaFirstTraceEnergy : ℂ) ^ 2 *
        (hpThetaIteratedComplexDeriv 4 hpThetaNormalizedXi 0 / 12) at h
  rw [hpThetaHankelSpectralSquareSum_eq_cast_energy] at h
  have hre := congrArg Complex.re h
  change
    r ^ 2 * (hpThetaFirstTraceEnergy ^ 2 -
      hpThetaHankelSpectralSquareEnergy) =
        hpThetaFirstTraceEnergy ^ 2 *
          hpThetaNormalizedXiFourthTraceCoefficient
  simpa only [hpThetaNormalizedXiFourthTraceCoefficient,
    pow_two, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.sub_im,
    mul_zero, zero_mul, sub_zero, add_zero, zero_add] using hre

theorem hpThetaHankelScaledSpectralProduct_ne_normalizedXi_of_real_invariant
    (hbad :
      (-(deriv (deriv hpRiemannXiCritical) 0).re /
          (2 * (hpRiemannXiCritical 0).re)) ^ 2 *
          (hpThetaFirstTraceEnergy ^ 2 -
            hpThetaHankelSpectralSquareEnergy) ≠
        hpThetaFirstTraceEnergy ^ 2 *
          hpThetaNormalizedXiFourthTraceCoefficient)
    (c : ℝ) :
    hpThetaHankelScaledSpectralProduct c ≠ hpThetaNormalizedXi := by
  intro hmatch
  exact hbad
    (hpThetaHankelScaledSpectralProduct_eq_normalizedXi_real_invariant
      c hmatch)

#print axioms hpThetaHankelSpectralSquares_real_hasSum
#print axioms hpThetaHankelSpectralSquares_real_summable
#print axioms hpThetaHankelSpectralSquareSum_im_eq_zero
#print axioms hpThetaHankelSpectralSquareSum_eq_cast_energy
#print axioms hpThetaHankelSpectralSquareEnergy_nonneg
#print axioms hpThetaHankelScaledSpectralProduct_eq_normalizedXi_real_invariant
#print axioms hpThetaHankelScaledSpectralProduct_ne_normalizedXi_of_real_invariant

end HodgeProofHP
