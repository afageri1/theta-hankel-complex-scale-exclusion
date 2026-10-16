/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVWeightedTailBarrier

/-!
# Retain exponential decay in the far derivative remainder

The earlier A(t)/250 estimate is valid but loses the decay needed in a
uniform far-field comparison. Retain the geometric quotient, and derive an
explicit remainder bounded by (128512/125)*pi^3*exp(13*t/2-4*pi*exp(2*t)).
This is a sharper estimate, not a global CNV positivity theorem.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaCNV_derivative_remainder_le_geometric (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) :
    hpThetaGaussianKernelDerivativeTerm Real.pi t - deriv hpRiemannThetaDifferentialKernel t ≤
      hpThetaCNVFarDerivativeAmplitude t *
        (hpThetaCNVFarDerivativeRatio t / (1 - hpThetaCNVFarDerivativeRatio t)) := by
  let A := hpThetaCNVFarDerivativeAmplitude t
  let q := hpThetaCNVFarDerivativeRatio t
  have hq := hpThetaCNV_farDerivativeRatio_bounds t ht
  have hq0 : 0 ≤ q := hq.1
  have hq1 : q < 1 := by dsimp [q]; linarith [hq.2]
  have hactual : HasSum
      (fun n : ℕ => hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) t)
      (deriv hpRiemannThetaDifferentialKernel t) := by
    rw [hpThetaPhi_deriv_eq_kernelSeries]
    exact (hpThetaGaussianKernelDerivativeTerm_summable t).hasSum
  have htail : HasSum
      (fun n : ℕ => hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter (n + 1)) t)
      (deriv hpRiemannThetaDifferentialKernel t - hpThetaGaussianKernelDerivativeTerm Real.pi t) := by
    have h := (hasSum_nat_add_iff' 1).mpr hactual
    simpa [hpThetaGaussianParameter] using h
  have hnegative : HasSum
      (fun n : ℕ => -hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter (n + 1)) t)
      (hpThetaGaussianKernelDerivativeTerm Real.pi t - deriv hpRiemannThetaDifferentialKernel t) := by
    simpa only [neg_sub] using htail.neg
  have hgeom : HasSum (fun n : ℕ => (A * q) * q ^ n) ((A * q) * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left (A * q)
  have hpoint : ∀ n : ℕ,
      -hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter (n + 1)) t ≤
        (A * q) * q ^ n := by
    intro n
    have h := hpThetaCNV_negDerivativeTerm_le_geometric (n + 1) t ht
    simpa only [A, q, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h
  have hsum := hasSum_le hpoint hnegative hgeom
  simpa only [A, q, div_eq_mul_inv, mul_assoc] using hsum

theorem hpThetaCNV_farDerivativeRatio_quotient_le_mul_ratio (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) :
    hpThetaCNVFarDerivativeRatio t / (1 - hpThetaCNVFarDerivativeRatio t) ≤
      (251 / 250 : ℝ) * hpThetaCNVFarDerivativeRatio t := by
  have hq := hpThetaCNV_farDerivativeRatio_bounds t ht
  have hden : 0 < 1 - hpThetaCNVFarDerivativeRatio t := by linarith [hq.2]
  have hprod := mul_nonneg hq.1 (sub_nonneg.mpr hq.2)
  apply (div_le_iff₀ hden).mpr
  nlinarith

theorem hpThetaCNV_farDerivative_geometric_amplitude_eq (t : ℝ) :
    hpThetaCNVFarDerivativeAmplitude t *
        ((251 / 250 : ℝ) * hpThetaCNVFarDerivativeRatio t) =
      (128512 / 125 : ℝ) * Real.pi ^ 3 *
        Real.exp ((13 / 2 : ℝ) * t - 4 * Real.pi * Real.exp (2 * t)) := by
  calc
    _ = (128512 / 125 : ℝ) * Real.pi ^ 3 *
        (Real.exp ((2 * t) * (3 : ℕ)) *
          Real.exp (t / 2 - Real.pi * Real.exp (2 * t)) *
          Real.exp (-3 * (Real.pi * Real.exp (2 * t)))) := by
      unfold hpThetaCNVFarDerivativeAmplitude hpThetaCNVFarDerivativeRatio
        hpThetaGaussianProfile
      rw [mul_pow, hpThetaKernelUpper_exp_pow]
      ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2 <;> ring

theorem hpThetaCNV_derivative_remainder_le_explicit_exponential (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) :
    hpThetaGaussianKernelDerivativeTerm Real.pi t - deriv hpRiemannThetaDifferentialKernel t ≤
      (128512 / 125 : ℝ) * Real.pi ^ 3 *
        Real.exp ((13 / 2 : ℝ) * t - 4 * Real.pi * Real.exp (2 * t)) := by
  have hA : 0 ≤ hpThetaCNVFarDerivativeAmplitude t := by
    unfold hpThetaCNVFarDerivativeAmplitude hpThetaGaussianProfile
    positivity
  calc
    _ ≤ hpThetaCNVFarDerivativeAmplitude t *
        (hpThetaCNVFarDerivativeRatio t / (1 - hpThetaCNVFarDerivativeRatio t)) :=
      hpThetaCNV_derivative_remainder_le_geometric t ht
    _ ≤ hpThetaCNVFarDerivativeAmplitude t *
        ((251 / 250 : ℝ) * hpThetaCNVFarDerivativeRatio t) :=
      mul_le_mul_of_nonneg_left (hpThetaCNV_farDerivativeRatio_quotient_le_mul_ratio t ht) hA
    _ = _ := hpThetaCNV_farDerivative_geometric_amplitude_eq t

theorem hpThetaPhi_abs_deriv_le_first_add_exponential_on_far (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) :
    |deriv hpRiemannThetaDifferentialKernel t| ≤
      -hpThetaGaussianKernelDerivativeTerm Real.pi t +
        (128512 / 125 : ℝ) * Real.pi ^ 3 *
          Real.exp ((13 / 2 : ℝ) * t - 4 * Real.pi * Real.exp (2 * t)) := by
  rw [abs_of_neg (hpThetaPhi_deriv_neg_on_far t ht)]
  have h := hpThetaCNV_derivative_remainder_le_explicit_exponential t ht
  linarith

#print axioms hpThetaCNV_derivative_remainder_le_geometric
#print axioms hpThetaCNV_farDerivativeRatio_quotient_le_mul_ratio
#print axioms hpThetaCNV_farDerivative_geometric_amplitude_eq
#print axioms hpThetaCNV_derivative_remainder_le_explicit_exponential
#print axioms hpThetaPhi_abs_deriv_le_first_add_exponential_on_far
end HodgeProofHP
