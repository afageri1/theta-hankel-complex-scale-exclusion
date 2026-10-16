/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVKernelFarDecreasing

/-!
# Quantitative far-field derivative bound

Keep the first differentiated Gaussian term exactly. Dominate the remaining
terms by a geometric series of ratio 64*exp(-3*pi*exp(2*t)). On t >= 1/50 the
ratio is at most 1/251, so the derivative remainder is at most 1/250 of the
explicit amplitude below. This is not yet a weighted-tail or CNV certificate.
-/
noncomputable section
namespace HodgeProofHP

def hpThetaCNVFarDerivativeRatio (t : ℝ) : ℝ :=
  64 * Real.exp (-3 * (Real.pi * Real.exp (2 * t)))

def hpThetaCNVFarDerivativeAmplitude (t : ℝ) : ℝ :=
  8 * (Real.pi * Real.exp (2 * t)) ^ 3 * hpThetaGaussianProfile Real.pi t

theorem hpThetaCNV_sixth_growth (n : ℕ) :
    ((n : ℝ) + 1) ^ 6 ≤ (64 : ℝ) ^ n := by
  have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
    (hpThetaKernelUpper_nat_growth n) 6
  calc
    ((n : ℝ) + 1) ^ 6 ≤ ((2 : ℝ) ^ n) ^ 6 := h
    _ = ((2 : ℝ) ^ 6) ^ n := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = (64 : ℝ) ^ n := by norm_num

set_option maxHeartbeats 2000000 in
-- The 24-term rational Taylor certificate is checked without external arithmetic.
theorem hpThetaCNV_exp_thirtyNine_fourths_lower :
    (16064 : ℝ) ≤ Real.exp (39 / 4 : ℝ) := by
  exact hpThetaTrace_exp_lower_of_taylor (39 / 4) 16064 24
    (by norm_num)
    (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])

theorem hpThetaCNV_farDerivativeRatio_bounds (t : ℝ) (ht : (1 / 50 : ℝ) ≤ t) :
    0 ≤ hpThetaCNVFarDerivativeRatio t ∧
      hpThetaCNVFarDerivativeRatio t ≤ (1 / 251 : ℝ) := by
  have hq : (13 / 4 : ℝ) ≤ Real.pi * Real.exp (2 * t) := by
    simpa only [hpThetaGaussianParameter, Nat.cast_zero, zero_add, one_pow, mul_one] using
      hpThetaCNV_far_parameter_ge_thirteen_fourths 0 t ht
  have hprod := mul_le_mul_of_nonneg_right hpThetaCNV_exp_thirtyNine_fourths_lower
    (Real.exp_nonneg (-(39 / 4 : ℝ)))
  have hid : Real.exp (39 / 4 : ℝ) * Real.exp (-(39 / 4 : ℝ)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hid] at hprod
  have hneg : Real.exp (-(39 / 4 : ℝ)) ≤ (1 / 16064 : ℝ) := by linarith
  have he : Real.exp (-3 * (Real.pi * Real.exp (2 * t))) ≤ (1 / 16064 : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans hneg
  unfold hpThetaCNVFarDerivativeRatio
  constructor
  · positivity
  · linarith

theorem hpThetaCNV_farDerivativeRatio_quotient_le (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) :
    hpThetaCNVFarDerivativeRatio t / (1 - hpThetaCNVFarDerivativeRatio t) ≤
      (1 / 250 : ℝ) := by
  have h := hpThetaCNV_farDerivativeRatio_bounds t ht
  have hden : 0 < 1 - hpThetaCNVFarDerivativeRatio t := by linarith [h.2]
  apply (div_le_iff₀ hden).mpr
  linarith [h.2]

theorem hpThetaCNV_negDerivativeTerm_le_geometric (n : ℕ) (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) :
    -hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) t ≤
      hpThetaCNVFarDerivativeAmplitude t * hpThetaCNVFarDerivativeRatio t ^ n := by
  let m : ℝ := (n : ℝ) + 1
  let b : ℝ := Real.pi * Real.exp (2 * t)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hbm : (13 / 4 : ℝ) ≤ b * m ^ 2 := by
    have h := hpThetaCNV_far_parameter_ge_thirteen_fourths n t ht
    dsimp [b, m, hpThetaGaussianParameter] at h ⊢
    nlinarith
  have hrest := mul_nonneg (show 0 ≤ b * m ^ 2 by positivity)
    (show 0 ≤ 2 * (b * m ^ 2) - 1 by linarith)
  have hcoeff : 8 * b ^ 3 * m ^ 6 - 30 * b ^ 2 * m ^ 4 + 15 * b * m ^ 2 ≤
      8 * b ^ 3 * m ^ 6 := by nlinarith
  have hgap : 3 * (n : ℝ) ≤ m ^ 2 - 1 := hpThetaKernelUpper_square_growth n
  have hscaled := mul_le_mul_of_nonneg_left hgap hb
  have hexp : Real.exp (-b * (m ^ 2 - 1)) ≤ Real.exp (-3 * b * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hprofile : hpThetaGaussianProfile (hpThetaGaussianParameter n) t =
      hpThetaGaussianProfile Real.pi t * Real.exp (-b * (m ^ 2 - 1)) := by
    unfold hpThetaGaussianProfile hpThetaGaussianParameter
    dsimp [b, m]
    conv_rhs => rw [mul_assoc, ← Real.exp_add]
    congr 2 <;> ring
  have hterm : -hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) t =
      (8 * b ^ 3 * m ^ 6 - 30 * b ^ 2 * m ^ 4 + 15 * b * m ^ 2) *
        (hpThetaGaussianProfile Real.pi t * Real.exp (-b * (m ^ 2 - 1))) := by
    unfold hpThetaGaussianKernelDerivativeTerm
    rw [hprofile]
    dsimp [hpThetaGaussianParameter, b, m]
    ring
  have hgrowth : m ^ 6 ≤ (64 : ℝ) ^ n := hpThetaCNV_sixth_growth n
  have hratio : (64 : ℝ) ^ n * Real.exp (-3 * b * (n : ℝ)) =
      hpThetaCNVFarDerivativeRatio t ^ n := by
    unfold hpThetaCNVFarDerivativeRatio
    rw [mul_pow, hpThetaKernelUpper_exp_pow]
  have hA : 0 ≤ hpThetaCNVFarDerivativeAmplitude t := by
    unfold hpThetaCNVFarDerivativeAmplitude hpThetaGaussianProfile
    positivity
  calc
    -hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) t =
        (8 * b ^ 3 * m ^ 6 - 30 * b ^ 2 * m ^ 4 + 15 * b * m ^ 2) *
          (hpThetaGaussianProfile Real.pi t * Real.exp (-b * (m ^ 2 - 1))) := hterm
    _ ≤ (8 * b ^ 3 * m ^ 6) *
        (hpThetaGaussianProfile Real.pi t * Real.exp (-b * (m ^ 2 - 1))) := by
      exact mul_le_mul_of_nonneg_right hcoeff (by
        unfold hpThetaGaussianProfile
        positivity)
    _ = hpThetaCNVFarDerivativeAmplitude t * (m ^ 6 * Real.exp (-b * (m ^ 2 - 1))) := by
      dsimp [hpThetaCNVFarDerivativeAmplitude, b]
      ring
    _ ≤ hpThetaCNVFarDerivativeAmplitude t *
        ((64 : ℝ) ^ n * Real.exp (-3 * b * (n : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hgrowth hexp (Real.exp_nonneg _) (by positivity)) hA
    _ = _ := by rw [hratio]

theorem hpThetaCNV_derivative_remainder_le (t : ℝ) (ht : (1 / 50 : ℝ) ≤ t) :
    hpThetaGaussianKernelDerivativeTerm Real.pi t - deriv hpRiemannThetaDifferentialKernel t ≤
      hpThetaCNVFarDerivativeAmplitude t / 250 := by
  let A := hpThetaCNVFarDerivativeAmplitude t
  let q := hpThetaCNVFarDerivativeRatio t
  have hq := hpThetaCNV_farDerivativeRatio_bounds t ht
  have hq0 : 0 ≤ q := hq.1
  have hq1 : q < 1 := by dsimp [q]; linarith [hq.2]
  have hA : 0 ≤ A := by
    dsimp [A, hpThetaCNVFarDerivativeAmplitude, hpThetaGaussianProfile]
    positivity
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
  have hquot := mul_le_mul_of_nonneg_left (hpThetaCNV_farDerivativeRatio_quotient_le t ht) hA
  have hfinal : (A * q) * (1 - q)⁻¹ ≤ A / 250 := by
    simpa only [q, div_eq_mul_inv, mul_assoc] using hquot
  exact hsum.trans hfinal

theorem hpThetaPhi_abs_deriv_le_first_add_remainder_on_far (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) :
    |deriv hpRiemannThetaDifferentialKernel t| ≤
      -hpThetaGaussianKernelDerivativeTerm Real.pi t + hpThetaCNVFarDerivativeAmplitude t / 250 := by
  rw [abs_of_neg (hpThetaPhi_deriv_neg_on_far t ht)]
  have h := hpThetaCNV_derivative_remainder_le t ht
  linarith

#print axioms hpThetaCNV_sixth_growth
#print axioms hpThetaCNV_exp_thirtyNine_fourths_lower
#print axioms hpThetaCNV_farDerivativeRatio_bounds
#print axioms hpThetaCNV_farDerivativeRatio_quotient_le
#print axioms hpThetaCNV_negDerivativeTerm_le_geometric
#print axioms hpThetaCNV_derivative_remainder_le
#print axioms hpThetaPhi_abs_deriv_le_first_add_remainder_on_far
end HodgeProofHP
