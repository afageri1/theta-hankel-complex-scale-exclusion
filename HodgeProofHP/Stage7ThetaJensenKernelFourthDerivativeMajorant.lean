/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenKernelFourthDerivativeCriterion

/-!
# Summable fourth derivative majorant for the actual theta kernel

A local sextic factor is absorbed into a Gaussian with positive rate.
This discharges the fourth derivative series criterion at every real point.
No fourth derivative numerical certificate or density curvature sign is asserted.
-/
noncomputable section
namespace HodgeProofHP

def hpThetaGaussianKernelFourthDerivativeMajorant (l r : ℝ) (n : ℕ) : ℝ :=
  200000 * ((1 / 2 : ℝ) + 2 * hpThetaGaussianParameter n * Real.exp (2 * r)) ^ 6 *
    (2 * Real.exp (r / 2 - hpThetaGaussianParameter n * Real.exp (2 * l)))

theorem hpThetaGaussianKernelFourthDerivativeMajorant_nonneg (l r : ℝ) (n : ℕ) :
    0 ≤ hpThetaGaussianKernelFourthDerivativeMajorant l r n := by
  have ha := hpThetaGaussianParameter_nonneg n
  unfold hpThetaGaussianKernelFourthDerivativeMajorant
  positivity

theorem hpThetaGaussianKernelFourthDerivativeFactor_norm_le
    (a r u : ℝ) (ha : 0 ≤ a) (hur : u ≤ r) :
    ‖64 * a ^ 6 * Real.exp (2 * u) ^ 6 -
      1056 * a ^ 5 * Real.exp (2 * u) ^ 5 +
      5176 * a ^ 4 * Real.exp (2 * u) ^ 4 -
      8512 * a ^ 3 * Real.exp (2 * u) ^ 3 +
      (15465 / 4 : ℝ) * a ^ 2 * Real.exp (2 * u) ^ 2 -
      (1875 / 8 : ℝ) * a * Real.exp (2 * u)‖ ≤
      200000 * ((1 / 2 : ℝ) + 2 * a * Real.exp (2 * r)) ^ 6 := by
  let x := a * Real.exp (2 * u)
  let y := a * Real.exp (2 * r)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hxy : x ≤ y := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith)) ha
  have hxy2 : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy 2
  have hxy3 : x ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hx hxy 3
  have hxy4 : x ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ hx hxy 4
  have hxy5 : x ^ 5 ≤ y ^ 5 := pow_le_pow_left₀ hx hxy 5
  have hxy6 : x ^ 6 ≤ y ^ 6 := pow_le_pow_left₀ hx hxy 6
  have hn : ‖64 * x ^ 6 - 1056 * x ^ 5 + 5176 * x ^ 4 -
      8512 * x ^ 3 + (15465 / 4 : ℝ) * x ^ 2 - (1875 / 8 : ℝ) * x‖ ≤
      64 * y ^ 6 + 1056 * y ^ 5 + 5176 * y ^ 4 +
        8512 * y ^ 3 + (15465 / 4 : ℝ) * y ^ 2 + (1875 / 8 : ℝ) * y := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> nlinarith [pow_nonneg hx 3, pow_nonneg hy 3,
      pow_nonneg hx 4, pow_nonneg hy 4, pow_nonneg hx 5, pow_nonneg hy 5,
      pow_nonneg hx 6, pow_nonneg hy 6, sq_nonneg x]
  have hp : 64 * y ^ 6 + 1056 * y ^ 5 + 5176 * y ^ 4 +
        8512 * y ^ 3 + (15465 / 4 : ℝ) * y ^ 2 + (1875 / 8 : ℝ) * y ≤
      200000 * ((1 / 2 : ℝ) + 2 * y) ^ 6 := by
    nlinarith [pow_nonneg hy 3, pow_nonneg hy 4, pow_nonneg hy 5,
      pow_nonneg hy 6, sq_nonneg y]
  have heq : 64 * a ^ 6 * Real.exp (2 * u) ^ 6 -
      1056 * a ^ 5 * Real.exp (2 * u) ^ 5 +
      5176 * a ^ 4 * Real.exp (2 * u) ^ 4 -
      8512 * a ^ 3 * Real.exp (2 * u) ^ 3 +
      (15465 / 4 : ℝ) * a ^ 2 * Real.exp (2 * u) ^ 2 -
      (1875 / 8 : ℝ) * a * Real.exp (2 * u) =
      64 * x ^ 6 - 1056 * x ^ 5 + 5176 * x ^ 4 -
      8512 * x ^ 3 + (15465 / 4 : ℝ) * x ^ 2 - (1875 / 8 : ℝ) * x := by
    dsimp [x]
    ring
  rw [heq]
  simpa only [y, mul_assoc] using hn.trans hp

theorem hpThetaGaussianKernelFourthDerivativeTerm_bound_on_Ioo (l r : ℝ) :
    ∀ n : ℕ, ∀ u ∈ Set.Ioo l r,
      ‖hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter n) u‖ ≤
        hpThetaGaussianKernelFourthDerivativeMajorant l r n := by
  intro n u hu
  have ha := hpThetaGaussianParameter_nonneg n
  have hf := hpThetaGaussianKernelFourthDerivativeFactor_norm_le
    (hpThetaGaussianParameter n) r u ha hu.2.le
  have hg := hpThetaGaussianProfile_norm_le_on_interval
    (hpThetaGaussianParameter n) l r u ha hu.1.le hu.2.le
  unfold hpThetaGaussianKernelFourthDerivativeTerm
    hpThetaGaussianKernelFourthDerivativeMajorant
  rw [norm_mul]
  exact mul_le_mul hf hg (norm_nonneg _) (by positivity)

theorem hpTheta_sextic_factor_gaussian_bound
    (a x b r : ℝ) (ha : 0 ≤ a) (hx : 0 < x) (hb : 0 ≤ b) :
    ((1 / 2 : ℝ) + 2 * a * b) ^ 6 * (2 * Real.exp (r / 2 - a * x)) ≤
      (3 * (((1 / 2 : ℝ) + 4 * b / x) * Real.exp (r / 2)) *
        ((1 / 2 : ℝ) + 4 * b / (x / 2)) *
        ((1 / 2 : ℝ) + 4 * b / (x / 4)) *
        ((1 / 2 : ℝ) + 4 * b / (x / 8)) *
        ((1 / 2 : ℝ) + 4 * b / (x / 16)) *
        ((1 / 2 : ℝ) + 4 * b / (x / 32))) *
          (2 * Real.exp (-a * (x / 64))) := by
  let q : ℝ := (1 / 2 : ℝ) + 2 * a * b
  let A : ℝ := 3 * (((1 / 2 : ℝ) + 4 * b / x) * Real.exp (r / 2)) *
    ((1 / 2 : ℝ) + 4 * b / (x / 2)) *
    ((1 / 2 : ℝ) + 4 * b / (x / 4)) *
    ((1 / 2 : ℝ) + 4 * b / (x / 8)) *
    ((1 / 2 : ℝ) + 4 * b / (x / 16))
  let B : ℝ := (1 / 2 : ℝ) + 4 * b / (x / 32)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h1 : q ^ 5 * (2 * Real.exp (r / 2 - a * x)) ≤
      A * (2 * Real.exp (-a * (x / 32))) :=
    hpTheta_quintic_factor_gaussian_bound a x b r ha hx hb
  have hsixtyfourth : (x / 32) / 2 = x / 64 := by ring
  have h2 : q * (2 * Real.exp (-a * (x / 32))) ≤
      B * (2 * Real.exp (-a * (x / 64))) := by
    simpa only [q, B, zero_div, zero_sub, Real.exp_zero, mul_one,
      hsixtyfourth, neg_mul] using
      hpTheta_linear_factor_gaussian_bound a (x / 32) b 0 ha (by positivity) hb
  change q ^ 6 * (2 * Real.exp (r / 2 - a * x)) ≤
    (A * B) * (2 * Real.exp (-a * (x / 64)))
  calc
    _ = q * (q ^ 5 * (2 * Real.exp (r / 2 - a * x))) := by ring
    _ ≤ q * (A * (2 * Real.exp (-a * (x / 32)))) :=
      mul_le_mul_of_nonneg_left h1 hq
    _ = A * (q * (2 * Real.exp (-a * (x / 32)))) := by ring
    _ ≤ A * (B * (2 * Real.exp (-a * (x / 64)))) :=
      mul_le_mul_of_nonneg_left h2 hA
    _ = _ := by ring

def hpThetaGaussianKernelFourthDerivativeComparisonConstant (l r : ℝ) : ℝ :=
  200000 * (3 * (((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / Real.exp (2 * l)) *
    Real.exp (r / 2)) * ((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / (Real.exp (2 * l) / 2)) *
    ((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / (Real.exp (2 * l) / 4)) *
    ((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / (Real.exp (2 * l) / 8)) *
    ((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / (Real.exp (2 * l) / 16)) *
    ((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / (Real.exp (2 * l) / 32)))

theorem hpThetaGaussianKernelFourthDerivativeMajorant_le_gaussian (l r : ℝ) (n : ℕ) :
    hpThetaGaussianKernelFourthDerivativeMajorant l r n ≤
      hpThetaGaussianKernelFourthDerivativeComparisonConstant l r *
        (2 * Real.exp (-hpThetaGaussianParameter n * (Real.exp (2 * l) / 64))) := by
  have h := mul_le_mul_of_nonneg_left
    (hpTheta_sextic_factor_gaussian_bound (hpThetaGaussianParameter n)
      (Real.exp (2 * l)) (Real.exp (2 * r)) r
      (hpThetaGaussianParameter_nonneg n) (Real.exp_pos _) (Real.exp_nonneg _))
    (by norm_num : (0 : ℝ) ≤ 200000)
  simpa only [hpThetaGaussianKernelFourthDerivativeMajorant,
    hpThetaGaussianKernelFourthDerivativeComparisonConstant, mul_assoc] using h

theorem hpThetaGaussianKernelFourthDerivativeMajorant_summable (l r : ℝ) :
    Summable (hpThetaGaussianKernelFourthDerivativeMajorant l r) := by
  have hg := hpThetaGaussianParameter_series_summable
    (Real.exp (2 * l) / 64) (by positivity)
  have hc := Summable.mul_left
    (hpThetaGaussianKernelFourthDerivativeComparisonConstant l r) hg
  exact Summable.of_nonneg_of_le
    (fun n => hpThetaGaussianKernelFourthDerivativeMajorant_nonneg l r n)
    (fun n => hpThetaGaussianKernelFourthDerivativeMajorant_le_gaussian l r n) hc

theorem hpThetaPhi_thirdDeriv_hasDerivAt_kernelSeries (u : ℝ) :
    HasDerivAt (deriv (deriv (deriv hpRiemannThetaDifferentialKernel)))
      (∑' n : ℕ, hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter n) u) u := by
  have hu : u ∈ Set.Ioo (u - 1) (u + 1) := by constructor <;> linarith
  exact hpThetaPhi_thirdDeriv_hasDerivAt_of_fourth_local_majorant
    (Set.Ioo (u - 1) (u + 1))
    (hpThetaGaussianKernelFourthDerivativeMajorant (u - 1) (u + 1))
    isOpen_Ioo isPreconnected_Ioo
    (hpThetaGaussianKernelFourthDerivativeMajorant_summable (u - 1) (u + 1))
    (hpThetaGaussianKernelFourthDerivativeTerm_bound_on_Ioo (u - 1) (u + 1)) u u hu hu

theorem hpThetaPhi_fourthDeriv_eq_kernelSeries (u : ℝ) :
    deriv (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) u =
      ∑' n : ℕ, hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter n) u :=
  (hpThetaPhi_thirdDeriv_hasDerivAt_kernelSeries u).deriv

#print axioms hpThetaGaussianKernelFourthDerivativeMajorant_nonneg
#print axioms hpThetaGaussianKernelFourthDerivativeFactor_norm_le
#print axioms hpThetaGaussianKernelFourthDerivativeTerm_bound_on_Ioo
#print axioms hpTheta_sextic_factor_gaussian_bound
#print axioms hpThetaGaussianKernelFourthDerivativeMajorant_le_gaussian
#print axioms hpThetaGaussianKernelFourthDerivativeMajorant_summable
#print axioms hpThetaPhi_thirdDeriv_hasDerivAt_kernelSeries
#print axioms hpThetaPhi_fourthDeriv_eq_kernelSeries
end HodgeProofHP
