/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenKernelThirdDerivativeCriterion

/-!
Explicit local quintic majorant and the actual third kernel derivative.
No CNV positivity assertion is made.
-/
noncomputable section
namespace HodgeProofHP

def hpThetaGaussianKernelThirdDerivativeMajorant (l r : ℝ) (n : ℕ) : ℝ :=
  20000 * ((1 / 2 : ℝ) + 2 * hpThetaGaussianParameter n * Real.exp (2 * r)) ^ 5 *
    (2 * Real.exp (r / 2 - hpThetaGaussianParameter n * Real.exp (2 * l)))

theorem hpThetaGaussianKernelThirdDerivativeMajorant_nonneg (l r : ℝ) (n : ℕ) :
    0 ≤ hpThetaGaussianKernelThirdDerivativeMajorant l r n := by
  have ha := hpThetaGaussianParameter_nonneg n
  unfold hpThetaGaussianKernelThirdDerivativeMajorant
  positivity

theorem hpThetaGaussianKernelThirdDerivativeFactor_norm_le
    (a r u : ℝ) (ha : 0 ≤ a) (hur : u ≤ r) :
    ‖-32 * a ^ 5 * Real.exp (2 * u) ^ 5 +
      360 * a ^ 4 * Real.exp (2 * u) ^ 4 -
      1058 * a ^ 3 * Real.exp (2 * u) ^ 3 +
      (1635 / 2 : ℝ) * a ^ 2 * Real.exp (2 * u) ^ 2 -
      (375 / 4 : ℝ) * a * Real.exp (2 * u)‖ ≤
      20000 * ((1 / 2 : ℝ) + 2 * a * Real.exp (2 * r)) ^ 5 := by
  let x := a * Real.exp (2 * u)
  let y := a * Real.exp (2 * r)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hxy : x ≤ y := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith)) ha
  have hxy2 : x ^ 2 ≤ y ^ 2 := by nlinarith
  have hxy3 : x ^ 3 ≤ y ^ 3 := by
    simpa only [pow_succ] using mul_le_mul hxy2 hxy hx (sq_nonneg y)
  have hxy4 : x ^ 4 ≤ y ^ 4 := by
    have h := mul_le_mul hxy2 hxy2 (sq_nonneg x) (sq_nonneg y)
    nlinarith [h]
  have hxy5 : x ^ 5 ≤ y ^ 5 := by
    simpa only [pow_succ] using
      mul_le_mul hxy4 hxy hx (pow_nonneg hy 4)
  have hn : ‖-32 * x ^ 5 + 360 * x ^ 4 - 1058 * x ^ 3 +
      (1635 / 2 : ℝ) * x ^ 2 - (375 / 4 : ℝ) * x‖ ≤
      32 * y ^ 5 + 360 * y ^ 4 + 1058 * y ^ 3 +
        (1635 / 2 : ℝ) * y ^ 2 + (375 / 4 : ℝ) * y := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> nlinarith [pow_nonneg hx 3, pow_nonneg hy 3,
      pow_nonneg hx 4, pow_nonneg hy 4, pow_nonneg hx 5,
      pow_nonneg hy 5, sq_nonneg x]
  have hp : 32 * y ^ 5 + 360 * y ^ 4 + 1058 * y ^ 3 +
      (1635 / 2 : ℝ) * y ^ 2 + (375 / 4 : ℝ) * y ≤
      20000 * ((1 / 2 : ℝ) + 2 * y) ^ 5 := by
    nlinarith [pow_nonneg hy 3, pow_nonneg hy 4, pow_nonneg hy 5, sq_nonneg y]
  have heq : -32 * a ^ 5 * Real.exp (2 * u) ^ 5 +
      360 * a ^ 4 * Real.exp (2 * u) ^ 4 -
      1058 * a ^ 3 * Real.exp (2 * u) ^ 3 +
      (1635 / 2 : ℝ) * a ^ 2 * Real.exp (2 * u) ^ 2 -
      (375 / 4 : ℝ) * a * Real.exp (2 * u) =
      -32 * x ^ 5 + 360 * x ^ 4 - 1058 * x ^ 3 +
        (1635 / 2 : ℝ) * x ^ 2 - (375 / 4 : ℝ) * x := by
    dsimp [x]
    ring
  rw [heq]
  simpa only [y, mul_assoc] using hn.trans hp

theorem hpThetaGaussianKernelThirdDerivativeTerm_bound_on_Ioo (l r : ℝ) :
    ∀ n : ℕ, ∀ u ∈ Set.Ioo l r,
      ‖hpThetaGaussianKernelThirdDerivativeTerm (hpThetaGaussianParameter n) u‖ ≤
        hpThetaGaussianKernelThirdDerivativeMajorant l r n := by
  intro n u hu
  have ha := hpThetaGaussianParameter_nonneg n
  have hf := hpThetaGaussianKernelThirdDerivativeFactor_norm_le
    (hpThetaGaussianParameter n) r u ha hu.2.le
  have hg := hpThetaGaussianProfile_norm_le_on_interval
    (hpThetaGaussianParameter n) l r u ha hu.1.le hu.2.le
  unfold hpThetaGaussianKernelThirdDerivativeTerm hpThetaGaussianKernelThirdDerivativeMajorant
  rw [norm_mul]
  exact mul_le_mul hf hg (norm_nonneg _) (by positivity)

theorem hpTheta_quintic_factor_gaussian_bound
    (a x b r : ℝ) (ha : 0 ≤ a) (hx : 0 < x) (hb : 0 ≤ b) :
    ((1 / 2 : ℝ) + 2 * a * b) ^ 5 * (2 * Real.exp (r / 2 - a * x)) ≤
      (3 * (((1 / 2 : ℝ) + 4 * b / x) * Real.exp (r / 2)) *
        ((1 / 2 : ℝ) + 4 * b / (x / 2)) *
        ((1 / 2 : ℝ) + 4 * b / (x / 4)) *
        ((1 / 2 : ℝ) + 4 * b / (x / 8)) *
        ((1 / 2 : ℝ) + 4 * b / (x / 16))) *
          (2 * Real.exp (-a * (x / 32))) := by
  let q : ℝ := (1 / 2 : ℝ) + 2 * a * b
  let A : ℝ := 3 * (((1 / 2 : ℝ) + 4 * b / x) * Real.exp (r / 2)) *
    ((1 / 2 : ℝ) + 4 * b / (x / 2)) *
    ((1 / 2 : ℝ) + 4 * b / (x / 4)) *
    ((1 / 2 : ℝ) + 4 * b / (x / 8))
  let B : ℝ := (1 / 2 : ℝ) + 4 * b / (x / 16)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h1 : q ^ 4 * (2 * Real.exp (r / 2 - a * x)) ≤
      A * (2 * Real.exp (-a * (x / 16))) :=
    hpTheta_quartic_factor_gaussian_bound a x b r ha hx hb
  have hthirtysecond : (x / 16) / 2 = x / 32 := by ring
  have h2 : q * (2 * Real.exp (-a * (x / 16))) ≤
      B * (2 * Real.exp (-a * (x / 32))) := by
    simpa only [q, B, zero_div, zero_sub, Real.exp_zero, mul_one,
      hthirtysecond, neg_mul] using
      hpTheta_linear_factor_gaussian_bound a (x / 16) b 0 ha (by positivity) hb
  change q ^ 5 * (2 * Real.exp (r / 2 - a * x)) ≤
    (A * B) * (2 * Real.exp (-a * (x / 32)))
  calc
    _ = q * (q ^ 4 * (2 * Real.exp (r / 2 - a * x))) := by ring
    _ ≤ q * (A * (2 * Real.exp (-a * (x / 16)))) :=
      mul_le_mul_of_nonneg_left h1 hq
    _ = A * (q * (2 * Real.exp (-a * (x / 16)))) := by ring
    _ ≤ A * (B * (2 * Real.exp (-a * (x / 32)))) :=
      mul_le_mul_of_nonneg_left h2 hA
    _ = _ := by ring

def hpThetaGaussianKernelThirdDerivativeComparisonConstant (l r : ℝ) : ℝ :=
  20000 * (3 * (((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / Real.exp (2 * l)) *
    Real.exp (r / 2)) * ((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / (Real.exp (2 * l) / 2)) *
    ((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / (Real.exp (2 * l) / 4)) *
    ((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / (Real.exp (2 * l) / 8)) *
    ((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / (Real.exp (2 * l) / 16)))

theorem hpThetaGaussianKernelThirdDerivativeMajorant_le_gaussian (l r : ℝ) (n : ℕ) :
    hpThetaGaussianKernelThirdDerivativeMajorant l r n ≤
      hpThetaGaussianKernelThirdDerivativeComparisonConstant l r *
        (2 * Real.exp (-hpThetaGaussianParameter n * (Real.exp (2 * l) / 32))) := by
  have h := mul_le_mul_of_nonneg_left
    (hpTheta_quintic_factor_gaussian_bound (hpThetaGaussianParameter n)
      (Real.exp (2 * l)) (Real.exp (2 * r)) r
      (hpThetaGaussianParameter_nonneg n) (Real.exp_pos _) (Real.exp_nonneg _))
    (by norm_num : (0 : ℝ) ≤ 20000)
  simpa only [hpThetaGaussianKernelThirdDerivativeMajorant,
    hpThetaGaussianKernelThirdDerivativeComparisonConstant, mul_assoc] using h

theorem hpThetaGaussianKernelThirdDerivativeMajorant_summable (l r : ℝ) :
    Summable (hpThetaGaussianKernelThirdDerivativeMajorant l r) := by
  have hg := hpThetaGaussianParameter_series_summable
    (Real.exp (2 * l) / 32) (by positivity)
  have hc := Summable.mul_left (hpThetaGaussianKernelThirdDerivativeComparisonConstant l r) hg
  exact Summable.of_nonneg_of_le
    (fun n => hpThetaGaussianKernelThirdDerivativeMajorant_nonneg l r n)
    (fun n => hpThetaGaussianKernelThirdDerivativeMajorant_le_gaussian l r n) hc

theorem hpThetaPhi_secondDeriv_hasDerivAt_kernelSeries (u : ℝ) :
    HasDerivAt (deriv (deriv hpRiemannThetaDifferentialKernel))
      (∑' n : ℕ, hpThetaGaussianKernelThirdDerivativeTerm (hpThetaGaussianParameter n) u) u := by
  have hu : u ∈ Set.Ioo (u - 1) (u + 1) := by constructor <;> linarith
  exact hpThetaPhi_secondDeriv_hasDerivAt_of_third_local_majorant
    (Set.Ioo (u - 1) (u + 1))
    (hpThetaGaussianKernelThirdDerivativeMajorant (u - 1) (u + 1))
    isOpen_Ioo isPreconnected_Ioo
    (hpThetaGaussianKernelThirdDerivativeMajorant_summable (u - 1) (u + 1))
    (hpThetaGaussianKernelThirdDerivativeTerm_bound_on_Ioo (u - 1) (u + 1)) u u hu hu

theorem hpThetaPhi_thirdDeriv_eq_kernelSeries (u : ℝ) :
    deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) u =
      ∑' n : ℕ, hpThetaGaussianKernelThirdDerivativeTerm (hpThetaGaussianParameter n) u :=
  (hpThetaPhi_secondDeriv_hasDerivAt_kernelSeries u).deriv

#print axioms hpThetaGaussianKernelThirdDerivativeMajorant_nonneg
#print axioms hpThetaGaussianKernelThirdDerivativeFactor_norm_le
#print axioms hpThetaGaussianKernelThirdDerivativeTerm_bound_on_Ioo
#print axioms hpTheta_quintic_factor_gaussian_bound
#print axioms hpThetaGaussianKernelThirdDerivativeMajorant_le_gaussian
#print axioms hpThetaGaussianKernelThirdDerivativeMajorant_summable
#print axioms hpThetaPhi_secondDeriv_hasDerivAt_kernelSeries
#print axioms hpThetaPhi_thirdDeriv_eq_kernelSeries
end HodgeProofHP
