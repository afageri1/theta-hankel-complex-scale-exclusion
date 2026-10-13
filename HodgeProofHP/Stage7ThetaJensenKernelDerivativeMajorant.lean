/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenKernelDerivativeCriterion
import HodgeProofHP.Stage4ThetaSecondMajorantSummable

/-! Explicit local cubic majorant. No CNV positivity assertion is made. -/
noncomputable section
namespace HodgeProofHP

def hpThetaGaussianKernelDerivativeMajorant (l r : ℝ) (n : ℕ) : ℝ :=
  200 * ((1 / 2 : ℝ) + 2 * hpThetaGaussianParameter n * Real.exp (2 * r)) ^ 3 *
    (2 * Real.exp (r / 2 - hpThetaGaussianParameter n * Real.exp (2 * l)))

theorem hpThetaGaussianKernelDerivativeMajorant_nonneg (l r : ℝ) (n : ℕ) :
    0 ≤ hpThetaGaussianKernelDerivativeMajorant l r n := by
  have ha := hpThetaGaussianParameter_nonneg n
  unfold hpThetaGaussianKernelDerivativeMajorant
  positivity

theorem hpThetaGaussianKernelDerivativeFactor_norm_le
    (a r u : ℝ) (ha : 0 ≤ a) (hur : u ≤ r) :
    ‖-8 * a ^ 3 * Real.exp (2 * u) ^ 3 +
      30 * a ^ 2 * Real.exp (2 * u) ^ 2 - 15 * a * Real.exp (2 * u)‖ ≤
      200 * ((1 / 2 : ℝ) + 2 * a * Real.exp (2 * r)) ^ 3 := by
  let x := a * Real.exp (2 * u)
  let y := a * Real.exp (2 * r)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hxy : x ≤ y := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith)) ha
  have hxy2 : x ^ 2 ≤ y ^ 2 := by nlinarith
  have hxy3 : x ^ 3 ≤ y ^ 3 := by
    simpa only [pow_succ] using mul_le_mul hxy2 hxy hx (sq_nonneg y)
  have hn : ‖-8 * x ^ 3 + 30 * x ^ 2 - 15 * x‖ ≤
      8 * y ^ 3 + 30 * y ^ 2 + 15 * y := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> nlinarith [pow_nonneg hx 3, pow_nonneg hy 3, sq_nonneg x]
  have hp : 8 * y ^ 3 + 30 * y ^ 2 + 15 * y ≤
      200 * ((1 / 2 : ℝ) + 2 * y) ^ 3 := by
    nlinarith [pow_nonneg hy 3, sq_nonneg y]
  have heq : -8 * a ^ 3 * Real.exp (2 * u) ^ 3 +
      30 * a ^ 2 * Real.exp (2 * u) ^ 2 - 15 * a * Real.exp (2 * u) =
      -8 * x ^ 3 + 30 * x ^ 2 - 15 * x := by dsimp [x]; ring
  rw [heq]
  simpa only [y, mul_assoc] using hn.trans hp

theorem hpThetaGaussianKernelDerivativeTerm_bound_on_Ioo (l r : ℝ) :
    ∀ n : ℕ, ∀ u ∈ Set.Ioo l r,
      ‖hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) u‖ ≤
        hpThetaGaussianKernelDerivativeMajorant l r n := by
  intro n u hu
  have ha := hpThetaGaussianParameter_nonneg n
  have hf := hpThetaGaussianKernelDerivativeFactor_norm_le
    (hpThetaGaussianParameter n) r u ha hu.2.le
  have hg := hpThetaGaussianProfile_norm_le_on_interval
    (hpThetaGaussianParameter n) l r u ha hu.1.le hu.2.le
  unfold hpThetaGaussianKernelDerivativeTerm hpThetaGaussianKernelDerivativeMajorant
  rw [norm_mul]
  exact mul_le_mul hf hg (norm_nonneg _) (by positivity)

theorem hpTheta_cubic_factor_gaussian_bound
    (a x b r : ℝ) (ha : 0 ≤ a) (hx : 0 < x) (hb : 0 ≤ b) :
    ((1 / 2 : ℝ) + 2 * a * b) ^ 3 * (2 * Real.exp (r / 2 - a * x)) ≤
      (3 * (((1 / 2 : ℝ) + 4 * b / x) * Real.exp (r / 2)) *
        ((1 / 2 : ℝ) + 4 * b / (x / 2)) *
        ((1 / 2 : ℝ) + 4 * b / (x / 4))) *
          (2 * Real.exp (-a * (x / 8))) := by
  let q : ℝ := (1 / 2 : ℝ) + 2 * a * b
  let A : ℝ := 3 * (((1 / 2 : ℝ) + 4 * b / x) * Real.exp (r / 2)) *
    ((1 / 2 : ℝ) + 4 * b / (x / 2))
  let B : ℝ := (1 / 2 : ℝ) + 4 * b / (x / 4)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h1 : (q ^ 2 + 4 * a * b) * (2 * Real.exp (r / 2 - a * x)) ≤
      A * (2 * Real.exp (-a * (x / 4))) :=
    hpTheta_quadratic_factor_gaussian_bound a x b r ha hx hb
  have heighth : (x / 4) / 2 = x / 8 := by ring
  have h2 : q * (2 * Real.exp (-a * (x / 4))) ≤
      B * (2 * Real.exp (-a * (x / 8))) := by
    simpa only [q, B, zero_div, zero_sub, Real.exp_zero, mul_one,
      heighth, neg_mul] using
      hpTheta_linear_factor_gaussian_bound a (x / 4) b 0 ha (by positivity) hb
  change q ^ 3 * (2 * Real.exp (r / 2 - a * x)) ≤
    (A * B) * (2 * Real.exp (-a * (x / 8)))
  calc
    _ ≤ q * ((q ^ 2 + 4 * a * b) * (2 * Real.exp (r / 2 - a * x))) := by
      have hp : q ^ 2 ≤ q ^ 2 + 4 * a * b := by
        have hab : 0 ≤ 4 * a * b := by positivity
        linarith
      have hm := mul_le_mul_of_nonneg_left hp hq
      have hh := mul_le_mul_of_nonneg_right hm
        (by positivity : 0 ≤ 2 * Real.exp (r / 2 - a * x))
      nlinarith [hh]
    _ ≤ q * (A * (2 * Real.exp (-a * (x / 4)))) :=
      mul_le_mul_of_nonneg_left h1 hq
    _ = A * (q * (2 * Real.exp (-a * (x / 4)))) := by ring
    _ ≤ A * (B * (2 * Real.exp (-a * (x / 8)))) :=
      mul_le_mul_of_nonneg_left h2 hA
    _ = _ := by ring

def hpThetaGaussianKernelDerivativeComparisonConstant (l r : ℝ) : ℝ :=
  200 * (3 * (((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / Real.exp (2 * l)) *
    Real.exp (r / 2)) * ((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / (Real.exp (2 * l) / 2)) *
    ((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / (Real.exp (2 * l) / 4)))

theorem hpThetaGaussianKernelDerivativeMajorant_le_gaussian (l r : ℝ) (n : ℕ) :
    hpThetaGaussianKernelDerivativeMajorant l r n ≤
      hpThetaGaussianKernelDerivativeComparisonConstant l r *
        (2 * Real.exp (-hpThetaGaussianParameter n * (Real.exp (2 * l) / 8))) := by
  have h := mul_le_mul_of_nonneg_left
    (hpTheta_cubic_factor_gaussian_bound (hpThetaGaussianParameter n)
      (Real.exp (2 * l)) (Real.exp (2 * r)) r
      (hpThetaGaussianParameter_nonneg n) (Real.exp_pos _) (Real.exp_nonneg _))
    (by norm_num : (0 : ℝ) ≤ 200)
  simpa only [hpThetaGaussianKernelDerivativeMajorant,
    hpThetaGaussianKernelDerivativeComparisonConstant, mul_assoc] using h

theorem hpThetaGaussianKernelDerivativeMajorant_summable (l r : ℝ) :
    Summable (hpThetaGaussianKernelDerivativeMajorant l r) := by
  have hg := hpThetaGaussianParameter_series_summable
    (Real.exp (2 * l) / 8) (by positivity)
  have hc := Summable.mul_left (hpThetaGaussianKernelDerivativeComparisonConstant l r) hg
  exact Summable.of_nonneg_of_le
    (fun n => hpThetaGaussianKernelDerivativeMajorant_nonneg l r n)
    (fun n => hpThetaGaussianKernelDerivativeMajorant_le_gaussian l r n) hc

theorem hpThetaPhi_hasDerivAt_kernelSeries (u : ℝ) :
    HasDerivAt hpRiemannThetaDifferentialKernel
      (∑' n : ℕ, hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) u) u := by
  have hu : u ∈ Set.Ioo (u - 1) (u + 1) := by constructor <;> linarith
  exact hpThetaPhi_hasDerivAt_of_local_majorant
    (Set.Ioo (u - 1) (u + 1))
    (hpThetaGaussianKernelDerivativeMajorant (u - 1) (u + 1))
    isOpen_Ioo isPreconnected_Ioo
    (hpThetaGaussianKernelDerivativeMajorant_summable (u - 1) (u + 1))
    (hpThetaGaussianKernelDerivativeTerm_bound_on_Ioo (u - 1) (u + 1)) u u hu hu

theorem hpThetaPhi_deriv_eq_kernelSeries (u : ℝ) :
    deriv hpRiemannThetaDifferentialKernel u =
      ∑' n : ℕ, hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) u :=
  (hpThetaPhi_hasDerivAt_kernelSeries u).deriv

#print axioms hpThetaGaussianKernelDerivativeMajorant_nonneg
#print axioms hpThetaGaussianKernelDerivativeFactor_norm_le
#print axioms hpThetaGaussianKernelDerivativeTerm_bound_on_Ioo
#print axioms hpTheta_cubic_factor_gaussian_bound
#print axioms hpThetaGaussianKernelDerivativeMajorant_le_gaussian
#print axioms hpThetaGaussianKernelDerivativeMajorant_summable
#print axioms hpThetaPhi_hasDerivAt_kernelSeries
#print axioms hpThetaPhi_deriv_eq_kernelSeries
end HodgeProofHP
