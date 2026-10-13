/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenKernelSecondDerivativeCriterion

/-! Explicit local quartic majorant and the actual second kernel derivative. No CNV positivity assertion is made. -/
noncomputable section
namespace HodgeProofHP

def hpThetaGaussianKernelSecondDerivativeMajorant (l r : ℝ) (n : ℕ) : ℝ :=
  2000 * ((1 / 2 : ℝ) + 2 * hpThetaGaussianParameter n * Real.exp (2 * r)) ^ 4 *
    (2 * Real.exp (r / 2 - hpThetaGaussianParameter n * Real.exp (2 * l)))

theorem hpThetaGaussianKernelSecondDerivativeMajorant_nonneg (l r : ℝ) (n : ℕ) :
    0 ≤ hpThetaGaussianKernelSecondDerivativeMajorant l r n := by
  have ha := hpThetaGaussianParameter_nonneg n
  unfold hpThetaGaussianKernelSecondDerivativeMajorant
  positivity

theorem hpThetaGaussianKernelSecondDerivativeFactor_norm_le
    (a r u : ℝ) (ha : 0 ≤ a) (hur : u ≤ r) :
    ‖16 * a ^ 4 * Real.exp (2 * u) ^ 4 -
      112 * a ^ 3 * Real.exp (2 * u) ^ 3 +
      165 * a ^ 2 * Real.exp (2 * u) ^ 2 -
      (75 / 2 : ℝ) * a * Real.exp (2 * u)‖ ≤
      2000 * ((1 / 2 : ℝ) + 2 * a * Real.exp (2 * r)) ^ 4 := by
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
  have hn : ‖16 * x ^ 4 - 112 * x ^ 3 + 165 * x ^ 2 - (75 / 2 : ℝ) * x‖ ≤
      16 * y ^ 4 + 112 * y ^ 3 + 165 * y ^ 2 + (75 / 2 : ℝ) * y := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> nlinarith [pow_nonneg hx 3, pow_nonneg hy 3,
      pow_nonneg hx 4, pow_nonneg hy 4, sq_nonneg x]
  have hp : 16 * y ^ 4 + 112 * y ^ 3 + 165 * y ^ 2 + (75 / 2 : ℝ) * y ≤
      2000 * ((1 / 2 : ℝ) + 2 * y) ^ 4 := by
    nlinarith [pow_nonneg hy 3, pow_nonneg hy 4, sq_nonneg y]
  have heq : 16 * a ^ 4 * Real.exp (2 * u) ^ 4 -
      112 * a ^ 3 * Real.exp (2 * u) ^ 3 +
      165 * a ^ 2 * Real.exp (2 * u) ^ 2 -
      (75 / 2 : ℝ) * a * Real.exp (2 * u) =
      16 * x ^ 4 - 112 * x ^ 3 + 165 * x ^ 2 - (75 / 2 : ℝ) * x := by
    dsimp [x]
    ring
  rw [heq]
  simpa only [y, mul_assoc] using hn.trans hp

theorem hpThetaGaussianKernelSecondDerivativeTerm_bound_on_Ioo (l r : ℝ) :
    ∀ n : ℕ, ∀ u ∈ Set.Ioo l r,
      ‖hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) u‖ ≤
        hpThetaGaussianKernelSecondDerivativeMajorant l r n := by
  intro n u hu
  have ha := hpThetaGaussianParameter_nonneg n
  have hf := hpThetaGaussianKernelSecondDerivativeFactor_norm_le
    (hpThetaGaussianParameter n) r u ha hu.2.le
  have hg := hpThetaGaussianProfile_norm_le_on_interval
    (hpThetaGaussianParameter n) l r u ha hu.1.le hu.2.le
  unfold hpThetaGaussianKernelSecondDerivativeTerm hpThetaGaussianKernelSecondDerivativeMajorant
  rw [norm_mul]
  exact mul_le_mul hf hg (norm_nonneg _) (by positivity)

theorem hpTheta_quartic_factor_gaussian_bound
    (a x b r : ℝ) (ha : 0 ≤ a) (hx : 0 < x) (hb : 0 ≤ b) :
    ((1 / 2 : ℝ) + 2 * a * b) ^ 4 * (2 * Real.exp (r / 2 - a * x)) ≤
      (3 * (((1 / 2 : ℝ) + 4 * b / x) * Real.exp (r / 2)) *
        ((1 / 2 : ℝ) + 4 * b / (x / 2)) *
        ((1 / 2 : ℝ) + 4 * b / (x / 4)) *
        ((1 / 2 : ℝ) + 4 * b / (x / 8))) *
          (2 * Real.exp (-a * (x / 16))) := by
  let q : ℝ := (1 / 2 : ℝ) + 2 * a * b
  let A : ℝ := 3 * (((1 / 2 : ℝ) + 4 * b / x) * Real.exp (r / 2)) *
    ((1 / 2 : ℝ) + 4 * b / (x / 2)) *
    ((1 / 2 : ℝ) + 4 * b / (x / 4))
  let B : ℝ := (1 / 2 : ℝ) + 4 * b / (x / 8)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h1 : q ^ 3 * (2 * Real.exp (r / 2 - a * x)) ≤
      A * (2 * Real.exp (-a * (x / 8))) :=
    hpTheta_cubic_factor_gaussian_bound a x b r ha hx hb
  have hsixteenth : (x / 8) / 2 = x / 16 := by ring
  have h2 : q * (2 * Real.exp (-a * (x / 8))) ≤
      B * (2 * Real.exp (-a * (x / 16))) := by
    simpa only [q, B, zero_div, zero_sub, Real.exp_zero, mul_one,
      hsixteenth, neg_mul] using
      hpTheta_linear_factor_gaussian_bound a (x / 8) b 0 ha (by positivity) hb
  change q ^ 4 * (2 * Real.exp (r / 2 - a * x)) ≤
    (A * B) * (2 * Real.exp (-a * (x / 16)))
  calc
    _ = q * (q ^ 3 * (2 * Real.exp (r / 2 - a * x))) := by ring
    _ ≤ q * (A * (2 * Real.exp (-a * (x / 8)))) :=
      mul_le_mul_of_nonneg_left h1 hq
    _ = A * (q * (2 * Real.exp (-a * (x / 8)))) := by ring
    _ ≤ A * (B * (2 * Real.exp (-a * (x / 16)))) :=
      mul_le_mul_of_nonneg_left h2 hA
    _ = _ := by ring

def hpThetaGaussianKernelSecondDerivativeComparisonConstant (l r : ℝ) : ℝ :=
  2000 * (3 * (((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / Real.exp (2 * l)) *
    Real.exp (r / 2)) * ((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / (Real.exp (2 * l) / 2)) *
    ((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / (Real.exp (2 * l) / 4)) *
    ((1 / 2 : ℝ) + 4 * Real.exp (2 * r) / (Real.exp (2 * l) / 8)))

theorem hpThetaGaussianKernelSecondDerivativeMajorant_le_gaussian (l r : ℝ) (n : ℕ) :
    hpThetaGaussianKernelSecondDerivativeMajorant l r n ≤
      hpThetaGaussianKernelSecondDerivativeComparisonConstant l r *
        (2 * Real.exp (-hpThetaGaussianParameter n * (Real.exp (2 * l) / 16))) := by
  have h := mul_le_mul_of_nonneg_left
    (hpTheta_quartic_factor_gaussian_bound (hpThetaGaussianParameter n)
      (Real.exp (2 * l)) (Real.exp (2 * r)) r
      (hpThetaGaussianParameter_nonneg n) (Real.exp_pos _) (Real.exp_nonneg _))
    (by norm_num : (0 : ℝ) ≤ 2000)
  simpa only [hpThetaGaussianKernelSecondDerivativeMajorant,
    hpThetaGaussianKernelSecondDerivativeComparisonConstant, mul_assoc] using h

theorem hpThetaGaussianKernelSecondDerivativeMajorant_summable (l r : ℝ) :
    Summable (hpThetaGaussianKernelSecondDerivativeMajorant l r) := by
  have hg := hpThetaGaussianParameter_series_summable
    (Real.exp (2 * l) / 16) (by positivity)
  have hc := Summable.mul_left (hpThetaGaussianKernelSecondDerivativeComparisonConstant l r) hg
  exact Summable.of_nonneg_of_le
    (fun n => hpThetaGaussianKernelSecondDerivativeMajorant_nonneg l r n)
    (fun n => hpThetaGaussianKernelSecondDerivativeMajorant_le_gaussian l r n) hc

theorem hpThetaPhi_deriv_hasDerivAt_kernelSeries (u : ℝ) :
    HasDerivAt (deriv hpRiemannThetaDifferentialKernel)
      (∑' n : ℕ, hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) u) u := by
  have hu : u ∈ Set.Ioo (u - 1) (u + 1) := by constructor <;> linarith
  exact hpThetaPhi_deriv_hasDerivAt_of_second_local_majorant
    (Set.Ioo (u - 1) (u + 1))
    (hpThetaGaussianKernelSecondDerivativeMajorant (u - 1) (u + 1))
    isOpen_Ioo isPreconnected_Ioo
    (hpThetaGaussianKernelSecondDerivativeMajorant_summable (u - 1) (u + 1))
    (hpThetaGaussianKernelSecondDerivativeTerm_bound_on_Ioo (u - 1) (u + 1)) u u hu hu

theorem hpThetaPhi_secondDeriv_eq_kernelSeries (u : ℝ) :
    deriv (deriv hpRiemannThetaDifferentialKernel) u =
      ∑' n : ℕ, hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) u :=
  (hpThetaPhi_deriv_hasDerivAt_kernelSeries u).deriv

#print axioms hpThetaGaussianKernelSecondDerivativeMajorant_nonneg
#print axioms hpThetaGaussianKernelSecondDerivativeFactor_norm_le
#print axioms hpThetaGaussianKernelSecondDerivativeTerm_bound_on_Ioo
#print axioms hpTheta_quartic_factor_gaussian_bound
#print axioms hpThetaGaussianKernelSecondDerivativeMajorant_le_gaussian
#print axioms hpThetaGaussianKernelSecondDerivativeMajorant_summable
#print axioms hpThetaPhi_deriv_hasDerivAt_kernelSeries
#print axioms hpThetaPhi_secondDeriv_eq_kernelSeries
end HodgeProofHP
