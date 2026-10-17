/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenKernelThirdDerivativeMajorant
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Fourth Gaussian kernel derivative and its series criterion

The third derivative terms are summable and have explicit derivatives.
The fourth derivative series follows under a summable local majorant.
The companion majorant module discharges that condition.
No density curvature sign or higher-order endpoint estimate is asserted.
-/
noncomputable section
namespace HodgeProofHP

def hpThetaGaussianKernelFourthDerivativeTerm (a u : ℝ) : ℝ :=
  (64 * a ^ 6 * Real.exp (2 * u) ^ 6 -
    1056 * a ^ 5 * Real.exp (2 * u) ^ 5 +
    5176 * a ^ 4 * Real.exp (2 * u) ^ 4 -
    8512 * a ^ 3 * Real.exp (2 * u) ^ 3 +
    (15465 / 4 : ℝ) * a ^ 2 * Real.exp (2 * u) ^ 2 -
    (1875 / 8 : ℝ) * a * Real.exp (2 * u)) * hpThetaGaussianProfile a u

theorem hpThetaGaussianKernelThirdDerivativeTerm_hasDerivAt (a u : ℝ) :
    HasDerivAt (hpThetaGaussianKernelThirdDerivativeTerm a)
      (hpThetaGaussianKernelFourthDerivativeTerm a u) u := by
  have he := ((hasDerivAt_id u).const_mul 2).exp
  have hp := (((((he.pow 5).const_mul (-32 * a ^ 5)).add
    ((he.pow 4).const_mul (360 * a ^ 4))).sub
    ((he.pow 3).const_mul (1058 * a ^ 3))).add
    ((he.pow 2).const_mul ((1635 / 2 : ℝ) * a ^ 2))).sub
    (he.const_mul ((375 / 4 : ℝ) * a))
  have h := hp.mul (hpThetaGaussianProfile_hasDerivAt a u)
  change HasDerivAt (hpThetaGaussianKernelThirdDerivativeTerm a) _ u at h
  convert h using 1 <;>
    norm_num [hpThetaGaussianKernelFourthDerivativeTerm] <;> ring

theorem hpThetaGaussianKernelThirdDerivativeTerm_deriv (a u : ℝ) :
    deriv (hpThetaGaussianKernelThirdDerivativeTerm a) u =
      hpThetaGaussianKernelFourthDerivativeTerm a u :=
  (hpThetaGaussianKernelThirdDerivativeTerm_hasDerivAt a u).deriv

theorem hpThetaGaussianKernelThirdDerivativeTerm_norm_summable (u : ℝ) :
    Summable (fun n : ℕ =>
      ‖hpThetaGaussianKernelThirdDerivativeTerm (hpThetaGaussianParameter n) u‖) := by
  have hu : u ∈ Set.Ioo (u - 1) (u + 1) := by constructor <;> linarith
  exact Summable.of_nonneg_of_le
    (fun n => norm_nonneg _)
    (fun n => hpThetaGaussianKernelThirdDerivativeTerm_bound_on_Ioo
      (u - 1) (u + 1) n u hu)
    (hpThetaGaussianKernelThirdDerivativeMajorant_summable (u - 1) (u + 1))

theorem hpThetaGaussianKernelThirdDerivativeTerm_summable (u : ℝ) :
    Summable (fun n : ℕ =>
      hpThetaGaussianKernelThirdDerivativeTerm (hpThetaGaussianParameter n) u) :=
  Summable.of_norm (hpThetaGaussianKernelThirdDerivativeTerm_norm_summable u)

theorem hpThetaPhi_thirdDeriv_hasDerivAt_of_fourth_local_majorant
    (s : Set ℝ) (majorant : ℕ → ℝ)
    (hs : IsOpen s) (hconnected : IsPreconnected s)
    (hm : Summable majorant)
    (hbound : ∀ n : ℕ, ∀ v ∈ s,
      ‖hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter n) v‖ ≤ majorant n)
    (u0 u : ℝ) (hu0 : u0 ∈ s) (hu : u ∈ s) :
    HasDerivAt (deriv (deriv (deriv hpRiemannThetaDifferentialKernel)))
      (∑' n : ℕ, hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter n) u) u := by
  have hseries := hasDerivAt_tsum_of_isPreconnected
    hm hs hconnected
    (fun n v _ => hpThetaGaussianKernelThirdDerivativeTerm_hasDerivAt
      (hpThetaGaussianParameter n) v)
    hbound hu0 (hpThetaGaussianKernelThirdDerivativeTerm_summable u0) hu
  have heq : deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) =
      fun v : ℝ => ∑' n : ℕ,
        hpThetaGaussianKernelThirdDerivativeTerm (hpThetaGaussianParameter n) v := by
    funext v
    exact hpThetaPhi_thirdDeriv_eq_kernelSeries v
  rw [← heq] at hseries
  exact hseries

theorem hpThetaPhi_fourthDeriv_eq_tsum_of_local_majorant
    (s : Set ℝ) (majorant : ℕ → ℝ)
    (hs : IsOpen s) (hconnected : IsPreconnected s)
    (hm : Summable majorant)
    (hbound : ∀ n : ℕ, ∀ v ∈ s,
      ‖hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter n) v‖ ≤ majorant n)
    (u0 u : ℝ) (hu0 : u0 ∈ s) (hu : u ∈ s) :
    deriv (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) u =
      ∑' n : ℕ, hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter n) u :=
  (hpThetaPhi_thirdDeriv_hasDerivAt_of_fourth_local_majorant
    s majorant hs hconnected hm hbound u0 u hu0 hu).deriv

#print axioms hpThetaGaussianKernelThirdDerivativeTerm_hasDerivAt
#print axioms hpThetaGaussianKernelThirdDerivativeTerm_deriv
#print axioms hpThetaGaussianKernelThirdDerivativeTerm_norm_summable
#print axioms hpThetaGaussianKernelThirdDerivativeTerm_summable
#print axioms hpThetaPhi_thirdDeriv_hasDerivAt_of_fourth_local_majorant
#print axioms hpThetaPhi_fourthDeriv_eq_tsum_of_local_majorant
end HodgeProofHP
