/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenKernelSecondDerivativeMajorant
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Third Gaussian kernel derivative and its series criterion

Term derivatives and summability of the second derivative terms are proved.
The actual third derivative still requires the displayed summable local bound
for third derivative terms. No CNV positivity is claimed.
-/
noncomputable section
namespace HodgeProofHP

def hpThetaGaussianKernelThirdDerivativeTerm (a u : ℝ) : ℝ :=
  (-32 * a ^ 5 * Real.exp (2 * u) ^ 5 +
    360 * a ^ 4 * Real.exp (2 * u) ^ 4 -
    1058 * a ^ 3 * Real.exp (2 * u) ^ 3 +
    (1635 / 2 : ℝ) * a ^ 2 * Real.exp (2 * u) ^ 2 -
    (375 / 4 : ℝ) * a * Real.exp (2 * u)) * hpThetaGaussianProfile a u

theorem hpThetaGaussianKernelSecondDerivativeTerm_hasDerivAt (a u : ℝ) :
    HasDerivAt (hpThetaGaussianKernelSecondDerivativeTerm a)
      (hpThetaGaussianKernelThirdDerivativeTerm a u) u := by
  have he := ((hasDerivAt_id u).const_mul 2).exp
  have hp := ((((he.pow 4).const_mul (16 * a ^ 4)).sub
    ((he.pow 3).const_mul (112 * a ^ 3))).add
    ((he.pow 2).const_mul (165 * a ^ 2))).sub (he.const_mul ((75 / 2 : ℝ) * a))
  have h := hp.mul (hpThetaGaussianProfile_hasDerivAt a u)
  change HasDerivAt (hpThetaGaussianKernelSecondDerivativeTerm a) _ u at h
  convert h using 1 <;>
    norm_num [hpThetaGaussianKernelThirdDerivativeTerm] <;> ring

theorem hpThetaGaussianKernelSecondDerivativeTerm_deriv (a u : ℝ) :
    deriv (hpThetaGaussianKernelSecondDerivativeTerm a) u =
      hpThetaGaussianKernelThirdDerivativeTerm a u :=
  (hpThetaGaussianKernelSecondDerivativeTerm_hasDerivAt a u).deriv

theorem hpThetaGaussianKernelSecondDerivativeTerm_norm_summable (u : ℝ) :
    Summable (fun n : ℕ =>
      ‖hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) u‖) := by
  have hu : u ∈ Set.Ioo (u - 1) (u + 1) := by constructor <;> linarith
  exact Summable.of_nonneg_of_le
    (fun n => norm_nonneg _)
    (fun n => hpThetaGaussianKernelSecondDerivativeTerm_bound_on_Ioo (u - 1) (u + 1) n u hu)
    (hpThetaGaussianKernelSecondDerivativeMajorant_summable (u - 1) (u + 1))

theorem hpThetaGaussianKernelSecondDerivativeTerm_summable (u : ℝ) :
    Summable (fun n : ℕ =>
      hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) u) :=
  Summable.of_norm (hpThetaGaussianKernelSecondDerivativeTerm_norm_summable u)

theorem hpThetaPhi_secondDeriv_hasDerivAt_of_third_local_majorant
    (s : Set ℝ) (majorant : ℕ → ℝ)
    (hs : IsOpen s) (hconnected : IsPreconnected s)
    (hm : Summable majorant)
    (hbound : ∀ n : ℕ, ∀ v ∈ s,
      ‖hpThetaGaussianKernelThirdDerivativeTerm (hpThetaGaussianParameter n) v‖ ≤ majorant n)
    (u0 u : ℝ) (hu0 : u0 ∈ s) (hu : u ∈ s) :
    HasDerivAt (deriv (deriv hpRiemannThetaDifferentialKernel))
      (∑' n : ℕ, hpThetaGaussianKernelThirdDerivativeTerm (hpThetaGaussianParameter n) u) u := by
  have hseries := hasDerivAt_tsum_of_isPreconnected
    hm hs hconnected
    (fun n v _ => hpThetaGaussianKernelSecondDerivativeTerm_hasDerivAt (hpThetaGaussianParameter n) v)
    hbound hu0 (hpThetaGaussianKernelSecondDerivativeTerm_summable u0) hu
  have heq : deriv (deriv hpRiemannThetaDifferentialKernel) =
      fun v : ℝ => ∑' n : ℕ,
        hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) v := by
    funext v
    exact hpThetaPhi_secondDeriv_eq_kernelSeries v
  rw [← heq] at hseries
  exact hseries

theorem hpThetaPhi_thirdDeriv_eq_tsum_of_local_majorant
    (s : Set ℝ) (majorant : ℕ → ℝ)
    (hs : IsOpen s) (hconnected : IsPreconnected s)
    (hm : Summable majorant)
    (hbound : ∀ n : ℕ, ∀ v ∈ s,
      ‖hpThetaGaussianKernelThirdDerivativeTerm (hpThetaGaussianParameter n) v‖ ≤ majorant n)
    (u0 u : ℝ) (hu0 : u0 ∈ s) (hu : u ∈ s) :
    deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) u =
      ∑' n : ℕ, hpThetaGaussianKernelThirdDerivativeTerm (hpThetaGaussianParameter n) u :=
  (hpThetaPhi_secondDeriv_hasDerivAt_of_third_local_majorant
    s majorant hs hconnected hm hbound u0 u hu0 hu).deriv

#print axioms hpThetaGaussianKernelSecondDerivativeTerm_hasDerivAt
#print axioms hpThetaGaussianKernelSecondDerivativeTerm_deriv
#print axioms hpThetaGaussianKernelSecondDerivativeTerm_norm_summable
#print axioms hpThetaGaussianKernelSecondDerivativeTerm_summable
#print axioms hpThetaPhi_secondDeriv_hasDerivAt_of_third_local_majorant
#print axioms hpThetaPhi_thirdDeriv_eq_tsum_of_local_majorant
end HodgeProofHP
