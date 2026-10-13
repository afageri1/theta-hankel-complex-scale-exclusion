/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenKernelDerivativeMajorant
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Second Gaussian kernel derivative and its series criterion

Term derivatives and summability of the first derivative terms are proved.
The actual second derivative still requires the displayed summable local bound
for second derivative terms. No CNV positivity or higher derivative is claimed.
-/
noncomputable section
namespace HodgeProofHP

def hpThetaGaussianKernelSecondDerivativeTerm (a u : ℝ) : ℝ :=
  (16 * a ^ 4 * Real.exp (2 * u) ^ 4 -
    112 * a ^ 3 * Real.exp (2 * u) ^ 3 +
    165 * a ^ 2 * Real.exp (2 * u) ^ 2 -
    (75 / 2 : ℝ) * a * Real.exp (2 * u)) * hpThetaGaussianProfile a u

theorem hpThetaGaussianKernelDerivativeTerm_hasDerivAt (a u : ℝ) :
    HasDerivAt (hpThetaGaussianKernelDerivativeTerm a)
      (hpThetaGaussianKernelSecondDerivativeTerm a u) u := by
  have he := ((hasDerivAt_id u).const_mul 2).exp
  have hp := (((he.pow 3).const_mul (-8 * a ^ 3)).add
    ((he.pow 2).const_mul (30 * a ^ 2))).sub (he.const_mul (15 * a))
  have h := hp.mul (hpThetaGaussianProfile_hasDerivAt a u)
  change HasDerivAt (hpThetaGaussianKernelDerivativeTerm a) _ u at h
  convert h using 1 <;>
    norm_num [hpThetaGaussianKernelSecondDerivativeTerm] <;> ring

theorem hpThetaGaussianKernelDerivativeTerm_deriv (a u : ℝ) :
    deriv (hpThetaGaussianKernelDerivativeTerm a) u =
      hpThetaGaussianKernelSecondDerivativeTerm a u :=
  (hpThetaGaussianKernelDerivativeTerm_hasDerivAt a u).deriv

theorem hpThetaGaussianKernelDerivativeTerm_norm_summable (u : ℝ) :
    Summable (fun n : ℕ =>
      ‖hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) u‖) := by
  have hu : u ∈ Set.Ioo (u - 1) (u + 1) := by constructor <;> linarith
  exact Summable.of_nonneg_of_le
    (fun n => norm_nonneg _)
    (fun n => hpThetaGaussianKernelDerivativeTerm_bound_on_Ioo (u - 1) (u + 1) n u hu)
    (hpThetaGaussianKernelDerivativeMajorant_summable (u - 1) (u + 1))

theorem hpThetaGaussianKernelDerivativeTerm_summable (u : ℝ) :
    Summable (fun n : ℕ =>
      hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) u) :=
  Summable.of_norm (hpThetaGaussianKernelDerivativeTerm_norm_summable u)

theorem hpThetaPhi_deriv_hasDerivAt_of_second_local_majorant
    (s : Set ℝ) (majorant : ℕ → ℝ)
    (hs : IsOpen s) (hconnected : IsPreconnected s)
    (hm : Summable majorant)
    (hbound : ∀ n : ℕ, ∀ v ∈ s,
      ‖hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) v‖ ≤ majorant n)
    (u0 u : ℝ) (hu0 : u0 ∈ s) (hu : u ∈ s) :
    HasDerivAt (deriv hpRiemannThetaDifferentialKernel)
      (∑' n : ℕ, hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) u) u := by
  have hseries := hasDerivAt_tsum_of_isPreconnected
    hm hs hconnected
    (fun n v _ => hpThetaGaussianKernelDerivativeTerm_hasDerivAt (hpThetaGaussianParameter n) v)
    hbound hu0 (hpThetaGaussianKernelDerivativeTerm_summable u0) hu
  have heq : deriv hpRiemannThetaDifferentialKernel =
      fun v : ℝ => ∑' n : ℕ,
        hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) v := by
    funext v
    exact hpThetaPhi_deriv_eq_kernelSeries v
  rw [← heq] at hseries
  exact hseries

theorem hpThetaPhi_secondDeriv_eq_tsum_of_local_majorant
    (s : Set ℝ) (majorant : ℕ → ℝ)
    (hs : IsOpen s) (hconnected : IsPreconnected s)
    (hm : Summable majorant)
    (hbound : ∀ n : ℕ, ∀ v ∈ s,
      ‖hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) v‖ ≤ majorant n)
    (u0 u : ℝ) (hu0 : u0 ∈ s) (hu : u ∈ s) :
    deriv (deriv hpRiemannThetaDifferentialKernel) u =
      ∑' n : ℕ, hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) u :=
  (hpThetaPhi_deriv_hasDerivAt_of_second_local_majorant
    s majorant hs hconnected hm hbound u0 u hu0 hu).deriv

#print axioms hpThetaGaussianKernelDerivativeTerm_hasDerivAt
#print axioms hpThetaGaussianKernelDerivativeTerm_deriv
#print axioms hpThetaGaussianKernelDerivativeTerm_norm_summable
#print axioms hpThetaGaussianKernelDerivativeTerm_summable
#print axioms hpThetaPhi_deriv_hasDerivAt_of_second_local_majorant
#print axioms hpThetaPhi_secondDeriv_eq_tsum_of_local_majorant
end HodgeProofHP
