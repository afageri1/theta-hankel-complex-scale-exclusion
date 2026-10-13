/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage4ThetaDifferentialKernelSeries
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Gaussian kernel derivatives and an explicit series criterion

Individual term derivatives are unconditional. Differentiation of the actual
kernel series requires the summable local majorant hypothesis displayed below.
This file does not provide that majorant or prove the CNV positivity obligation.
-/

noncomputable section
namespace HodgeProofHP

def hpThetaGaussianKernelDerivativeTerm (a u : ℝ) : ℝ :=
  (-8 * a ^ 3 * Real.exp (2 * u) ^ 3 +
    30 * a ^ 2 * Real.exp (2 * u) ^ 2 -
    15 * a * Real.exp (2 * u)) * hpThetaGaussianProfile a u

theorem hpThetaGaussianKernelTerm_hasDerivAt (a u : ℝ) :
    HasDerivAt (hpThetaGaussianKernelTerm a)
      (hpThetaGaussianKernelDerivativeTerm a u) u := by
  have he := ((hasDerivAt_id u).const_mul 2).exp
  have hp := ((he.pow 2).const_mul (4 * a ^ 2)).sub (he.const_mul (6 * a))
  convert hp.mul (hpThetaGaussianProfile_hasDerivAt a u) using 1 <;>
    norm_num [hpThetaGaussianKernelTerm, hpThetaGaussianKernelDerivativeTerm,
      Pi.sub_apply, Pi.pow_apply] <;> ring

theorem hpThetaGaussianKernelTerm_deriv (a u : ℝ) :
    deriv (hpThetaGaussianKernelTerm a) u =
      hpThetaGaussianKernelDerivativeTerm a u :=
  (hpThetaGaussianKernelTerm_hasDerivAt a u).deriv

theorem hpThetaPhi_hasDerivAt_of_local_majorant
    (s : Set ℝ) (majorant : ℕ → ℝ)
    (hs : IsOpen s) (hconnected : IsPreconnected s)
    (hm : Summable majorant)
    (hbound : ∀ n : ℕ, ∀ v ∈ s,
      ‖hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) v‖ ≤ majorant n)
    (u0 u : ℝ) (hu0 : u0 ∈ s) (hu : u ∈ s) :
    HasDerivAt hpRiemannThetaDifferentialKernel
      (∑' n : ℕ, hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) u) u := by
  have hseries := hasDerivAt_tsum_of_isPreconnected
    hm hs hconnected
    (fun n v _ => hpThetaGaussianKernelTerm_hasDerivAt (hpThetaGaussianParameter n) v)
    hbound hu0 (hpRiemannThetaDifferentialKernel_series_summable u0) hu
  have heq : hpRiemannThetaDifferentialKernel =
      fun v : ℝ => ∑' n : ℕ, hpThetaGaussianKernelTerm (hpThetaGaussianParameter n) v := by
    funext v
    exact hpRiemannThetaDifferentialKernel_eq_tsum v
  rw [← heq] at hseries
  exact hseries

theorem hpThetaPhi_deriv_eq_tsum_of_local_majorant
    (s : Set ℝ) (majorant : ℕ → ℝ)
    (hs : IsOpen s) (hconnected : IsPreconnected s)
    (hm : Summable majorant)
    (hbound : ∀ n : ℕ, ∀ v ∈ s,
      ‖hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) v‖ ≤ majorant n)
    (u0 u : ℝ) (hu0 : u0 ∈ s) (hu : u ∈ s) :
    deriv hpRiemannThetaDifferentialKernel u =
      ∑' n : ℕ, hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) u :=
  (hpThetaPhi_hasDerivAt_of_local_majorant
    s majorant hs hconnected hm hbound u0 u hu0 hu).deriv

#print axioms hpThetaGaussianKernelTerm_hasDerivAt
#print axioms hpThetaGaussianKernelTerm_deriv
#print axioms hpThetaPhi_hasDerivAt_of_local_majorant
#print axioms hpThetaPhi_deriv_eq_tsum_of_local_majorant

end HodgeProofHP
