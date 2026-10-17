/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityLogCurvature
import HodgeProofHP.Stage7ThetaJensenCNVZeroBoundary
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Actual density curvature derivative and flat zero boundary

The density curvature has an explicit derivative involving Phi'''.
Both the curvature and its first derivative vanish at zero.
In particular L(t)/t -> 0 from the right, so no positive linear
lower bound can hold throughout a right interval.

This rules out reusing the positive-first-derivative endpoint argument
for the CNV tail expression. Higher-order endpoint control and global
density curvature positivity remain unproved.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace HodgeProofHP

def hpThetaPhiDensityCurvatureFirstDerivative (t : ℝ) : ℝ :=
  2 * deriv hpRiemannThetaDifferentialKernel t ^ 2 +
    t * deriv hpRiemannThetaDifferentialKernel t *
      deriv (deriv hpRiemannThetaDifferentialKernel) t -
    t * hpRiemannThetaDifferentialKernel t *
      deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) t

theorem hpThetaPhiDensityCurvature_hasDerivAt (t : ℝ) :
    HasDerivAt hpThetaPhiDensityCurvature
      (hpThetaPhiDensityCurvatureFirstDerivative t) t := by
  have hphi := hpThetaPhi_hasDerivAt_kernelSeries t
  rw [← hpThetaPhi_deriv_eq_kernelSeries t] at hphi
  have hphi1 := hpThetaPhi_deriv_hasDerivAt_kernelSeries t
  rw [← hpThetaPhi_secondDeriv_eq_kernelSeries t] at hphi1
  have hphi2 := hpThetaPhi_secondDeriv_hasDerivAt_kernelSeries t
  rw [← hpThetaPhi_thirdDeriv_eq_kernelSeries t] at hphi2
  have h := (((hasDerivAt_id t).mul (hphi1.pow 2)).add
    (hphi.mul hphi1)).sub (((hasDerivAt_id t).mul hphi).mul hphi2)
  change HasDerivAt hpThetaPhiDensityCurvature _ t at h
  convert h using 1 <;>
    norm_num [hpThetaPhiDensityCurvatureFirstDerivative, Pi.mul_apply, id_eq] <;> ring

theorem hpThetaPhiDensityCurvature_deriv (t : ℝ) :
    deriv hpThetaPhiDensityCurvature t =
      hpThetaPhiDensityCurvatureFirstDerivative t :=
  (hpThetaPhiDensityCurvature_hasDerivAt t).deriv

theorem hpThetaPhiDensityCurvature_zero :
    hpThetaPhiDensityCurvature 0 = 0 := by
  simp [hpThetaPhiDensityCurvature, hpThetaPhi_deriv_zero]

theorem hpThetaPhiDensityCurvature_hasDerivAt_zero :
    HasDerivAt hpThetaPhiDensityCurvature 0 0 := by
  simpa only [hpThetaPhiDensityCurvatureFirstDerivative, hpThetaPhi_deriv_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul, add_zero, sub_zero]
    using hpThetaPhiDensityCurvature_hasDerivAt 0

theorem hpThetaPhiDensityCurvature_deriv_zero :
    deriv hpThetaPhiDensityCurvature 0 = 0 :=
  hpThetaPhiDensityCurvature_hasDerivAt_zero.deriv

theorem hpThetaPhiDensityCurvature_div_tendsto_right :
    Tendsto (fun t : ℝ => hpThetaPhiDensityCurvature t / t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hr : HasDerivWithinAt hpThetaPhiDensityCurvature 0 (Set.Ioi 0) 0 :=
    hpThetaPhiDensityCurvature_hasDerivAt_zero.hasDerivWithinAt
  have hlim := (hasDerivWithinAt_iff_tendsto_slope'
    (show (0 : ℝ) ∉ Set.Ioi 0 by simp)).mp hr
  have hfun : slope hpThetaPhiDensityCurvature 0 =
      (fun t : ℝ => hpThetaPhiDensityCurvature t / t) := by
    funext t
    simp only [slope_def_field, hpThetaPhiDensityCurvature_zero, sub_zero]
  rw [hfun] at hlim
  exact hlim

theorem hpThetaPhiDensityCurvature_no_positive_linear_lower (c : ℝ) (hc : 0 < c) :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      c * t ≤ hpThetaPhiDensityCurvature t := by
  rintro ⟨δ, hδ, hlin⟩
  have hevent : {t : ℝ | hpThetaPhiDensityCurvature t / t < c} ∈
      𝓝[>] (0 : ℝ) :=
    hpThetaPhiDensityCurvature_div_tendsto_right.eventually (Iio_mem_nhds hc)
  rcases Metric.mem_nhdsWithin_iff.mp hevent with ⟨ε, hε, hsub⟩
  let t : ℝ := min δ ε / 2
  have hm : 0 < min δ ε := lt_min hδ hε
  have ht : 0 < t := by dsimp [t]; linarith
  have htm : t < min δ ε := by dsimp [t]; linarith
  have htδ : t < δ := htm.trans_le (min_le_left δ ε)
  have htε : t < ε := htm.trans_le (min_le_right δ ε)
  have hupper : hpThetaPhiDensityCurvature t / t < c := by
    apply hsub
    constructor
    · simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htε
    · exact ht
  have hlower : c ≤ hpThetaPhiDensityCurvature t / t :=
    (le_div_iff₀ ht).mpr (hlin t ht htδ)
  linarith

#print axioms hpThetaPhiDensityCurvature_hasDerivAt
#print axioms hpThetaPhiDensityCurvature_deriv
#print axioms hpThetaPhiDensityCurvature_zero
#print axioms hpThetaPhiDensityCurvature_hasDerivAt_zero
#print axioms hpThetaPhiDensityCurvature_deriv_zero
#print axioms hpThetaPhiDensityCurvature_div_tendsto_right
#print axioms hpThetaPhiDensityCurvature_no_positive_linear_lower
end HodgeProofHP
