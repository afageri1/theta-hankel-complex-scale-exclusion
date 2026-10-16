/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVFarDerivativeBound
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Explicit analytic upper barrier for the actual weighted tail

The barrier retains the polynomial and exponential factors of the first
Gaussian profile. Its derivative is no greater than -t*Phi(t). Comparing the
barrier minus the actual tail on finite intervals, then using I(R) -> 0,
gives I(t) <= H(t). The barrier is nonnegative, so its own limit is unnecessary.
This upper bound alone does not establish global CNV positivity.
-/
noncomputable section
open Filter
open scoped Topology
namespace HodgeProofHP

def hpThetaCNVWeightedTailBarrier (t : ℝ) : ℝ :=
  (12183 / 12151 : ℝ) *
    ((1 + t * (2 * Real.pi * Real.exp (2 * t) - 1 / 2)) * hpThetaGaussianProfile Real.pi t)

theorem hpThetaCNVWeightedTailBarrier_hasDerivAt (t : ℝ) :
    HasDerivAt hpThetaCNVWeightedTailBarrier
      (-(12183 / 12151 : ℝ) *
        (t * hpThetaGaussianKernelTerm Real.pi t + (t / 4) * hpThetaGaussianProfile Real.pi t)) t := by
  have he := ((hasDerivAt_id t).const_mul 2).exp
  have hk := (he.const_mul (2 * Real.pi)).sub_const (1 / 2 : ℝ)
  have hc := ((hasDerivAt_id t).mul hk).const_add 1
  have h := (hc.mul (hpThetaGaussianProfile_hasDerivAt Real.pi t)).const_mul
    (12183 / 12151 : ℝ)
  change HasDerivAt hpThetaCNVWeightedTailBarrier _ t at h
  convert h using 1 <;> norm_num [hpThetaGaussianKernelTerm] <;> ring

theorem hpThetaCNVWeightedTailBarrier_pos (t : ℝ) (ht : 0 ≤ t) :
    0 < hpThetaCNVWeightedTailBarrier t := by
  have hq := hpThetaTrace_pi_exp_ge_three t ht
  have hk : 0 ≤ 2 * Real.pi * Real.exp (2 * t) - (1 / 2 : ℝ) := by linarith
  unfold hpThetaCNVWeightedTailBarrier
  exact mul_pos (by norm_num)
    (mul_pos (by positivity) (hpThetaGaussianProfile_pos Real.pi t))

theorem hpThetaCNVWeightedTailBarrier_deriv_le (t : ℝ) (ht : 0 ≤ t) :
    deriv hpThetaCNVWeightedTailBarrier t ≤ -(t * hpRiemannThetaDifferentialKernel t) := by
  rw [(hpThetaCNVWeightedTailBarrier_hasDerivAt t).deriv]
  have hupper := mul_le_mul_of_nonneg_left (hpThetaPhi_le_firstTerm_upper t ht) ht
  have hprofile := mul_nonneg ht (hpThetaGaussianProfile_pos Real.pi t).le
  nlinarith

theorem hpThetaCNVWeightedTailBarrier_sub_tail_antitoneOn :
    AntitoneOn (fun t : ℝ => hpThetaCNVWeightedTailBarrier t - hpThetaPhiWeightedTail t)
      (Set.Ici (0 : ℝ)) := by
  have hdH : Differentiable ℝ hpThetaCNVWeightedTailBarrier :=
    fun t => (hpThetaCNVWeightedTailBarrier_hasDerivAt t).differentiableAt
  have hcH : Continuous hpThetaCNVWeightedTailBarrier := hdH.continuous
  have hcI : ContinuousOn hpThetaPhiWeightedTail (Set.Ici (0 : ℝ)) := by
    intro t ht
    have ht0 : 0 ≤ t := by simpa only [Set.mem_Ici] using ht
    exact (hpThetaPhiWeightedTail_hasDerivWithinAt_nonnegative t ht0).continuousWithinAt
  apply antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ)) (hcH.continuousOn.sub hcI)
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    exact ((hpThetaCNVWeightedTailBarrier_hasDerivAt t).sub
      (hpThetaPhiWeightedTail_hasDerivAt t ht0)).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    have hH : HasDerivAt hpThetaCNVWeightedTailBarrier
        (deriv hpThetaCNVWeightedTailBarrier t) t :=
      (hpThetaCNVWeightedTailBarrier_hasDerivAt t).differentiableAt.hasDerivAt
    rw [(hH.sub (hpThetaPhiWeightedTail_hasDerivAt t ht0)).deriv]
    have h := hpThetaCNVWeightedTailBarrier_deriv_le t ht0.le
    linarith

theorem hpThetaCNV_weightedTail_finite_barrier_comparison (t R : ℝ)
    (ht : 0 ≤ t) (htR : t ≤ R) :
    hpThetaPhiWeightedTail t - hpThetaPhiWeightedTail R ≤
      hpThetaCNVWeightedTailBarrier t - hpThetaCNVWeightedTailBarrier R := by
  have h := hpThetaCNVWeightedTailBarrier_sub_tail_antitoneOn
    (show t ∈ Set.Ici (0 : ℝ) by simpa only [Set.mem_Ici] using ht)
    (show R ∈ Set.Ici (0 : ℝ) by simpa only [Set.mem_Ici] using ht.trans htR) htR
  linarith

theorem hpThetaPhiWeightedTail_tendsto_zero_atTop :
    Tendsto hpThetaPhiWeightedTail atTop (𝓝 (0 : ℝ)) := by
  unfold hpThetaPhiWeightedTail
  exact MeasureTheory.tendsto_integral_Ioi_zero
    (f := fun u : ℝ => u * hpRiemannThetaDifferentialKernel u)
    (μ := MeasureTheory.volume) (b := fun t : ℝ => t) tendsto_id

theorem hpThetaPhiWeightedTail_le_explicit_barrier (t : ℝ) (ht : 0 ≤ t) :
    hpThetaPhiWeightedTail t ≤ hpThetaCNVWeightedTailBarrier t := by
  have hlim : Tendsto (fun R : ℝ => hpThetaCNVWeightedTailBarrier t + hpThetaPhiWeightedTail R)
      atTop (𝓝 (hpThetaCNVWeightedTailBarrier t)) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add hpThetaPhiWeightedTail_tendsto_zero_atTop
  have hineq : ∀ᶠ R : ℝ in atTop,
      hpThetaPhiWeightedTail t ≤ hpThetaCNVWeightedTailBarrier t + hpThetaPhiWeightedTail R := by
    filter_upwards [eventually_ge_atTop t] with R hR
    have hcomp := hpThetaCNV_weightedTail_finite_barrier_comparison t R ht hR
    have hpos := hpThetaCNVWeightedTailBarrier_pos R (ht.trans hR)
    linarith
  exact le_of_tendsto hlim hineq

#print axioms hpThetaCNVWeightedTailBarrier_hasDerivAt
#print axioms hpThetaCNVWeightedTailBarrier_pos
#print axioms hpThetaCNVWeightedTailBarrier_deriv_le
#print axioms hpThetaCNVWeightedTailBarrier_sub_tail_antitoneOn
#print axioms hpThetaCNV_weightedTail_finite_barrier_comparison
#print axioms hpThetaPhiWeightedTail_tendsto_zero_atTop
#print axioms hpThetaPhiWeightedTail_le_explicit_barrier
end HodgeProofHP
