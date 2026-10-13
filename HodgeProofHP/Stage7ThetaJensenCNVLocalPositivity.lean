/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVWeightedTailCertifiedBounds
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Local positivity of the actual CNV expression

The proved right derivative and its positive numerical lower bound imply
an eventual linear lower bound and positivity on some right interval.
The interval length is existential; no explicit radius or global CNV
positivity is established.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace HodgeProofHP

theorem hpThetaPhiCNVTailExpression_div_tendsto_right :
    Tendsto (fun t : ℝ => hpThetaPhiCNVTailExpression t / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (hpThetaPhiCNVTailFirstDerivative 0)) := by
  have hd := hpThetaPhiCNVTailExpression_hasDerivWithinAt_nonnegative 0 le_rfl
  have hr : HasDerivWithinAt hpThetaPhiCNVTailExpression
      (hpThetaPhiCNVTailFirstDerivative 0) (Set.Ioi 0) 0 := by
    apply hd.mono
    intro t ht
    exact ht.le
  have hlim := (hasDerivWithinAt_iff_tendsto_slope'
    (show (0 : ℝ) ∉ Set.Ioi 0 by simp)).mp hr
  have hfun : slope hpThetaPhiCNVTailExpression 0 =
      (fun t : ℝ => hpThetaPhiCNVTailExpression t / t) := by
    funext t
    simp only [slope_def_field, hpThetaPhiCNVTailExpression_zero, sub_zero]
  rw [hfun] at hlim
  exact hlim

theorem hpThetaPhiCNVTailExpression_eventually_linear_lower :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (23 / 2500 : ℝ) * t < hpThetaPhiCNVTailExpression t := by
  have hcoef : (23 / 2500 : ℝ) < hpThetaPhiCNVTailFirstDerivative 0 := by
    have h := hpThetaPhiCNVTailFirstDerivative_zero_gt_certified
    linarith
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (23 / 2500 : ℝ) < hpThetaPhiCNVTailExpression t / t :=
    hpThetaPhiCNVTailExpression_div_tendsto_right.eventually (Ioi_mem_nhds hcoef)
  filter_upwards [hevent, self_mem_nhdsWithin] with t h ht
  change (0 : ℝ) < t at ht
  exact (lt_div_iff₀ ht).mp h

theorem hpThetaPhiCNVTailExpression_exists_linear_lower_interval :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (23 / 2500 : ℝ) * t < hpThetaPhiCNVTailExpression t := by
  have hevent : {t : ℝ | (23 / 2500 : ℝ) * t < hpThetaPhiCNVTailExpression t} ∈
      𝓝[>] (0 : ℝ) := hpThetaPhiCNVTailExpression_eventually_linear_lower
  rcases Metric.mem_nhdsWithin_iff.mp hevent with ⟨δ, hδ, hsub⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  apply hsub
  constructor
  · simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htδ
  · exact ht

theorem hpThetaPhiCNVTailExpression_exists_positive_interval :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ioo 0 δ, 0 < hpThetaPhiCNVTailExpression t := by
  rcases hpThetaPhiCNVTailExpression_exists_linear_lower_interval with ⟨δ, hδ, hlin⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  exact lt_trans (mul_pos (by norm_num : (0 : ℝ) < 23 / 2500) ht.1)
    (hlin t ht.1 ht.2)

#print axioms hpThetaPhiCNVTailExpression_div_tendsto_right
#print axioms hpThetaPhiCNVTailExpression_eventually_linear_lower
#print axioms hpThetaPhiCNVTailExpression_exists_linear_lower_interval
#print axioms hpThetaPhiCNVTailExpression_exists_positive_interval
end HodgeProofHP
