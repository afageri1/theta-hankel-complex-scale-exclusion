/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVSecondIntervalCriterion

/-! Adjacent closed interval bounds cover their union, including the shared endpoint. -/
noncomputable section
namespace HodgeProofHP

theorem hpThetaCNV_interval_lower_glue {f : ℝ → ℝ} {H l m r : ℝ}
    (hleft : ∀ u : ℝ, u ∈ Set.Icc l m → H ≤ f u)
    (hright : ∀ u : ℝ, u ∈ Set.Icc m r → H ≤ f u) :
    ∀ u : ℝ, u ∈ Set.Icc l r → H ≤ f u := by
  intro u hu
  by_cases hm : u ≤ m
  · exact hleft u ⟨hu.1, hm⟩
  · exact hright u ⟨(lt_of_not_ge hm).le, hu.2⟩

#print axioms hpThetaCNV_interval_lower_glue
end HodgeProofHP
