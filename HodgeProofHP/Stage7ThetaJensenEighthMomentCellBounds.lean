/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenSixthMomentCellBounds

/-! Eighth-power cells reuse the proved generic natural-power integral bounds. -/
noncomputable section
open MeasureTheory
namespace HodgeProofHP
theorem hpThetaJensen_eighthCellIntegral_bounds
    (l r L U : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) (hL : 0 ≤ L)
    (hbound : ∀ u ∈ Set.Icc l r,
      L ≤ hpRiemannThetaDifferentialKernel u ∧
        hpRiemannThetaDifferentialKernel u ≤ U) :
    l ^ 8 * L * (r - l) ≤
        (∫ u : ℝ in Set.Ioo l r, u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo l r, u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        r ^ 8 * U * (r - l) :=
  hpThetaJensen_natPowerCellIntegral_bounds 8 l r L U hl hlr hL hbound

theorem hpThetaJensen_eighthCellIntegral_endpoint_bounds
    (l r : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) :
    l ^ 8 * hpThetaTraceEndpointLower l r * (r - l) ≤
        (∫ u : ℝ in Set.Ioo l r, u ^ 8 * hpRiemannThetaDifferentialKernel u) ∧
      (∫ u : ℝ in Set.Ioo l r, u ^ 8 * hpRiemannThetaDifferentialKernel u) ≤
        r ^ 8 * hpThetaJensenKernelEndpointUpper l r * (r - l) := by
  apply hpThetaJensen_eighthCellIntegral_bounds l r
    (hpThetaTraceEndpointLower l r) (hpThetaJensenKernelEndpointUpper l r)
    hl hlr (hpThetaTraceEndpointLower_nonneg l r hl)
  intro u hu
  exact ⟨hpThetaJensenKernel_endpointLower_le l r u hl hu.1 hu.2,
    hpThetaJensenKernel_le_endpointUpper l r u hl hu.1 hu.2⟩


#print axioms hpThetaJensen_eighthCellIntegral_bounds
#print axioms hpThetaJensen_eighthCellIntegral_endpoint_bounds
end HodgeProofHP
