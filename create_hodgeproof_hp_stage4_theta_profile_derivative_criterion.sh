#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4ThetaProfileDerivativeCriterion.lean <<'LEAN'
import HodgeProofHP.Stage4ThetaGaussianProfileSeries
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
A local summable derivative bound implies differentiation of the
logarithmic theta profile term by term.

The majorant and its bound are explicit hypotheses.
-/

noncomputable section

namespace HodgeProofHP

/-- First derivative of the nth Gaussian profile term. -/
def hpThetaGaussianFirstTerm (n : ℕ) (u : ℝ) : ℝ :=
  (1 / 2 - 2 * hpThetaGaussianParameter n *
    Real.exp (2 * u)) *
    hpThetaGaussianProfile (hpThetaGaussianParameter n) u

theorem hpThetaGaussianTerm_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt
      (hpThetaGaussianProfile (hpThetaGaussianParameter n))
      (hpThetaGaussianFirstTerm n u) u := by
  exact hpThetaGaussianProfile_hasDerivAt
    (hpThetaGaussianParameter n) u

theorem hpRiemannThetaLogProfile_eq_tsum_function :
    hpRiemannThetaLogProfile =
      fun u : ℝ =>
        ∑' n : ℕ,
          hpThetaGaussianProfile (hpThetaGaussianParameter n) u := by
  funext u
  exact (hpThetaGaussianProfile_tsum u).symm

theorem hpRiemannThetaLogProfile_hasDerivAt_of_local_bound
    (s : Set ℝ) (majorant : ℕ → ℝ)
    (hs : IsOpen s) (hconnected : IsPreconnected s)
    (hm : Summable majorant)
    (hbound : ∀ n : ℕ, ∀ v ∈ s,
      ‖hpThetaGaussianFirstTerm n v‖ ≤ majorant n)
    (u₀ u : ℝ) (hu₀ : u₀ ∈ s) (hu : u ∈ s) :
    HasDerivAt hpRiemannThetaLogProfile
      (∑' n : ℕ, hpThetaGaussianFirstTerm n u) u := by
  have hseries :
      HasDerivAt
        (fun v : ℝ =>
          ∑' n : ℕ,
            hpThetaGaussianProfile (hpThetaGaussianParameter n) v)
        (∑' n : ℕ, hpThetaGaussianFirstTerm n u) u :=
    hasDerivAt_tsum_of_isPreconnected
      hm hs hconnected
      (fun n v _ => hpThetaGaussianTerm_hasDerivAt n v)
      hbound hu₀ (hpThetaGaussianProfile_summable u₀) hu
  rw [← hpRiemannThetaLogProfile_eq_tsum_function] at hseries
  exact hseries

theorem hpRiemannThetaLogProfile_deriv_eq_tsum_of_local_bound
    (s : Set ℝ) (majorant : ℕ → ℝ)
    (hs : IsOpen s) (hconnected : IsPreconnected s)
    (hm : Summable majorant)
    (hbound : ∀ n : ℕ, ∀ v ∈ s,
      ‖hpThetaGaussianFirstTerm n v‖ ≤ majorant n)
    (u₀ u : ℝ) (hu₀ : u₀ ∈ s) (hu : u ∈ s) :
    deriv hpRiemannThetaLogProfile u =
      ∑' n : ℕ, hpThetaGaussianFirstTerm n u :=
  (hpRiemannThetaLogProfile_hasDerivAt_of_local_bound
    s majorant hs hconnected hm hbound u₀ u hu₀ hu).deriv

#print axioms hpThetaGaussianTerm_hasDerivAt
#print axioms hpRiemannThetaLogProfile_eq_tsum_function
#print axioms hpRiemannThetaLogProfile_hasDerivAt_of_local_bound
#print axioms hpRiemannThetaLogProfile_deriv_eq_tsum_of_local_bound

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage4ThetaGaussianProfileSeries
lake env lean HodgeProofHP/Stage4ThetaProfileDerivativeCriterion.lean
lake build HodgeProofHP.Stage4ThetaProfileDerivativeCriterion
