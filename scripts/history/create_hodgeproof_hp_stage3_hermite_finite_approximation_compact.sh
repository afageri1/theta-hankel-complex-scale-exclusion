#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage3HermiteFiniteApproximationCompact.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteFiniteResolventApproximation
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Compactness of finite Hermite approximations

Finite Hermite projections and finite resolvent approximations are compact.
Compactness of the full resolvent is reduced to convergence in operator norm.
-/

noncomputable section

namespace HodgeProofHP

open Filter
open scoped Topology

theorem hpHermiteFiniteSpan_finiteDimensional (N : ℕ) :
    FiniteDimensional ℂ (hpHermiteFiniteSpan N) := by
  unfold hpHermiteFiniteSpan
  apply FiniteDimensional.span_of_finite
  exact (Finset.range N).finite_toSet.image hpHermiteNormalizedL2

theorem hpHermiteFiniteProjection_isCompact (N : ℕ) :
    IsCompactOperator (hpHermiteFiniteProjection N) := by
  change hpHermiteFiniteProjection N ∈
    compactOperator (RingHom.id ℂ) HPSpace HPSpace
  unfold hpHermiteFiniteProjection
  apply Submodule.sum_mem
  intro n hn
  change IsCompactOperator
    (fun v : HPSpace =>
      ((innerSL ℂ) (hpHermiteNormalizedL2 n)) v •
        hpHermiteNormalizedL2 n)
  have h :
      IsCompactOperator
        (ContinuousLinearMap.toSpanSingleton ℂ
          (hpHermiteNormalizedL2 n)) :=
    isCompactOperator_of_locallyCompactSpace_rng
      (ContinuousLinearMap.toSpanSingleton ℂ
        (hpHermiteNormalizedL2 n))
  exact h.comp_clm ((innerSL ℂ) (hpHermiteNormalizedL2 n))

theorem hpHermiteFiniteResolventApproximation_isCompact
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (N : ℕ) :
    IsCompactOperator
      (hpHermiteFiniteResolventApproximation
        c hcIm hcRe hcNorm N) := by
  change IsCompactOperator
    (fun v : HPSpace =>
      hpHermiteFiniteProjection N
        (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v))
  exact (hpHermiteFiniteProjection_isCompact N).comp_clm
    (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm)

/-- The convergence hypothesis is convergence of continuous linear maps,
hence convergence in operator norm, rather than pointwise convergence. -/
theorem hpHarmonicUnitImaginaryResolvent_isCompact_of_norm_approximation
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1)
    (hconv :
      Tendsto
        (fun N =>
          hpHermiteFiniteResolventApproximation c hcIm hcRe hcNorm N)
        atTop
        (𝓝 (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm))) :
    IsCompactOperator
      (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm) := by
  apply isCompactOperator_of_tendsto hconv
  exact Filter.Eventually.of_forall
    (fun N =>
      hpHermiteFiniteResolventApproximation_isCompact
        c hcIm hcRe hcNorm N)

end HodgeProofHP

#print axioms HodgeProofHP.hpHermiteFiniteSpan_finiteDimensional
#print axioms HodgeProofHP.hpHermiteFiniteProjection_isCompact
#print axioms HodgeProofHP.hpHermiteFiniteResolventApproximation_isCompact
#print axioms HodgeProofHP.hpHarmonicUnitImaginaryResolvent_isCompact_of_norm_approximation
LEAN

lake build HodgeProofHP.Stage3HermiteFiniteResolventApproximation
lake env lean HodgeProofHP/Stage3HermiteFiniteApproximationCompact.lean
lake build HodgeProofHP.Stage3HermiteFiniteApproximationCompact
