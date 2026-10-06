#!/usr/bin/env bash
set -euo pipefail

target="HodgeProofHP/Stage3HermiteDenseSpan.lean"

if [ -f "$target" ]; then
  cp "$target" "$target.bak.$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage3HermiteOrthogonalZero
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
Density of the Hermite span and of the polynomial-Gaussian range in L².
-/

noncomputable section

namespace HodgeProofHP

theorem hpHermiteL2Span_topologicalClosure_eq_top :
    hpHermiteL2Span.topologicalClosure = ⊤ := by
  exact Submodule.topologicalClosure_eq_top_iff.mpr
    hpHermiteL2Span_orthogonal_eq_bot

theorem hpHermiteL2Span_dense :
    Dense (hpHermiteL2Span : Set HPSpace) := by
  intro v
  change v ∈ hpHermiteL2Span.topologicalClosure
  simpa only [hpHermiteL2Span_topologicalClosure_eq_top] using
    (show v ∈ (⊤ : Submodule ℂ HPSpace) from by trivial)

theorem hpPolynomialGaussianL2Map_denseRange :
    DenseRange hpPolynomialGaussianL2Map := by
  change Dense (hpPolynomialGaussianL2Map.range : Set HPSpace)
  rw [hpPolynomialGaussianL2Map_range_eq_span]
  exact hpHermiteL2Span_dense

end HodgeProofHP

#print axioms HodgeProofHP.hpHermiteL2Span_topologicalClosure_eq_top
#print axioms HodgeProofHP.hpHermiteL2Span_dense
#print axioms HodgeProofHP.hpPolynomialGaussianL2Map_denseRange
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage3HermiteDenseSpan
