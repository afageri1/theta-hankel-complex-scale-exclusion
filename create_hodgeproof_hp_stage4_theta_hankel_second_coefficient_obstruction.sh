#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelBasisTrace

target="HodgeProofHP/Stage4ThetaHankelSecondCoefficientObstruction.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelBasisTrace

/-!
Conditional obstruction for a proposed even determinant.

D is an arbitrary complex function. The second-derivative/trace
identity is an explicit hypothesis, not a proved Fredholm identity.

For a normalized even determinant det(I - z^2 S), the intended
identity is D''(0) = -2 trace(S).
-/

namespace HodgeProofHP

theorem hpThetaHankel_secondCoefficient_ne_xiRatio_of_trace_identity
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (D : ℂ → ℂ)
    (hD :
      (deriv (deriv D) 0).re =
        -2 * (hpThetaHankelBasisTrace
          b hpThetaHankelAdjointSquare).re) :
    -(deriv (deriv D) 0).re / 2 ≠
      -(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re) := by
  have hc :
      -(deriv (deriv D) 0).re / 2 =
        (hpThetaHankelBasisTrace
          b hpThetaHankelAdjointSquare).re := by
    rw [hD]
    ring
  rw [hc]
  exact hpThetaHankelBasisTrace_adjointSquare_re_ne_xiRatio b

theorem hpThetaHankel_secondCoefficient_matching_incompatible
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (D : ℂ → ℂ) :
    ¬ (
      (deriv (deriv D) 0).re =
        -2 * (hpThetaHankelBasisTrace
          b hpThetaHankelAdjointSquare).re ∧
      -(deriv (deriv D) 0).re / 2 =
        -(deriv (deriv hpRiemannXiCritical) 0).re /
          (2 * (hpRiemannXiCritical 0).re)) := by
  rintro ⟨htrace, hmatch⟩
  exact
    hpThetaHankel_secondCoefficient_ne_xiRatio_of_trace_identity
      b D htrace hmatch

#print axioms hpThetaHankel_secondCoefficient_ne_xiRatio_of_trace_identity
#print axioms hpThetaHankel_secondCoefficient_matching_incompatible

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelSecondCoefficientObstruction

printf '%s\n' 'PASS: Stage4ThetaHankelSecondCoefficientObstruction'
