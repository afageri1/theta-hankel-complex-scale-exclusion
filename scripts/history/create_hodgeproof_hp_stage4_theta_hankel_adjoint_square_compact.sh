#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelCompactOperator
lake build HodgeProofHP.Stage4ThetaHankelAdjointSquare

target="HodgeProofHP/Stage4ThetaHankelAdjointSquareCompact.lean"

if [ -f "$target" ]; then
  backup="$target.before_update_$(date +%Y%m%d_%H%M%S)"
  cp -p "$target" "$backup"
  printf 'BACKUP: %s\n' "$backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelCompactOperator
import HodgeProofHP.Stage4ThetaHankelAdjointSquare

/-!
Compactness of the adjoint square of the theta Hankel operator.
-/

namespace HodgeProofHP

/-- The adjoint square A* A is compact because A is compact
and its adjoint is a continuous linear operator. -/
theorem hpThetaHankelAdjointSquare_isCompact :
    IsCompactOperator hpThetaHankelAdjointSquare := by
  change IsCompactOperator
    (fun x =>
      hpThetaHankelOperator.adjoint (hpThetaHankelOperator x))
  exact hpThetaHankelOperator_isCompact.clm_comp
    hpThetaHankelOperator.adjoint

#print axioms hpThetaHankelAdjointSquare_isCompact

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelAdjointSquareCompact

printf '%s\n' 'PASS: Stage4ThetaHankelAdjointSquareCompact'
