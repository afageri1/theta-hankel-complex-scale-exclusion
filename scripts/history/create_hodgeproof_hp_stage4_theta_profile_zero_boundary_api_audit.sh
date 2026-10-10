#!/usr/bin/env bash
set -euo pipefail

target="HodgeProofHP/Stage4ThetaProfileZeroBoundaryApiAudit.lean"

if [ ! -f lakefile.lean ] && [ ! -f lakefile.toml ]; then
  echo "STOP: run this script from the hodgeproof-hp repository root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaTrigonometricIntegrability

if [ -f "$target" ]; then
  stamp="$(date +%Y%m%d_%H%M%S)"
  cp -p "$target" "${target}.before_${stamp}_$$"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaTrigonometricIntegrability

/-!
Audit the definitions and derivative APIs needed to compute the
theta logarithmic profile's boundary derivative at zero.
This module does not assert the boundary derivative identity.
-/

namespace HodgeProofHP

-- Exact normalization and reflection identity.
#print hpRiemannThetaKernel
#print hpRiemannThetaKernel_transformation
#print hpRiemannThetaLogProfile

-- Existing derivative and continuity results.
#check hpRiemannThetaLogProfile_hasDerivAt
#print hpRiemannThetaLogProfile_deriv_function
#check hpRiemannThetaLogProfile_continuous
#check hpRiemannThetaLogProfile_deriv_continuous

-- Calculus interfaces for differentiating a reflected identity.
#check HasDerivAt.comp
#check HasDerivAt.mul
#check HasDerivAt.sub
#check HasDerivAt.deriv

-- Trust checks for the existing ingredients.
#print axioms hpRiemannThetaKernel_transformation
#print axioms hpRiemannThetaLogProfile_hasDerivAt
#print axioms hpRiemannThetaLogProfile_deriv_continuous

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaProfileZeroBoundaryApiAudit

echo "PASS: zero-boundary API audit completed."
