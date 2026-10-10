#!/usr/bin/env bash
set -euo pipefail

target="HodgeProofHP/Stage4ThetaIntegrationByPartsApiAudit.lean"
mathlib_integrals=".lake/packages/mathlib/Mathlib/MeasureTheory/Integral"

if [ ! -f lakefile.lean ] && [ ! -f lakefile.toml ]; then
  echo "STOP: run from the hodgeproof-hp repository root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaProfileZeroBoundary

if [ ! -d "$mathlib_integrals" ]; then
  echo "STOP: mathlib integral sources not found."
  exit 1
fi

echo "=== Local integration-by-parts and FTC declarations ==="
if rg -n -A 16 \
  '^(theorem|lemma) (integral_deriv_mul|integral_mul_deriv|integral_eq_sub_of_hasDerivAt|integral_eq_sub_of_hasDerivWithinAt)' \
  "$mathlib_integrals"; then
  :
else
  echo "No declarations matched this search; report this output."
fi

if [ -f "$target" ]; then
  stamp="$(date +%Y%m%d_%H%M%S)"
  cp -p "$target" "${target}.before_${stamp}_$$"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaProfileZeroBoundary

/-!
Audit the project interfaces needed for finite-interval integration
by parts in the differential theta-kernel representation.
No integration-by-parts identity is asserted in this module.
-/

namespace HodgeProofHP

-- Profile derivatives and their regularity.
#check hpRiemannThetaLogProfile_hasDerivAt
#check hpRiemannThetaLogProfile_first_hasDerivAt
#check hpRiemannThetaLogProfile_continuous
#check hpRiemannThetaLogProfile_deriv_continuous
#check hpRiemannThetaLogProfile_deriv_differentiable
#check hpRiemannThetaLogProfile_secondDeriv_function

-- Exact differential-kernel normalization.
#print hpRiemannThetaDifferentialKernel

-- Verified lower-boundary value.
#check hpRiemannThetaLogProfile_deriv_zero
#print axioms hpRiemannThetaLogProfile_deriv_zero

-- Integrability interfaces: print hypotheses, not proof terms.
#check hpRiemannThetaLogProfile_cos_integrableOn
#check hpRiemannThetaLogProfile_deriv_sin_integrableOn

-- Existing cosine representation to be transformed.
#check hpRiemannXiCritical_eq_logProfile_cosine_integral

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaIntegrationByPartsApiAudit

echo "PASS: integration-by-parts API audit completed."
