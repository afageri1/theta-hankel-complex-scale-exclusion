#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "Run this script from the hodgeproof-hp project root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaFiniteCosineIBP

target="HodgeProofHP/Stage4ThetaImproperIBPApiAudit.lean"

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaFiniteCosineIBP

/-!
Audit the existing integrability and boundary-limit interfaces
needed to pass from finite to improper integration by parts.
-/

namespace HodgeProofHP

#check hpTheta_weighted_integrableOn_of_continuous_decay
#check hpTheta_mul_complex_cos_integrableOn
#check hpTheta_mul_complex_sin_integrableOn
#check hpRiemannThetaLogProfile_secondDeriv_exp_weighted_tendsto_zero
#check hpRiemannThetaLogProfile_deriv_cos_boundary_tendsto_zero
#check hpRiemannThetaLogProfile_sin_boundary_tendsto_zero
#check hpRiemannThetaLogProfile_cos_integrableOn
#check hpRiemannThetaLogProfile_secondDeriv_continuous
#check hpRiemannThetaLogProfile_secondDeriv_finite_cosine_ibp

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaImproperIBPApiAudit

echo "===== Improper integral convergence APIs ====="
rg -n -A 22 -B 3 \
  'theorem.*(intervalIntegral_tendsto_integral_Ioi|tendsto_integral_Ioi|integral_Ioi_mul_deriv_eq_deriv_mul|integral_Ioi_deriv_mul_eq_sub)' \
  .lake/packages/mathlib/Mathlib \
  --glob '*.lean' || true

echo "PASS: improper integration by parts API audit"
