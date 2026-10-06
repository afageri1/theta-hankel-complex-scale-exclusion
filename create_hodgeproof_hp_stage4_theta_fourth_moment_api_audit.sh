#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaNormalizedXiFourthDerivative
lake build HodgeProofHP.Stage4ThetaPhiMomentIntegrability

target="HodgeProofHP/Stage4ThetaFourthMomentApiAudit.lean"

if [ -f "$target" ]; then
  backup="$target.before_update_$(date +%Y%m%d_%H%M%S)"
  cp -p "$target" "$backup"
  printf 'BACKUP: %s\n' "$backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaNormalizedXiFourthDerivative
import HodgeProofHP.Stage4ThetaPhiMomentIntegrability

/-!
Audit the existing theta moment integrability results before extending
the cosine integral derivative calculation to fourth order.
-/

namespace HodgeProofHP

#check hpThetaPhi_exp_weighted_integrableOn
#check hpThetaPhi_integrableOn
#check hpThetaPhi_secondMoment_integrableOn
#check hpRiemannThetaDifferentialKernel_continuous
#check hpRiemannXiCritical_eq_differentialKernel_cosine_integral
#check hpThetaNormalizedXiFourthTraceCoefficient_eq_xi_ratio

#print axioms hpThetaPhi_exp_weighted_integrableOn
#print axioms hpThetaPhi_secondMoment_integrableOn
#print axioms hpThetaNormalizedXiFourthTraceCoefficient_eq_xi_ratio

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaFourthMomentApiAudit

python - <<'PY'
from pathlib import Path

required = Path("HodgeProofHP/Stage4ThetaPhiMomentIntegrability.lean")
if not required.is_file():
    raise SystemExit(f"STOP: missing file: {required}")

print(f"\n=== SOURCE: {required} ===")
print(required.read_text(encoding="utf-8"))

root = Path("HodgeProofHP")
candidates = []
for path in sorted(root.glob("Stage4*.lean")):
    source = path.read_text(encoding="utf-8")
    if (
        "hasDerivAt_integral" in source
        or "hasDerivAt_integral_of_dominated" in source
    ) and (
        "hpRiemannXiCritical" in source
        or "hpRiemannThetaDifferentialKernel" in source
    ):
        candidates.append((path, source))

print("\n=== EXISTING XI INTEGRAL DIFFERENTIATION FILES ===")
if not candidates:
    print("No matching source files found.")
else:
    for path, source in candidates:
        print(f"\n=== SOURCE: {path} ===")
        print(source)
PY

printf '%s\n' 'PASS: Stage4ThetaFourthMomentApiAudit'
