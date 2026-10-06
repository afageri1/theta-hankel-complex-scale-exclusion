#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "STOP: run this script from ~/hodgeproof-hp"
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaHankelSelfAdjoint

target="HodgeProofHP/Stage4HankelCompactApiAudit.lean"

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSelfAdjoint

/-!
Audit of the established theta Hankel operator and its kernel.
Compact-operator APIs are inspected separately in mathlib source.
-/

namespace HodgeProofHP

#check hpThetaHankelOperator
#check hpThetaHankelOperator_isSelfAdjoint
#check hpThetaHankelKernel_memLp
#check hpThetaHankelKernel_norm_sq_integrable
#check hpThetaHankelKernel_sq_lintegral_weight_identity
#check hpThetaHankelActionL2_norm_le

#print hpThetaHankelMeasure
#print hpThetaHankelKernel
#print hpRiemannThetaDifferentialKernel
#print hpRiemannThetaLogProfile
#print hpRiemannXiCritical_eq_differentialKernel_cosine_integral

#print axioms hpThetaHankelOperator_isSelfAdjoint

end HodgeProofHP
LEAN

lake env lean "$target"

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib")
if not root.is_dir():
    raise SystemExit("STOP: mathlib source directory not found")

groups = [
    (
        "HILBERT-SCHMIDT AND INTEGRAL-KERNEL APIs",
        re.compile(
            r"HilbertSchmidt|hilbertSchmidt|hilbert_schmidt|"
            r"IsCompactOperator.*[Kk]ernel|"
            r"[Kk]ernel.*IsCompactOperator|"
            r"integralOperator|integral_operator"
        ),
        None,
        45,
    ),
    (
        "COMPACT OPERATORS: LIMITS AND FINITE-RANK CRITERIA",
        re.compile(
            r"^\s*(?:@\[[^\]]*\]\s*)?"
            r"(?:theorem|lemma|def|abbrev)\s+.*"
            r"(?:[Cc]ompact|[Ff]inite[Rr]ank|finite_rank)"
        ),
        lambda p: (
            "Operator" in p.parts or
            "InnerProductSpace" in p.parts
        ),
        65,
    ),
    (
        "Lp PRODUCT APPROXIMATION AND DENSITY",
        re.compile(
            r"^\s*(?:theorem|lemma|def|abbrev)\s+.*"
            r"(?:[Dd]ense|[Tt]ensor|[Pp]rod|[Rr]ectangle)"
        ),
        lambda p: (
            "MeasureTheory" in p.parts and
            any(part in {"LpSpace", "SimpleFunc", "L2Space"}
                for part in p.parts + (p.stem,))
        ),
        45,
    ),
]

files = sorted(root.rglob("*.lean"))

for title, pattern, select, limit in groups:
    print("\n=== " + title + " ===")
    count = 0
    truncated = False
    for path in files:
        if select is not None and not select(path):
            continue
        lines = path.read_text(encoding="utf-8").splitlines()
        for index, line in enumerate(lines):
            if not pattern.search(line):
                continue
            if count >= limit:
                truncated = True
                break
            print(f"\n{path.as_posix()}:{index + 1}")
            stop = min(index + 7, len(lines))
            for context in lines[index:stop]:
                print(context)
            count += 1
        if truncated:
            break
    if count == 0:
        print("No matches.")
    if truncated:
        print(f"\nOutput limited to {limit} matches.")
PY

echo "PASS: Stage4HankelCompactApiAudit"
