#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "ERROR: Run from the hodgeproof-hp project root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaHankelBoundedOperator

target="HodgeProofHP/Stage4HankelAdjointApiAudit.lean"

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp -p "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelBoundedOperator

/-!
Audit the established Hankel operator and product-space
integrability tools before proving the adjoint identity.
-/

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

#check hpThetaHankelOperator
#check hpThetaHankelOperator_coeFn_ae
#check hpThetaHankelKernel_hermitian
#check hpThetaHankelKernel_symmetric
#check hpThetaHankelKernel_memLp
#check hpThetaHankelSpace_norm_sq_eq_integral

#check MeasureTheory.L2.inner_def
#check MeasureTheory.L2.integrable_inner
#check MeasureTheory.MemLp.integrable_mul
#check MeasureTheory.memLp_two_iff_integrable_sq_norm
#check MeasureTheory.AEStronglyMeasurable.comp_fst
#check MeasureTheory.AEStronglyMeasurable.comp_snd

#print axioms hpThetaHankelOperator

end HodgeProofHP
LEAN

lake env lean "$target"

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib")
if not root.is_dir():
    raise SystemExit("STOP: mathlib source directory not found.")

searches = [
    (
        "PRODUCT INTEGRABILITY AND FUBINI",
        root / "MeasureTheory",
        re.compile(
            r"(?:theorem|lemma)\s+"
            r"(?:[A-Za-z0-9_'.]*"
            r"(?:prod_mul|integrable_prod_mul|integral_integral_swap|"
            r"integral_prod_mul|integral_inner|inner_integral)"
            r"[A-Za-z0-9_'.]*)\b"
        ),
    ),
    (
        "CONTINUOUS OPERATOR ADJOINT",
        root / "Analysis/InnerProductSpace",
        re.compile(
            r"(?:theorem|lemma)\s+"
            r"[A-Za-z0-9_'.]*"
            r"(?:adjoint_eq|eq_adjoint|isSelfAdjoint_iff|"
            r"inner_adjoint|adjoint_inner|isSymmetric_iff)"
            r"[A-Za-z0-9_'.]*\b"
        ),
    ),
]

for title, directory, pattern in searches:
    print("\n=== " + title + " ===")
    if not directory.is_dir():
        print("Directory not found:", directory)
        continue
    matches = 0
    for path in sorted(directory.rglob("*.lean")):
        lines = path.read_text(encoding="utf-8").splitlines()
        for index, line in enumerate(lines):
            if pattern.search(line):
                print(f"\n{path}:{index + 1}")
                print("\n".join(lines[index:index + 12]))
                matches += 1
    print("\nMATCHES:", matches)
PY

echo "PASS: Stage4HankelAdjointApiAudit"
