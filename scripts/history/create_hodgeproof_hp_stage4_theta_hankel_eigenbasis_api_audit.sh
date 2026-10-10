#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelPositiveEigenvalue

target="HodgeProofHP/Stage4ThetaHankelEigenbasisApiAudit.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelPositiveEigenvalue

/-!
API audit for constructing a Hilbert basis of eigenvectors.
This file records interfaces; it does not construct that basis.
-/

namespace HodgeProofHP

#check HilbertBasis
#check HilbertBasis.mkOfOrthogonalEqBot
#check HilbertBasis.coe_mkOfOrthogonalEqBot
#check OrthogonalFamily

#check hpThetaHankelAdjointSquare_eigenspaces_orthogonalFamily
#check hpThetaHankelAdjointSquare_eigenspaces_orthogonalComplement_eq_bot
#check hpThetaHankelAdjointSquare_eigenspace_finiteDimensional
#check hpThetaHankel_exists_hilbertBasis
#check hpThetaHankelAdjointSquare_exists_positive_eigenvector

#print axioms hpThetaHankelAdjointSquare_eigenspaces_orthogonalFamily
#print axioms hpThetaHankelAdjointSquare_eigenspaces_orthogonalComplement_eq_bot

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelEigenbasisApiAudit

python - <<'PY'
from pathlib import Path
import re
import subprocess

root = Path(".lake/packages/mathlib/Mathlib")
if not root.is_dir():
    raise SystemExit(f"STOP: missing mathlib source: {root}")

result = subprocess.run(
    ["rg", "--files", str(root / "Analysis" / "InnerProductSpace")],
    check=True, capture_output=True, text=True, encoding="utf-8"
)

stems = {"l2space", "orthonormal", "orthogonal", "subspace", "spectrum"}
pattern = re.compile(
    r"exists_hilbertBasis|mkOfOrthogonalEqBot|"
    r"orthonormal.*sigma|sigma.*orthonormal|"
    r"iSup.*span|span.*iSup|"
    r"orthogonalFamily.*orthonormal|orthonormal.*orthogonalFamily|"
    r"orthogonalFamily.*comp|orthonormal.*comp"
)
declaration = re.compile(
    r"^\s*(?:(?:noncomputable|protected|private)\s+)*"
    r"(?:theorem|lemma|def|instance)\s+"
)

count = 0
for name in sorted(result.stdout.splitlines()):
    path = Path(name)
    if path.stem.lower() not in stems:
        continue
    lines = path.read_text(encoding="utf-8").splitlines()
    matches = [
        i for i, line in enumerate(lines)
        if declaration.search(line) and pattern.search(line)
    ]
    if not matches:
        continue
    print(f"\nSOURCE: {path}")
    scopes = [
        line for line in lines
        if re.match(r"^\s*(namespace|section)\b", line)
    ]
    print("SCOPES: " + " | ".join(scopes))
    for i in matches[:8]:
        print(f"\nDeclaration at line {i + 1}:")
        print("\n".join(lines[i:i + 14]))
        count += 1

print(f"\nMatched declaration excerpts: {count}")
PY

printf '%s\n' 'PASS: Stage4ThetaHankelEigenbasisApiAudit'
