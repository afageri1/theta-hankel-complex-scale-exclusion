#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelAdjointSquareKernel

target="HodgeProofHP/Stage4ThetaHankelSpectralApiAudit.lean"

if [ -f "$target" ]; then
  backup="$target.before_update_$(date +%Y%m%d_%H%M%S)"
  cp -p "$target" "$backup"
  printf 'BACKUP: %s\n' "$backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelAdjointSquareKernel

/-!
Audit of the verified theta Hankel operator frontier.
The accompanying script examines the installed spectral API.
-/

namespace HodgeProofHP

#check HPThetaHankelSpace
#check hpThetaHankelOperator
#check hpThetaHankelOperator_isCompact
#check hpThetaHankelOperator_isSelfAdjoint

#check hpThetaHankelAdjointSquare
#check hpThetaHankelAdjointSquare_isCompact
#check hpThetaHankelAdjointSquare_isSelfAdjoint
#check hpThetaHankelAdjointSquare_isSymmetric

#check hpThetaHankelAdjointSquare_eigenvalue_real_nonneg
#check hpThetaHankelAdjointSquare_apply_eq_zero_iff
#check hpThetaHankelAdjointSquare_eigenvalue_energy_quotient

#print axioms hpThetaHankelAdjointSquare_isCompact
#print axioms hpThetaHankelAdjointSquare_isSelfAdjoint
#print axioms hpThetaHankelAdjointSquare_eigenvalue_real_nonneg

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelSpectralApiAudit

python - <<'PY'
from pathlib import Path
import re
import subprocess

root = Path(".lake/packages/mathlib/Mathlib")
if not root.is_dir():
    raise SystemExit(f"STOP: mathlib source directory missing: {root}")

result = subprocess.run(
    ["rg", "--files", str(root / "Analysis")],
    capture_output=True, text=True, check=True, encoding="utf-8"
)
files = sorted(Path(p) for p in result.stdout.splitlines())

selected = [
    p for p in files
    if (
        "InnerProductSpace" in p.parts
        and any(word in p.stem for word in (
            "Spectrum", "Spectral", "Rayleigh", "Eigen"
        ))
    ) or (
        "Operator" in p.parts
        and "Compact" in p.parts
        and "Fredholm" in p.stem
    )
]

print("\n=== Installed spectral source files ===")
for path in selected:
    print(path.as_posix())

declaration = re.compile(
    r"^\s*(?:(?:protected|private|noncomputable)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure)\s+"
)
keywords = re.compile(
    r"compact|eigen|spectr|orthonormal|hilbertBasis|diagonal|rayleigh",
    re.IGNORECASE
)

print("\n=== Relevant declaration signatures ===")
count = 0
for path in selected:
    lines = path.read_text(encoding="utf-8").splitlines()
    namespaces = [
        line.strip() for line in lines
        if line.strip().startswith("namespace ")
    ]
    print(f"\nFILE: {path.as_posix()}")
    if namespaces:
        print("NAMESPACES:", " | ".join(namespaces))
    for index, line in enumerate(lines):
        if not declaration.match(line):
            continue
        block = []
        for next_line in lines[index:index + 24]:
            block.append(next_line)
            if ":=" in next_line or next_line.rstrip().endswith("where"):
                break
        signature = "\n".join(block).split(":=", 1)[0].rstrip()
        if keywords.search(signature):
            print(f"\nLINE {index + 1}:\n{signature}")
            count += 1

print(f"\nMatched declarations: {count}")
if not selected:
    raise SystemExit("STOP: no matching spectral source files found")
PY

printf '%s\n' 'PASS: Stage4ThetaHankelSpectralApiAudit'
