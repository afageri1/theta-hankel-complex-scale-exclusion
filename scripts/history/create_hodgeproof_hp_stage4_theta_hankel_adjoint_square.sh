#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelTraceApiAudit

target="HodgeProofHP/Stage4ThetaHankelAdjointSquare.lean"
if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelTraceApiAudit

/-!
The adjoint square of the established theta Hankel operator.
Its trace-class property and trace-energy identity remain separate goals.
-/

namespace HodgeProofHP

/-- The bounded operator A* A associated with the theta Hankel operator. -/
noncomputable def hpThetaHankelAdjointSquare :
    HPThetaHankelSpace →L[ℂ] HPThetaHankelSpace :=
  hpThetaHankelOperator.adjoint.comp hpThetaHankelOperator

theorem hpThetaHankelAdjointSquare_apply
    (f : HPThetaHankelSpace) :
    hpThetaHankelAdjointSquare f =
      hpThetaHankelOperator.adjoint (hpThetaHankelOperator f) := by
  rfl

#check hpThetaHankelAdjointSquare
#print axioms hpThetaHankelAdjointSquare
#print axioms hpThetaHankelAdjointSquare_apply

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelAdjointSquare

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib")
trace = root / "Analysis/InnerProductSpace/Trace.lean"

print("\n=== Exact source: InnerProductSpace/Trace.lean ===")
if not trace.is_file():
    raise SystemExit(f"STOP: missing {trace}")
for number, line in enumerate(
    trace.read_text(encoding="utf-8").splitlines(), 1
):
    print(f"{number}: {line}")

groups = [
    (
        "Hilbert basis and Parseval",
        root / "Analysis/InnerProductSpace",
        re.compile(
            r"(?:tsum|hasSum|summable|sum).*(?:norm|inner|repr)"
            r"|(?:norm|inner|repr).*(?:tsum|hasSum|summable)"
            r"|exists.*[Hh]ilbert[Bb]asis"
            r"|[Hh]ilbert[Bb]asis.*exists",
            re.IGNORECASE,
        ),
        lambda p: "Basis" in p.name or "Orthonormal" in p.name,
    ),
    (
        "Adjoint pairing",
        root / "Analysis/InnerProductSpace",
        re.compile(r"adjoint_inner|inner_adjoint"),
        lambda p: "Adjoint" in p.name,
    ),
    (
        "Tonelli for infinite sums",
        root / "MeasureTheory",
        re.compile(r"lintegral_tsum|tsum_lintegral"),
        lambda p: True,
    ),
]

declaration = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma|def|abbrev)\s+"
)

for title, directory, pattern, file_filter in groups:
    print(f"\n=== {title} ===")
    count = 0
    for path in sorted(directory.rglob("*.lean")):
        if not file_filter(path):
            continue
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            if declaration.match(line) and pattern.search(line):
                print(f"\n{path}:{i + 1}")
                print("\n".join(lines[i:i + 8]))
                count += 1
    print(f"\nMatched declarations: {count}")
PY

printf '%s\n' 'PASS: Stage4ThetaHankelAdjointSquare'
