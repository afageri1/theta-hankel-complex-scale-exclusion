#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaNormalizedXiObstruction

target="HodgeProofHP/Stage4ThetaHankelBasisExistenceAudit.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaNormalizedXiObstruction
import Mathlib

namespace HodgeProofHP

#check HPThetaHankelSpace
#check hpThetaHankelMeasure
#check HilbertBasis
#check hpThetaHankelBasisTrace
#check hpThetaHankelBasis_norm_sq_hasSum_energy

#synth CompleteSpace HPThetaHankelSpace
#synth InnerProductSpace ℂ HPThetaHankelSpace

-- Probe instance availability; this proves only True.
example : True := by
  first
  | haveI : SeparableSpace HPThetaHankelSpace := inferInstance
    trace "FOUND: SeparableSpace HPThetaHankelSpace"
    exact True.intro
  | trace "MISSING: automatic separability instance; an explicit proof is needed"
    exact True.intro

#print axioms hpThetaHankelBasis_norm_sq_hasSum_energy
#print axioms hpThetaHankel_function_ne_normalizedXi_of_trace_identity

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelBasisExistenceAudit

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib")
patterns = [
    ("Hilbert basis existence and countability",
     root / "Analysis/InnerProductSpace",
     re.compile(
         r"exists.*(?:[Hh]ilbert|[Oo]rthonormal)|"
         r"(?:[Hh]ilbert|[Oo]rthonormal).*exists|"
         r"(?:[Cc]ountable|[Ss]eparable|[Ii]s[Ss]eparable)")),

    ("Lp separability",
     root / "MeasureTheory",
     re.compile(
         r"SeparableSpace|IsSeparable|"
         r"CountablyGenerated|SecondCountableTopology")),
]

for title, directory, pattern in patterns:
    print("\n=== " + title + " ===")
    shown = 0
    for path in sorted(directory.rglob("*.lean")):
        if title == "Lp separability":
            if not any(part in str(path)
                       for part in ("LpSpace", "L2Space",
                                    "StronglyMeasurable",
                                    "Measure/Typeclasses")):
                continue
        lines = path.read_text(encoding="utf-8").splitlines()
        for index, line in enumerate(lines):
            if line.lstrip().startswith("--"):
                continue
            if pattern.search(line):
                print(f"{path.as_posix()}:{index + 1}")
                print("\n".join(lines[max(0, index - 1):index + 5]))
                shown += 1
                if shown >= 35:
                    break
        if shown >= 35:
            break
    if shown == 0:
        print("No matching excerpts in these directories.")

print("\n=== Project space definition ===")
project = Path("HodgeProofHP")
pattern = re.compile(
    r"(?:def|abbrev)\s+HPThetaHankelSpace|"
    r"SeparableSpace\s+HPThetaHankelSpace|"
    r"HilbertBasis.*HPThetaHankelSpace")
shown = 0
for path in sorted(project.glob("*.lean")):
    lines = path.read_text(encoding="utf-8").splitlines()
    for index, line in enumerate(lines):
        if pattern.search(line):
            print(f"{path.as_posix()}:{index + 1}")
            print("\n".join(lines[max(0, index - 1):index + 7]))
            shown += 1
            if shown >= 15:
                break
    if shown >= 15:
        break
PY

printf '%s\n' 'PASS: Stage4ThetaHankelBasisExistenceAudit'
