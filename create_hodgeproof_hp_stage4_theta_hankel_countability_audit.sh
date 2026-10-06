#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSeparability

target="HodgeProofHP/Stage4ThetaHankelCountabilityAudit.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSeparability

/-!
Check the hypotheses needed to obtain a countable Hilbert basis.
Countability itself is not asserted in this audit.
-/

namespace HodgeProofHP

example :
    SecondCountableTopology HPThetaHankelSpace := by
  infer_instance

example :
    TopologicalSpace.SeparableSpace HPThetaHankelSpace := by
  infer_instance

example :
    Orthonormal ℂ
      (hpThetaHankelHilbertBasis :
        hpThetaHankelBasisSet → HPThetaHankelSpace) :=
  hpThetaHankelHilbertBasis_orthonormal

#check hpThetaHankelBasisSet
#check hpThetaHankelHilbertBasis
#check hpThetaHankelHilbertBasis_coe

#print axioms hpThetaHankelHilbertBasis_orthonormal

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelCountabilityAudit

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib")
folders = [
    root / "Topology",
    root / "Analysis/InnerProductSpace",
]

declaration = re.compile(
    r"^\s*(?:(?:protected|private|noncomputable)\s+)*"
    r"(?:theorem|lemma|instance|def|abbrev)\b",
    re.MULTILINE,
)

matches = []
for folder in folders:
    for path in sorted(folder.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        starts = list(declaration.finditer(text))
        for i, item in enumerate(starts):
            end = starts[i + 1].start() if i + 1 < len(starts) else len(text)
            block = text[item.start():end]
            header = block.split(":= ", 1)[0].split(":=\n", 1)[0]
            low = header.lower()
            if (
                "countable" in low
                and any(word in low for word in (
                    "separat", "orthonormal", "discrete",
                    "secondcountable", "hilbertbasis"
                ))
            ):
                line = text.count("\n", 0, item.start()) + 1
                matches.append((path, line, block))

print("\n=== Countability declarations in installed mathlib ===")
for path, line, block in matches:
    print(f"\n{path.as_posix()}:{line}")
    print("\n".join(block.strip().splitlines()[:24]))

print(f"\nMatched declarations: {len(matches)}")
PY

printf '%s\n' 'PASS: Stage4ThetaHankelCountabilityAudit'
