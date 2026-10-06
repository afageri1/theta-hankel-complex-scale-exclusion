#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelChosenDiagonalAbsolute

target="HodgeProofHP/Stage4ThetaHankelCompactApiAudit.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelChosenDiagonalAbsolute

/-!
Audit the established summability input for finite-rank approximation.
Compactness is not asserted in this module.
-/

namespace HodgeProofHP

example :
    Summable
      (fun i : hpThetaHankelBasisSet =>
        ‖hpThetaHankelOperator
          (hpThetaHankelHilbertBasis i)‖ ^ 2) :=
  hpThetaHankelChosenBasis_norm_sq_hasSum_energy.summable

#check hpThetaHankelOperator
#check hpThetaHankelHilbertBasis
#check hpThetaHankelBasisSet_countable
#check hpThetaHankelChosenBasis_norm_sq_hasSum_energy
#check hpThetaHankelChosenDiagonal_norm_summable

#print axioms hpThetaHankelChosenBasis_norm_sq_hasSum_energy
#print axioms hpThetaHankelChosenDiagonal_norm_summable

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelCompactApiAudit

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib")
folders = [
    root / "Analysis/Normed/Operator",
    root / "Analysis/InnerProductSpace",
]

decl = re.compile(
    r"^\s*(?:(?:protected|private|noncomputable)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\b",
    re.MULTILINE,
)

print("\n=== Compactness and finite-rank approximation API ===")
count = 0

for folder in folders:
    for path in sorted(folder.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        starts = list(decl.finditer(text))
        for j, item in enumerate(starts):
            end = starts[j + 1].start() if j + 1 < len(starts) else len(text)
            block = text[item.start():end]
            header = block.split(":=", 1)[0]
            low = header.lower()

            compact = "iscompactoperator" in low
            approximation = any(word in low for word in (
                "rankone", "rank_one", "smulright",
                "hassum_repr", "sum_repr", "has_sum_repr",
            ))
            finite_range = (
                ("finitedimensional" in low or "finite_dimensional" in low)
                and ("range" in low or "compact" in low)
            )

            if not (compact or approximation or finite_range):
                continue

            line = text.count("\n", 0, item.start()) + 1
            print(f"\n{path.as_posix()}:{line}")
            print("\n".join(block.strip().splitlines()[:28]))
            count += 1

print(f"\nMatched declarations: {count}")
PY

printf '%s\n' 'PASS: Stage4ThetaHankelCompactApiAudit'
