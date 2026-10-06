#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelTailEnergy

target="HodgeProofHP/Stage4ThetaHankelRemainderApiAudit.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelTailEnergy

/-!
Audit of the established inputs for the operator norm remainder estimate.
No remainder estimate is asserted in this module.
-/

namespace HodgeProofHP

#check hpThetaHankelHilbertBasis
#check hpThetaHankelHilbertBasis_orthonormal
#check hpThetaHankelFiniteApproximation_apply
#check hpThetaHankelFiniteApproximation_eq_comp
#check hpThetaHankelFiniteApproximation_isCompact
#check hpThetaHankelChosenBasis_norm_sq_hasSum_energy
#check hpThetaHankelTailEnergy_tendsto_zero

#print axioms hpThetaHankelFiniteApproximation_isCompact
#print axioms hpThetaHankelTailEnergy_tendsto_zero

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelRemainderApiAudit

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib")
if not root.is_dir():
    raise SystemExit("STOP: mathlib source directory not found")

groups = [
    ("Hilbert basis expansion",
     r"hasSum_repr|sum_repr|hasSum_inner|sum_inner_mul"),
    ("Finite Cauchy-Schwarz and Bessel",
     r"sum_mul_sq_le|sum_sq_le|sum_norm_sq|sum_inner.*le"),
    ("Norms of sums",
     r"norm_sum_le|norm_tsum_le"),
    ("Summable tails",
     r"sum_le_tsum|sum_add_tsum|tsum_subtype.*add|tsum.*compl"),
    ("Operator norm bounds",
     r"opNorm_le_bound|opNorm_le_of|norm_le_of.*bound"),
]

folders = [
    root / "Analysis/InnerProductSpace",
    root / "Analysis/Normed",
    root / "Topology/Algebra/InfiniteSum",
    root / "Algebra/Order/BigOperators",
]

files = sorted({
    path
    for folder in folders if folder.is_dir()
    for path in folder.rglob("*.lean")
})

declaration = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:protected|private|noncomputable)\s+)*"
    r"(?:theorem|lemma|def)\s+([^\s({:]+)"
)

sources = []
for path in files:
    lines = path.read_text(encoding="utf-8").splitlines()
    sources.append((path, lines))

for title, pattern in groups:
    print(f"\n=== {title} ===")
    matcher = re.compile(pattern)
    found = 0
    for path, lines in sources:
        for index, line in enumerate(lines):
            match = declaration.match(line)
            if not match or not matcher.search(match.group(1)):
                continue
            print(f"\n{path.as_posix()}:{index + 1}")
            print("\n".join(lines[index:index + 20]))
            found += 1
            if found >= 8:
                break
        if found >= 8:
            break
    if found == 0:
        print("NO MATCH: inspect additional source files if needed")
PY

printf '%s\n' 'PASS: Stage4ThetaHankelRemainderApiAudit'
