#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaNormalizedXiObstruction

target="HodgeProofHP/Stage4ThetaHankelHilbertBasis.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaNormalizedXiObstruction
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
An actual Hilbert basis for the Hankel space.

The index set is not yet proved countable.
No separability assumption is introduced.
-/

namespace HodgeProofHP

theorem hpThetaHankel_exists_hilbertBasis :
    ∃ (w : Set HPThetaHankelSpace)
      (b : HilbertBasis w ℂ HPThetaHankelSpace),
      ⇑b = ((↑) : w → HPThetaHankelSpace) := by
  exact exists_hilbertBasis ℂ HPThetaHankelSpace

noncomputable def hpThetaHankelBasisSet :
    Set HPThetaHankelSpace :=
  hpThetaHankel_exists_hilbertBasis.choose

noncomputable def hpThetaHankelHilbertBasis :
    HilbertBasis hpThetaHankelBasisSet ℂ HPThetaHankelSpace :=
  hpThetaHankel_exists_hilbertBasis.choose_spec.choose

theorem hpThetaHankelHilbertBasis_coe :
    ⇑hpThetaHankelHilbertBasis =
      ((↑) : hpThetaHankelBasisSet → HPThetaHankelSpace) := by
  exact hpThetaHankel_exists_hilbertBasis.choose_spec.choose_spec

theorem hpThetaHankelHilbertBasis_orthonormal :
    Orthonormal ℂ
      (hpThetaHankelHilbertBasis :
        hpThetaHankelBasisSet → HPThetaHankelSpace) := by
  exact hpThetaHankelHilbertBasis.orthonormal

#print axioms hpThetaHankel_exists_hilbertBasis
#print axioms hpThetaHankelHilbertBasis
#print axioms hpThetaHankelHilbertBasis_coe
#print axioms hpThetaHankelHilbertBasis_orthonormal

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelHilbertBasis

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib")

print("\n=== Lp separability: source search ===")
found = 0
for path in sorted((root / "MeasureTheory").rglob("*.lean")):
    lines = path.read_text(encoding="utf-8").splitlines()
    for i, line in enumerate(lines):
        if not re.search(r"SeparableSpace|[Ss]eparable", line):
            continue
        context = "\n".join(lines[max(0, i-8):i+12])
        if not (
            "Lp" in context or "lp " in context
            or "LpSpace" in str(path)
            or "L2Space" in str(path)
        ):
            continue
        print(f"\n{path.as_posix()}:{i+1}")
        print(context)
        found += 1
        if found >= 25:
            break
    if found >= 25:
        break
if found == 0:
    print("No matching Lp separability excerpts found.")

print("\n=== Countability of orthonormal families ===")
found = 0
for path in sorted((root / "Analysis").rglob("*.lean")):
    lines = path.read_text(encoding="utf-8").splitlines()
    if not any("Orthonormal" in line or "HilbertBasis" in line
               for line in lines):
        continue
    for i, line in enumerate(lines):
        if not re.search(
            r"Countable|countable|SeparableSpace|SecondCountableTopology",
            line
        ):
            continue
        context = "\n".join(lines[max(0, i-6):i+12])
        if "Orthonormal" not in context and "HilbertBasis" not in context:
            continue
        print(f"\n{path.as_posix()}:{i+1}")
        print(context)
        found += 1
        if found >= 25:
            break
    if found >= 25:
        break
if found == 0:
    print("No matching countability excerpts found.")
PY

printf '%s\n' 'PASS: Stage4ThetaHankelHilbertBasis'
