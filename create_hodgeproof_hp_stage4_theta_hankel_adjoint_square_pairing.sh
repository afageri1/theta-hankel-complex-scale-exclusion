#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelAdjointSquare

target="HodgeProofHP/Stage4ThetaHankelAdjointSquarePairing.lean"
if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelAdjointSquare

/-!
The quadratic form of A* A is the squared norm of A f.
These identities precede the infinite basis sum and trace construction.
-/

namespace HodgeProofHP

theorem hpThetaHankelAdjointSquare_inner
    (f : HPThetaHankelSpace) :
    inner ℂ f (hpThetaHankelAdjointSquare f) =
      (‖hpThetaHankelOperator f‖ ^ 2 : ℝ) := by
  rw [hpThetaHankelAdjointSquare_apply,
    ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  simp only [Complex.ofReal_pow] <;> rfl

theorem hpThetaHankelAdjointSquare_inner_re
    (f : HPThetaHankelSpace) :
    (inner ℂ f (hpThetaHankelAdjointSquare f)).re =
      ‖hpThetaHankelOperator f‖ ^ 2 := by
  rw [hpThetaHankelAdjointSquare_inner]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

theorem hpThetaHankelAdjointSquare_inner_im
    (f : HPThetaHankelSpace) :
    (inner ℂ f (hpThetaHankelAdjointSquare f)).im = 0 := by
  rw [hpThetaHankelAdjointSquare_inner]
  simp only [← Complex.ofReal_pow, Complex.ofReal_im]

theorem hpThetaHankelAdjointSquare_inner_re_nonneg
    (f : HPThetaHankelSpace) :
    0 ≤ (inner ℂ f (hpThetaHankelAdjointSquare f)).re := by
  rw [hpThetaHankelAdjointSquare_inner_re]
  exact sq_nonneg _

theorem hpThetaHankelAdjointSquare_diagonal_finset
    {ι : Type*} (v : ι → HPThetaHankelSpace) (s : Finset ι) :
    (∑ i ∈ s, (inner ℂ (v i)
      (hpThetaHankelAdjointSquare (v i))).re) =
    ∑ i ∈ s, ‖hpThetaHankelOperator (v i)‖ ^ 2 := by
  simp only [hpThetaHankelAdjointSquare_inner_re]

#print axioms hpThetaHankelAdjointSquare_inner
#print axioms hpThetaHankelAdjointSquare_inner_re
#print axioms hpThetaHankelAdjointSquare_inner_im
#print axioms hpThetaHankelAdjointSquare_inner_re_nonneg
#print axioms hpThetaHankelAdjointSquare_diagonal_finset

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelAdjointSquarePairing

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib/Analysis")
if not root.is_dir():
    raise SystemExit(f"STOP: missing {root}")

declaration = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma|def|abbrev)\s+"
)
wanted = re.compile(
    r"tsum|hasSum|summable|norm|inner|repr|exists",
    re.IGNORECASE,
)

print("\n=== HilbertBasis / Parseval source declarations ===")
count = 0
for path in sorted(root.rglob("*.lean")):
    text = path.read_text(encoding="utf-8")
    if "HilbertBasis" not in text:
        continue
    print(f"\nFILE: {path}")
    lines = text.splitlines()
    for i, line in enumerate(lines):
        if declaration.match(line) and wanted.search(line):
            print(f"\n{path}:{i + 1}")
            print("\n".join(lines[i:i + 7]))
            count += 1

print(f"\nMatched declaration excerpts: {count}")
PY

printf '%s\n' 'PASS: Stage4ThetaHankelAdjointSquarePairing'
