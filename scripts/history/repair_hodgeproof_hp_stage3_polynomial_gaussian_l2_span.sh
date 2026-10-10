#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path

targets = [
    Path("HodgeProofHP/Stage3PolynomialGaussianL2Span.lean"),
    Path("create_hodgeproof_hp_stage3_polynomial_gaussian_l2_span.sh"),
]

old = "  simpa only [heq] using hg"
new = """  change g ∈ hpHermiteSchwartzSpan at hg
  rw [← heq]
  exact hg"""

for path in targets:
    text = path.read_text(encoding="utf-8")
    if new in text:
        print(f"Already repaired: {path}")
        continue
    if text.count(old) != 1:
        raise SystemExit(f"STOP: expected exactly one matching line in {path}")
    backup = Path(str(path) + ".before_membership_fix")
    if not backup.exists():
        backup.write_text(text, encoding="utf-8")
    path.write_text(text.replace(old, new, 1), encoding="utf-8")
    print(f"Repaired: {path}")
PY

lake env lean HodgeProofHP/Stage3PolynomialGaussianL2Span.lean
lake build HodgeProofHP.Stage3PolynomialGaussianL2Span
