#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path

targets = [
    Path("HodgeProofHP/Stage3HermitePolynomialSpan.lean"),
    Path("create_hodgeproof_hp_stage3_hermite_polynomial_span.sh"),
]

old = """      map_smul' := by
        intro c q
        rw [← hpPolynomial_C_mul_eq_smul c q,
          ← hpPolynomial_C_mul_eq_smul c (Polynomial.X * q)]
        ring }"""

new = """      map_smul' := by
        intro c q
        change Polynomial.X * (c • q) =
          c • (Polynomial.X * q)
        rw [← hpPolynomial_C_mul_eq_smul c q,
          ← hpPolynomial_C_mul_eq_smul c (Polynomial.X * q)]
        ring }"""

for path in targets:
    text = path.read_text(encoding="utf-8")
    if new in text:
        print(f"Already repaired: {path}")
        continue
    if text.count(old) != 1:
        raise SystemExit(f"STOP: expected exactly one matching block in {path}")
    backup = Path(str(path) + ".before_scalar_identity_fix")
    if not backup.exists():
        backup.write_text(text, encoding="utf-8")
    path.write_text(text.replace(old, new, 1), encoding="utf-8")
    print(f"Repaired: {path}")
PY

lake env lean HodgeProofHP/Stage3HermitePolynomialSpan.lean
lake build HodgeProofHP.Stage3HermitePolynomialSpan
