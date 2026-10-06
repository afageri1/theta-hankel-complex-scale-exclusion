#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4RiemannXiExponentialSimplified.lean"),
    Path("create_hodgeproof_hp_stage4_riemann_xi_exponential_simplified.sh"),
]

start = """  simp only [Complex.real_smul, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  calc
"""
end = "/-- Simplified exponential theta integrand. -/"

replacement = """  simp only [Complex.real_smul, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_ofNat] at hsum ⊢
  rw [← hsum]
  ring

"""

pending = []
for path in paths:
    original = path.read_bytes()
    text = original.decode("utf-8")
    if text.count(start) != 1 or text.count(end) != 1:
        raise SystemExit(f"STOP: unexpected proof structure in {path}")
    first = text.index(start)
    last = text.index(end)
    if last <= first:
        raise SystemExit(f"STOP: invalid replacement boundaries in {path}")
    updated = text[:first] + replacement + text[last:]
    pending.append((path, original, updated.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, updated in pending:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(original)
    print(f"BACKUP: {backup}")

for path, original, updated in pending:
    path.write_bytes(updated)
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_riemann_xi_exponential_simplified.sh
