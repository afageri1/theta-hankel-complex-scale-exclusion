#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage3ClosureImaginaryShiftBound.lean"),
    Path("create_hodgeproof_hp_stage3_closure_imaginary_shift_bound.sh"),
]

replacements = [
    (
        "  rw [← hA, hz] at hform",
        "  rw [← hA, ← hz] at hform",
    ),
    (
        """    rw [inner_smul_right]
    simp [Complex.mul_re, hsRe, him]""",
        """    rw [inner_smul_right]
    change
      s.re * (inner ℂ (HPHarmonicClosure.toFun x) (x : HPSpace)).re -
        s.im * (inner ℂ (HPHarmonicClosure.toFun x) (x : HPSpace)).im = 0
    rw [hsRe, him]
    simp""",
    ),
]

pending = []
for path in paths:
    original = path.read_text(encoding="utf-8")
    updated = original
    for old, new in replacements:
        if updated.count(old) != 1:
            raise SystemExit(f"STOP: expected exactly one matching block in {path}")
        updated = updated.replace(old, new, 1)
    pending.append((path, original, updated))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, updated in pending:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_text(original, encoding="utf-8")
    path.write_text(updated, encoding="utf-8")
    print(f"Repaired: {path}")
    print(f"Backup: {backup}")
PY

bash ./create_hodgeproof_hp_stage3_closure_imaginary_shift_bound.sh
