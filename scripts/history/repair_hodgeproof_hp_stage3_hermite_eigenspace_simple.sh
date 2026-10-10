#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage3HermiteEigenspaceSimple.lean"),
    Path("create_hodgeproof_hp_stage3_hermite_eigenspace_simple.sh"),
]

replacements = [
    (
        """  have hnm : (n : ℝ) = (m : ℝ) := by
    linarith
  exact_mod_cast hnm""",
        """  exact hr""",
    ),
    (
        """    simp only [hpHermiteCoefficient, inner_smul_right,
      hinner, if_pos rfl, mul_one]""",
        """    have hself :
        inner ℂ (hpHermiteNormalizedL2 n)
          (hpHermiteNormalizedL2 n) = 1 := by
      simpa using hinner
    simp [hpHermiteCoefficient, inner_smul_right, hself]""",
    ),
    (
        """    simpa only [hpHermiteCoefficient, inner_smul_right,
      hinner, if_neg hmn, mul_zero] using hzero""",
        """    have hoff :
        inner ℂ (hpHermiteNormalizedL2 m)
          (hpHermiteNormalizedL2 n) = 0 := by
      simpa [hmn] using hinner
    simpa only [hpHermiteCoefficient, inner_smul_right,
      hoff, mul_zero] using hzero""",
    ),
]

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    original = path.read_text(encoding="utf-8")
    updated = original
    for old, new in replacements:
        count = updated.count(old)
        if count != 1:
            raise SystemExit(
                f"STOP: expected one matching block in {path}; found {count}"
            )
        updated = updated.replace(old, new, 1)
    prepared.append((path, original, updated))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, updated in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_text(original, encoding="utf-8")
    path.write_text(updated, encoding="utf-8")
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash ./create_hodgeproof_hp_stage3_hermite_eigenspace_simple.sh
