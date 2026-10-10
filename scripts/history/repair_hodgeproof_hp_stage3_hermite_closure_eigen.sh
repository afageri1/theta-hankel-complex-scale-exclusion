#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage3HermiteClosureEigen.lean"),
    Path("create_hodgeproof_hp_stage3_hermite_closure_eigen.sh"),
]

replacements = [
    (
        """theorem hpHermiteL2_mem_closure_domain (n : ℕ) :
    hpHermiteL2 n ∈ HPHarmonicClosure.domain :=
  (LinearPMap.domain_mono hpHarmonicCoreOperator_le_closure)
    (hpHermiteL2_mem_domain n)""",
        """theorem hpHermiteL2_mem_closure_domain (n : ℕ) :
    hpHermiteL2 n ∈ HPHarmonicClosure.domain := by
  obtain ⟨x, hx, _⟩ :=
    LinearPMap.exists_of_le hpHarmonicCoreOperator_le_closure
      (hpHermiteCoreVector n)
  change hpHermiteL2 n = (x : HPSpace) at hx
  rw [hx]
  exact x.property""",
    ),
    (
        """  have hstar :
      (starRingEnd ℂ) (2 * (n : ℂ) + 1) =
        2 * (n : ℂ) + 1 := by
    simp""",
        """  have hstar :
      (starRingEnd ℂ) (2 * (n : ℂ) + 1) =
        2 * (n : ℂ) + 1 := by
    apply Complex.ext
    · rfl
    · change
        -(2 * (n : ℂ) + 1).im =
          (2 * (n : ℂ) + 1).im
      norm_num [Complex.mul_im]""",
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

bash ./create_hodgeproof_hp_stage3_hermite_closure_eigen.sh
