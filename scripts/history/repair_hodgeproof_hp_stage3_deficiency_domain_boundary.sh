#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PY'
from pathlib import Path

old = """  have hg : HPHarmonicClosure.toFun g = c • (g : HPSpace) := by
    rw [hA, hf]
    rfl"""
new = """  have hg : HPHarmonicClosure.toFun g = c • (g : HPSpace) := by
    rw [hA, hf]"""

for name in (
    "HodgeProofHP/Stage3DeficiencyDomainBoundary.lean",
    "create_hodgeproof_hp_stage3_deficiency_domain_boundary.sh",
):
    path = Path(name)
    content = path.read_text(encoding="utf-8")
    if content.count(old) != 1:
        raise SystemExit(f"Expected exactly one proof block in {name}; found {content.count(old)}")
    path.write_text(content.replace(old, new), encoding="utf-8")
    print(f"UPDATED: {name}")
PY

lake env lean HodgeProofHP/Stage3DeficiencyDomainBoundary.lean
lake build HodgeProofHP.Stage3DeficiencyDomainBoundary
