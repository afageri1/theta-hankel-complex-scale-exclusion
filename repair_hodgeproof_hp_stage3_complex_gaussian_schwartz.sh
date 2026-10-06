#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PY'
from pathlib import Path

files = [
    Path("HodgeProofHP/Stage3ComplexGaussianSchwartz.lean"),
    Path("create_hodgeproof_hp_stage3_complex_gaussian_schwartz.sh"),
]

old = "    simp [hpComplexGaussianSchwartz, hpRealGaussianSchwartz]"
new = """    simp only [hpComplexGaussianSchwartz, SchwartzMap.postcompCLM_apply]
    rfl"""

for path in files:
    content = path.read_text(encoding="utf-8")
    if content.count(old) != 1:
        raise SystemExit(f"STOP: expected exactly one occurrence in {path}")
    path.write_text(content.replace(old, new), encoding="utf-8")
    print(f"UPDATED: {path}")
PY

lake env lean HodgeProofHP/Stage3ComplexGaussianSchwartz.lean
lake build HodgeProofHP.Stage3ComplexGaussianSchwartz
