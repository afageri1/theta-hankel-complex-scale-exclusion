#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PY'
from pathlib import Path

old = """    simpa only [hf] using
      (hpHarmonicCoreOperator_isFormalAdjoint f f)"""
new = """    have hformal := hpHarmonicCoreOperator_isFormalAdjoint f f
    change
      inner ℂ (HPHarmonicCoreOperator.toFun f) (f : HPSpace) =
        inner ℂ (f : HPSpace) (HPHarmonicCoreOperator.toFun f) at hformal
    rw [hf] at hformal
    exact hformal"""

for name in (
    "HodgeProofHP/Stage3CoreNoNonrealEigen.lean",
    "create_hodgeproof_hp_stage3_core_no_nonreal_eigen.sh",
):
    path = Path(name)
    content = path.read_text(encoding="utf-8")
    if content.count(old) != 1:
        raise SystemExit(f"Expected exactly one proof block in {name}; found {content.count(old)}")
    path.write_text(content.replace(old, new), encoding="utf-8")
    print(f"UPDATED: {name}")
PY

lake env lean HodgeProofHP/Stage3CoreNoNonrealEigen.lean
lake build HodgeProofHP.Stage3CoreNoNonrealEigen
