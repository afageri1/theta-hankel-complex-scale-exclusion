#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PY'
from pathlib import Path

old = """    _ = inner ℂ (x : HPSpace) (HPHarmonicClosure.toFun y) := by rw [hA]"""
new = """    _ = inner ℂ (x : HPSpace) (HPHarmonicClosure.toFun y) := by
      change HPHarmonicClosure.toFun y =
        HPHarmonicCoreOperator.adjoint.toFun z at hA
      rw [hA]"""

for name in (
    "HodgeProofHP/Stage3CoreFormalAdjointClosure.lean",
    "create_hodgeproof_hp_stage3_core_formal_adjoint_closure.sh",
):
    path = Path(name)
    content = path.read_text(encoding="utf-8")
    if content.count(old) != 1:
        raise SystemExit(f"Expected exactly one target line in {name}; found {content.count(old)}")
    path.write_text(content.replace(old, new), encoding="utf-8")
    print(f"UPDATED: {name}")
PY

lake env lean HodgeProofHP/Stage3CoreFormalAdjointClosure.lean
lake build HodgeProofHP.Stage3CoreFormalAdjointClosure
