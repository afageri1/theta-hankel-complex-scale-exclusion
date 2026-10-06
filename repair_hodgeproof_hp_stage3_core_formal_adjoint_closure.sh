#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PY'
from pathlib import Path

replacements = {
    "(↑HPHarmonicCoreOperator x)": "(HPHarmonicCoreOperator.toFun x)",
    "(↑HPHarmonicCoreOperator.adjoint z)": "(HPHarmonicCoreOperator.adjoint.toFun z)",
    "(↑HPHarmonicClosure y)": "(HPHarmonicClosure.toFun y)",
}

for name in (
    "HodgeProofHP/Stage3CoreFormalAdjointClosure.lean",
    "create_hodgeproof_hp_stage3_core_formal_adjoint_closure.sh",
):
    path = Path(name)
    content = path.read_text(encoding="utf-8")
    for old, new in replacements.items():
        if old not in content:
            raise SystemExit(f"Expected expression missing in {name}: {old}")
        content = content.replace(old, new)
    path.write_text(content, encoding="utf-8")
    print(f"UPDATED: {name}")
PY

lake env lean HodgeProofHP/Stage3CoreFormalAdjointClosure.lean
lake build HodgeProofHP.Stage3CoreFormalAdjointClosure
