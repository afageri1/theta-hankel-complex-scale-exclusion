#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelBasisExistenceAudit.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_basis_existence_audit.sh"),
]

old = '''/-- Check separability without admitting a missing instance. -/
run_cmd do
  let goal ← Lean.Elab.Term.elabType
    (← `(SeparableSpace HPThetaHankelSpace))
  let result ← Lean.Meta.synthInstance? goal
  match result with
  | some _ =>
      Lean.logInfo
        "FOUND: SeparableSpace HPThetaHankelSpace"
  | none =>
      Lean.logInfo
        "MISSING: automatic separability instance; an explicit proof is needed"'''

new = '''-- Probe instance availability; this proves only True.
example : True := by
  first
  | haveI : SeparableSpace HPThetaHankelSpace := inferInstance
    trace "FOUND: SeparableSpace HPThetaHankelSpace"
    exact True.intro
  | trace "MISSING: automatic separability instance; an explicit proof is needed"
    exact True.intro'''

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    count = text.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: expected one matching block in {path}; found {count}"
        )
    updated = text.replace(old, new)
    if b"\r\n" in raw:
        updated = updated.replace("\n", "\r\n")
    prepared.append((path, raw, updated.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, raw, updated in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    path.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_basis_existence_audit.sh
