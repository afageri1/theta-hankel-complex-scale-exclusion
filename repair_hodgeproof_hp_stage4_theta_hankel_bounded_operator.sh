#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelBoundedOperator.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_bounded_operator.sh"),
]

old = """        exact Filter.Eventually.of_forall (fun x => by
          rw [inner_self_eq_norm_sq_to_K]
          simp only [Complex.ofReal_pow] <;> rfl)"""

new = """        exact Filter.Eventually.of_forall (fun x => by
          change inner ℂ (f x) (f x) =
            ((‖f x‖ ^ 2 : ℝ) : ℂ)
          rw [inner_self_eq_norm_sq_to_K]
          simp only [Complex.ofReal_pow] <;> rfl)"""

prepared = []
for path in paths:
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    count = text.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: {path}: expected one match, found {count}"
        )
    prepared.append((path, raw, text.replace(old, new, 1)))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, raw, text in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    print("BACKUP:", backup)

for path, raw, text in prepared:
    if b"\r\n" in raw:
        text = text.replace("\n", "\r\n")
    path.write_bytes(text.encode("utf-8"))
    print("REPAIRED:", path)
PY

lake env lean HodgeProofHP/Stage4ThetaHankelBoundedOperator.lean
lake build HodgeProofHP.Stage4ThetaHankelBoundedOperator
echo "PASS: Stage4ThetaHankelBoundedOperator"
