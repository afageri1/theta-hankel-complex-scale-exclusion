#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "STOP: run from the hodgeproof-hp project root."
  exit 1
fi

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelSquareIdentity.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_square_identity.sh"),
]

old = """      rw [hsupport]
      exact lintegral_indicator measurableSet_Ioi _
"""

new = """      calc
        (∫⁻ u : ℝ, ENNReal.ofReal u * F u) =
            ∫⁻ u : ℝ,
              (Set.Ioi (0 : ℝ)).indicator
                (fun u : ℝ => ENNReal.ofReal u * F u) u := by
          exact congrArg
            (fun f : ℝ → ℝ≥0∞ => ∫⁻ u : ℝ, f u)
            hsupport
        _ = ∫⁻ u in Set.Ioi (0 : ℝ),
              ENNReal.ofReal u * F u :=
          lintegral_indicator
            (μ := (volume : Measure ℝ))
            (s := Set.Ioi (0 : ℝ))
            measurableSet_Ioi
            (fun u : ℝ => ENNReal.ofReal u * F u)
"""

changes = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    count = text.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: expected one match in {path}, found {count}"
        )
    updated = text.replace(old, new, 1)
    if b"\r\n" in raw:
        updated = updated.replace("\n", "\r\n")
    changes.append((path, updated.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, _ in changes:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    shutil.copy2(path, backup)
    print(f"BACKUP: {backup}")

for path, content in changes:
    path.write_bytes(content)
    print(f"REPAIRED: {path}")
PY

lake env lean HodgeProofHP/Stage4ThetaHankelSquareIdentity.lean
lake build HodgeProofHP.Stage4ThetaHankelSquareIdentity

echo "PASS: Stage4ThetaHankelSquareIdentity"
