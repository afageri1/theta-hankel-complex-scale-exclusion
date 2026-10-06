#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import re

paths = [
    Path("HodgeProofHP/Stage4ThetaEnergyUpperCertificate.lean"),
    Path("create_hodgeproof_hp_stage4_theta_energy_upper_certificate.sh"),
]

name = "hpThetaEnergyUpperIntegrand_integrableOn_positive"
pattern = re.compile(
    r"(?m)(^theorem\s+" + re.escape(name) +
    r"\b[\s\S]*?:=\s*by)[\s\S]*?"
    r"(?=^\s*(?:theorem|lemma|def|#print|end)\b)"
)

body = """
  have heq :
      hpThetaEnergyUpperIntegrand =
        (fun u : ℝ =>
          u * hpRiemannThetaDifferentialKernel u ^ 2) := by
    funext u
    rfl
  rw [heq]
  exact hpRiemannThetaDifferentialKernel_hankel_weight_integrableOn

"""

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
updates = []

for p in paths:
    if not p.is_file():
        raise SystemExit(f"STOP: missing {p}")
    raw = p.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    matches = list(pattern.finditer(text))
    if len(matches) != 1:
        raise SystemExit(
            f"STOP: {p}: expected one theorem block, found {len(matches)}"
        )
    updated = pattern.sub(lambda m: m.group(1) + body, text)
    if b"\r\n" in raw:
        updated = updated.replace("\n", "\r\n")
    updates.append((p, raw, updated.encode("utf-8")))

for p, raw, updated in updates:
    backup = p.with_name(p.name + ".before_integrability_v2_" + stamp)
    backup.write_bytes(raw)
    p.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {p}")
PY

mkdir -p stage4_fourth_certificate_build_logs
log=stage4_fourth_certificate_build_logs/energy_upper_integrability_repair_v2.log

if lake build HodgeProofHP.Stage4ThetaEnergyUpperCertificate >"$log" 2>&1; then
    tail -n 40 "$log"
    echo "PASS: Stage4ThetaEnergyUpperCertificate"
else
    tail -n 100 "$log"
    echo "STOP: build failed; log: $log"
    exit 1
fi
