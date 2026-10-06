#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaTraceFirstIntervalCertificate.lean"),
    Path("create_hodgeproof_hp_stage4_theta_trace_first_interval_certificate.sh"),
]

replacements = [
    (
        "    norm_num at h\n    exact h\n",
        "    norm_num at h ⊢\n    exact h\n",
    ),
    (
        "  change (5 / 4 : ℝ) ≤\n",
        "  norm_num only [hpThetaTraceEndpointLower]\n"
        "  change (5 / 4 : ℝ) ≤\n",
    ),
]

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    for old, new in replacements:
        if text.count(old) != 1:
            raise SystemExit(
                f"STOP: expected one matching repair location in {path}: {old!r}"
            )
        text = text.replace(old, new, 1)
    newline = "\r\n" if b"\r\n" in raw else "\n"
    prepared.append((path, raw, text.replace("\n", newline).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, raw, repaired in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    path.write_bytes(repaired)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

lake env lean HodgeProofHP/Stage4ThetaTraceFirstIntervalCertificate.lean
lake build HodgeProofHP.Stage4ThetaTraceFirstIntervalCertificate
echo "PASS: Stage4ThetaTraceFirstIntervalCertificate"
