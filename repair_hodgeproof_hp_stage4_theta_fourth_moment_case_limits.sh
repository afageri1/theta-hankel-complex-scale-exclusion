#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import re

root = Path("HodgeProofHP")
stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
changes = []

pattern = re.compile(
    r"(?m)^  · have h := (hpThetaFourthCertificate_endpoint_(\d+))\n"
    r"    norm_num \[hpThetaFourthCertificateLeft,\n"
    r"      hpThetaFourthCertificateRight, hpThetaFourthCertificateLower\] at h ⊢\n"
    r"    exact h"
)

for b in range(20):
    path = root / f"Stage4ThetaFourthMomentCertificateBatch{b:02d}.lean"
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")

    raw = path.read_bytes()
    text = raw.decode("utf-8")
    newline = "\r\n" if "\r\n" in text else "\n"
    text = text.replace("\r\n", "\n")

    marker = "-- Apply the resource limit inside each interval case."
    if marker in text:
        print(f"ALREADY REPAIRED: {path}")
        continue

    matches = list(pattern.finditer(text))
    indices = [int(m.group(2)) for m in matches]
    expected = list(range(20 * b, 20 * (b + 1)))
    if indices != expected:
        raise SystemExit(
            f"STOP: {path}: unexpected endpoint case structure: {indices}"
        )

    def replace(m):
        return (
            "  · set_option maxHeartbeats 2000000 in\n"
            "    exact (by\n"
            f"      have h := {m.group(1)}\n"
            "      norm_num [hpThetaFourthCertificateLeft,\n"
            "        hpThetaFourthCertificateRight,"
            " hpThetaFourthCertificateLower] at h ⊢\n"
            "      exact h)"
        )

    updated = pattern.sub(replace, text)
    updated = updated.replace(
        "  interval_cases i\n",
        f"  {marker}\n  interval_cases i\n",
        1
    )
    changes.append(
        (path, raw, updated.replace("\n", newline).encode("utf-8"))
    )

# Validate every batch before changing any file.
for path, raw, updated in changes:
    backup = Path(str(path) + f".before_case_limit_repair_{stamp}")
    backup.write_bytes(raw)
    path.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

mkdir -p stage4_fourth_certificate_build_logs

for batch in $(seq -w 0 19); do
    module="HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch${batch}"
    log="stage4_fourth_certificate_build_logs/batch_${batch}.log"

    printf '\n[%s] Building batch %s/19\n' "$(date +%H:%M:%S)" "$batch"

    if lake build "$module" > "$log" 2>&1; then
        tail -n 4 "$log"
        printf 'PASS: batch %s\n' "$batch"
    else
        tail -n 100 "$log"
        printf 'STOP: batch %s failed; log: %s\n' "$batch" "$log"
        exit 1
    fi
done

log="stage4_fourth_certificate_build_logs/final.log"
if lake build HodgeProofHP.Stage4ThetaFourthMomentLowerCertificate > "$log" 2>&1; then
    tail -n 25 "$log"
else
    tail -n 100 "$log"
    printf 'STOP: final certificate failed; log: %s\n' "$log"
    exit 1
fi

printf '%s\n' 'PASS: Stage4ThetaFourthMomentLowerCertificate'
