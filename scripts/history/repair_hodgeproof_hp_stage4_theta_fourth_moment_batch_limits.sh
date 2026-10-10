#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import re

root = Path("HodgeProofHP")
stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
changes = []

for b in range(20):
    path = root / f"Stage4ThetaFourthMomentCertificateBatch{b:02d}.lean"
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")

    raw = path.read_bytes()
    text = raw.decode("utf-8")
    newline = "\r\n" if "\r\n" in text else "\n"
    text = text.replace("\r\n", "\n")

    pattern = (
        r"(?m)^theorem "
        r"hpThetaFourthCertificateLower_endpoint_batch_\w+\b"
    )
    matches = list(re.finditer(pattern, text))
    if len(matches) != 1:
        raise SystemExit(
            f"STOP: {path}: expected one batch theorem, found {len(matches)}"
        )

    marker = "-- Allow the finite endpoint case split to elaborate."
    if marker in text:
        print(f"ALREADY REPAIRED: {path}")
        continue

    start = matches[0].start()
    prefix = (
        "set_option maxHeartbeats 2000000 in\n"
        f"{marker}\n"
    )
    updated = text[:start] + prefix + text[start:]
    changes.append((path, raw, updated.replace("\n", newline).encode("utf-8")))

# Validate every file before writing.
for path, raw, updated in changes:
    backup = Path(str(path) + f".before_limit_repair_{stamp}")
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
