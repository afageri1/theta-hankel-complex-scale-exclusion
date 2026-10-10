#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import re

path = Path("HodgeProofHP/Stage4ThetaFourthMomentLowerCertificate.lean")
if not path.is_file():
    raise SystemExit(f"STOP: missing {path}")

raw = path.read_bytes()
newline = "\r\n" if b"\r\n" in raw else "\n"
text = raw.decode("utf-8").replace("\r\n", "\n")
updated = text

old = "pow_nonneg (hl i hi) 4"
new = "pow_nonneg hu0 4"

if old in updated:
    if updated.count(old) != 1:
        raise SystemExit("STOP: unexpected number of product-bound occurrences")
    updated = updated.replace(old, new, 1)
elif new not in updated:
    raise SystemExit("STOP: product-bound proof was not found")

marker = "-- Expand the finite sum separately from rational normalization."
pattern = re.compile(
    r"(?m)^([ \t]*)norm_num\s*\[\s*"
    r"hpThetaFourthCertificateLeft\s*,\s*"
    r"hpThetaFourthCertificateRight\s*,\s*"
    r"hpThetaFourthCertificateLower\s*,\s*"
    r"Finset\.sum_range_succ\s*\]"
)

if marker not in updated:
    matches = list(pattern.finditer(updated))
    if len(matches) != 1:
        raise SystemExit(
            f"STOP: expected one numerical sum proof, found {len(matches)}"
        )

    def replacement(m):
        indent = m.group(1)
        return (
            f"{indent}{marker}\n"
            f"{indent}simp only [Finset.sum_range_succ]\n"
            f"{indent}norm_num (config := {{ maxSteps := 2000000 }})\n"
            f"{indent}  [hpThetaFourthCertificateLeft,\n"
            f"{indent}   hpThetaFourthCertificateRight,\n"
            f"{indent}   hpThetaFourthCertificateLower]"
        )

    updated = pattern.sub(replacement, updated, count=1)

if updated != text:
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    backup = Path(str(path) + f".before_final_repair_{stamp}")
    backup.write_bytes(raw)
    path.write_bytes(updated.replace("\n", newline).encode("utf-8"))
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
else:
    print(f"ALREADY REPAIRED: {path}")
PY

mkdir -p stage4_fourth_certificate_build_logs
log="stage4_fourth_certificate_build_logs/final.log"

printf '[%s] Building final fourth-moment certificate\n' "$(date +%H:%M:%S)"

if lake build HodgeProofHP.Stage4ThetaFourthMomentLowerCertificate > "$log" 2>&1; then
    tail -n 30 "$log"
else
    tail -n 100 "$log"
    printf 'STOP: final certificate failed; log: %s\n' "$log"
    exit 1
fi

printf '%s\n' 'PASS: Stage4ThetaFourthMomentLowerCertificate'
