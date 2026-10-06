#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import re

root = Path("HodgeProofHP")
source = root / "Stage4ThetaZeroMomentCertificate.lean"
target = root / "Stage4ThetaZeroMomentRefinedCertificate.lean"

if not source.is_file():
    raise SystemExit(f"STOP: missing {source}")

text = source.read_text(encoding="utf-8")
old_name = "hpThetaPhiMomentZero_gt_nine_twentieths"
new_name = "hpThetaPhiMomentZero_gt_twelve_twentyFifths"

pattern = re.compile(
    rf"(?ms)^theorem {old_name}\b.*?(?=^#print axioms)"
)
matches = list(pattern.finditer(text))
if len(matches) != 1:
    raise SystemExit("STOP: could not isolate the existing zeroth-moment proof")

proof = matches[0].group()
required = [
    "hpThetaPhi_finite_interval_lower_sum_le_momentZero",
    "hpThetaTraceCertificateLower_endpoint",
    "Finset.range 100",
    "(9 / 20 : ℝ)",
]
for item in required:
    if item not in proof:
        raise SystemExit(f"STOP: expected proof fragment missing: {item}")

replacements = {
    old_name: new_name,
    "hpThetaTraceCertificateLower_endpoint":
        "hpThetaFourthCertificateLower_endpoint",
    "hpThetaTraceCertificateLeft": "hpThetaFourthCertificateLeft",
    "hpThetaTraceCertificateRight": "hpThetaFourthCertificateRight",
    "hpThetaTraceCertificateLower": "hpThetaFourthCertificateLower",
    "Finset.range 100": "Finset.range 400",
    "(9 / 20 : ℝ)": "(12 / 25 : ℝ)",
}
for old, new in replacements.items():
    proof = proof.replace(old, new)

numeric = re.compile(
    r"(?m)^([ \t]*)norm_num\s*\[\s*"
    r"hpThetaFourthCertificateLeft\s*,\s*"
    r"hpThetaFourthCertificateRight\s*,\s*"
    r"hpThetaFourthCertificateLower\s*,\s*"
    r"Finset\.sum_range_succ\s*\]"
)
if len(list(numeric.finditer(proof))) != 1:
    raise SystemExit("STOP: unexpected numerical sum proof")

def replace_numeric(m):
    indent = m.group(1)
    return (
        f"{indent}-- Expand the sum before normalizing its rational terms.\n"
        f"{indent}simp only [Finset.sum_range_succ]\n"
        f"{indent}norm_num (config := {{ maxSteps := 2000000 }})\n"
        f"{indent}  [hpThetaFourthCertificateLeft,\n"
        f"{indent}   hpThetaFourthCertificateRight,\n"
        f"{indent}   hpThetaFourthCertificateLower]"
    )

proof = numeric.sub(replace_numeric, proof, count=1)

output = """import HodgeProofHP.Stage4ThetaFourthMomentLowerCertificate
import HodgeProofHP.Stage4ThetaZeroMomentCertificate

/-!
A refined numerical lower bound for the zeroth theta moment,
reusing the four hundred verified endpoint certificates.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The explicit rational sum contains four hundred certified intervals.
""" + proof + f"""
#print axioms {new_name}

end HodgeProofHP
"""

if target.exists():
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    backup = Path(str(target) + f".before_update_{stamp}")
    backup.write_bytes(target.read_bytes())
    print(f"BACKUP: {backup}")

target.write_text(output, encoding="utf-8")
print(f"CREATED: {target}")
PY

mkdir -p stage4_fourth_certificate_build_logs
log="stage4_fourth_certificate_build_logs/zero_moment_refined.log"

printf '[%s] Building refined zeroth-moment certificate\n' "$(date +%H:%M:%S)"

if lake build HodgeProofHP.Stage4ThetaZeroMomentRefinedCertificate > "$log" 2>&1; then
    tail -n 30 "$log"
else
    tail -n 100 "$log"
    printf 'STOP: build failed; log: %s\n' "$log"
    exit 1
fi

printf '%s\n' 'PASS: Stage4ThetaZeroMomentRefinedCertificate'
