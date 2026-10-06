#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import re

root = Path("HodgeProofHP")
target = root / "Stage4ThetaFourthMomentLowerCertificate.lean"
base = root / "Stage4ThetaFourthMomentCertificateBase.lean"
text = target.read_text(encoding="utf-8-sig")

marker = "private theorem hpThetaFourthCertificate_endpoint_0 :"

if marker not in text:
    if (
        base.exists()
        and "import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch19"
        in text
    ):
        print("Already split; resuming cached builds.")
        raise SystemExit(0)
    raise SystemExit("STOP: unexpected certificate file; no files changed.")

first = text.index(marker)
aggregate_start = text.index(
    "theorem hpThetaFourthCertificateLower_endpoint\n", first
)
generic_start = text.index(
    "theorem hpThetaFourthCertificate_finite_lower_sum_le_moment",
    aggregate_start,
)

prefix = text[:first]
numeric = text[first:aggregate_start]
suffix = text[generic_start:]

matches = list(re.finditer(
    r"private theorem hpThetaFourthCertificate_endpoint_(\d+)\s*:",
    numeric,
))
if [int(m.group(1)) for m in matches] != list(range(400)):
    raise SystemExit("STOP: expected exactly endpoints 0 through 399.")

if prefix.count(
    "private theorem hpThetaFourthCertificate_exp_upper_square"
) != 1:
    raise SystemExit("STOP: unexpected exponential helper.")

prefix = prefix.replace(
    "private theorem hpThetaFourthCertificate_exp_upper_square",
    "theorem hpThetaFourthCertificate_exp_upper_square",
)

endpoints = []
for i, match in enumerate(matches):
    end = matches[i+1].start() if i+1 < len(matches) else len(numeric)
    block = numeric[match.start():end]
    block = block.replace("private theorem", "theorem", 1)
    endpoints.append(block)

outputs = {
    base: prefix + "\nend HodgeProofHP\n",
}

for batch in range(20):
    lo, hi = 20*batch, 20*(batch+1)
    path = root / f"Stage4ThetaFourthMomentCertificateBatch{batch:02d}.lean"
    parts = ["""import HodgeProofHP.Stage4ThetaFourthMomentCertificateBase

/-! A finite batch of kernel-checked fourth-moment interval certificates. -/

-- Each batch contains twenty explicit exponential certificates.
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable section

namespace HodgeProofHP

"""]
    parts.extend(endpoints[lo:hi])
    parts.append(f"""
theorem hpThetaFourthCertificateLower_endpoint_batch_{batch}
    (i : ℕ) (hlo : {lo} ≤ i) (hi : i < {hi}) :
    hpThetaFourthCertificateLower i ≤
      hpThetaTraceEndpointLower
        (hpThetaFourthCertificateLeft i)
        (hpThetaFourthCertificateRight i) := by
  interval_cases i
""")
    for i in range(lo, hi):
        parts.append(f"""  · have h := hpThetaFourthCertificate_endpoint_{i}
    norm_num [hpThetaFourthCertificateLeft,
      hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
    exact h
""")
    parts.append("\nend HodgeProofHP\n")
    outputs[path] = "".join(parts)

imports = "\n".join(
    f"import HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch{b:02d}"
    for b in range(20)
)

bridge = """
theorem hpThetaFourthCertificateLower_endpoint
    (i : ℕ) (hi : i < 400) :
    hpThetaFourthCertificateLower i ≤
      hpThetaTraceEndpointLower
        (hpThetaFourthCertificateLeft i)
        (hpThetaFourthCertificateRight i) := by
"""
for batch in range(19):
    upper = 20*(batch+1)
    bridge += f"""  by_cases h{batch} : i < {upper}
  · exact hpThetaFourthCertificateLower_endpoint_batch_{batch}
      i (by omega) h{batch}
"""
bridge += """  exact hpThetaFourthCertificateLower_endpoint_batch_19
    i (by omega) hi
"""

outputs[target] = imports + """

/-!
The fourth-moment lower bound, assembled from independently compiled
interval certificate batches.
-/

-- The final rational sum has four hundred terms.
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable section

namespace HodgeProofHP

open MeasureTheory

""" + bridge + "\n" + suffix

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")

# All source validation and output construction precede writes.
for path, content in outputs.items():
    if path.exists():
        backup = path.with_name(path.name + ".before_split_" + stamp)
        backup.write_bytes(path.read_bytes())
        print("BACKUP:", backup)
    path.write_text(content, encoding="utf-8")
    print("CREATED:", path)
PY

logs="stage4_fourth_certificate_build_logs"
mkdir -p "$logs"

for batch in $(seq -w 0 19); do
  module="HodgeProofHP.Stage4ThetaFourthMomentCertificateBatch${batch}"
  log="$logs/batch_${batch}.log"

  printf '\n[%s] Building batch %s/19\n' "$(date +%H:%M:%S)" "$batch"

  if lake build "$module" >"$log" 2>&1; then
    printf 'PASS: batch %s\n' "$batch"
    tail -n 4 "$log"
  else
    tail -n 80 "$log"
    printf 'STOP: batch %s failed; log: %s\n' "$batch" "$log"
    exit 1
  fi
done

printf '\n[%s] Building final integral certificate\n' "$(date +%H:%M:%S)"

final_log="$logs/final.log"
if lake build HodgeProofHP.Stage4ThetaFourthMomentLowerCertificate \
    >"$final_log" 2>&1; then
  tail -n 20 "$final_log"
else
  tail -n 100 "$final_log"
  exit 1
fi

printf '%s\n' 'PASS: Stage4ThetaFourthMomentLowerCertificate'
