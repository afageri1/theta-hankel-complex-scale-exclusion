#!/usr/bin/env bash
set -euo pipefail

command -v lake >/dev/null || {
  echo "ERROR: lake is not available."
  exit 1
}

lake build HodgeProofHP.Stage4ThetaTraceRemainingBound

mkdir -p scripts

python - <<'PY'
import re
from pathlib import Path

root = Path("HodgeProofHP")
checks = {}
blocks = []

declaration = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected)\s+)*"
    r"(?:def|theorem|lemma|abbrev)\s+([A-Za-z0-9_₀-₉']+)"
)

wanted = re.compile(
    r"hpRiemannThetaLogProfile"
    r"|hpThetaComplexProfile"
    r"|hpThetaPhiMomentTwo"
    r"|hpRiemannThetaDifferentialKernel"
)

details = re.compile(
    r"hpRiemannThetaLogProfile"
    r"|hpThetaPhiMomentTwo"
)

for path in sorted(root.glob("Stage4*.lean")):
    text = path.read_text(encoding="utf-8-sig")
    if "namespace HodgeProofHP" not in text:
        continue
    matches = list(declaration.finditer(text))
    for j, match in enumerate(matches):
        name = match.group(1)
        if not wanted.search(name):
            continue
        prefix = text[match.start():match.end()]
        if "private" in prefix:
            continue
        checks.setdefault(name, path.name)
        if details.search(name):
            end = (
                matches[j+1].start()
                if j+1 < len(matches)
                else len(text)
            )
            block = text[match.start():end]
            block = re.split(
                r"(?m)^#(?:print|check)\b|^end HodgeProofHP\b",
                block,
                maxsplit=1,
            )[0].rstrip()
            blocks.append(f"\nFILE: {path}\n{block}\n")

audit = [
    "import HodgeProofHP.Stage4ThetaTraceRemainingBound",
    "",
    "/-! API audit for the second-moment upper bound. -/",
    "",
]
for name, filename in sorted(checks.items()):
    audit.append(f"-- {filename}")
    audit.append(f"#check HodgeProofHP.{name}")

audit += [
    "",
    "#print HodgeProofHP.hpRiemannThetaLogProfile",
    "#print HodgeProofHP.hpRiemannThetaDifferentialKernel",
    "#print HodgeProofHP.hpThetaPhiMomentTwo",
    "",
]

Path("HodgeProofHP/Stage4ThetaSecondMomentUpperAudit.lean").write_text(
    "\n".join(audit), encoding="utf-8"
)

Path("scripts/hp_theta_second_moment_upper_sources.txt").write_text(
    "".join(blocks), encoding="utf-8"
)

print("CREATED: HodgeProofHP/Stage4ThetaSecondMomentUpperAudit.lean")
print("CREATED: scripts/hp_theta_second_moment_upper_sources.txt")
print("Selected declarations:", len(checks))
PY

log="scripts/hp_theta_second_moment_upper_audit.log"

lake env lean HodgeProofHP/Stage4ThetaSecondMomentUpperAudit.lean \
  > "$log" 2>&1 || {
    cat "$log"
    exit 1
  }

cat "$log"
cat scripts/hp_theta_second_moment_upper_sources.txt

echo "PASS: Stage4ThetaSecondMomentUpperAudit"
echo "This is an API/source audit, not a proof of the numerical upper bound."
