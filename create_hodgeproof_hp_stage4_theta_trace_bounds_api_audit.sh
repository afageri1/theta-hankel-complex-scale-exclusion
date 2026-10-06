#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "STOP: run from the hodgeproof-hp repository root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaFirstTraceXiRatio

target="HodgeProofHP/Stage4ThetaTraceBoundsApiAudit.lean"
mkdir -p HodgeProofHP

if [[ -f "$target" ]]; then
  backup="${target}.before_update_$(date +%Y%m%d_%H%M%S)_$$"
  cp "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaFirstTraceXiRatio

/-!
Audit the exact theta definitions and available bounds before
proving numerical moment and energy estimates.
-/

open MeasureTheory

namespace HodgeProofHP

#print hpRiemannThetaKernel
#print hpRiemannThetaLogProfile
#print hpRiemannThetaDifferentialKernel

#print hpThetaPhiMomentZero
#print hpThetaPhiMomentTwo
#print hpThetaFirstTraceEnergy
#print hpThetaXiMomentRatio

#check hpRiemannThetaDifferentialKernel_continuous
#check hpRiemannThetaDifferentialKernel_exp_weighted_tendsto_zero
#check hpThetaPhi_integrableOn
#check hpThetaPhi_secondMoment_integrableOn
#check hpRiemannThetaDifferentialKernel_hankel_weight_integrableOn

#check hpThetaFirstTraceEnergy_ne_ratio_of_bounds
#check hpThetaFirstTraceEnergy_ne_xi_secondDeriv_ratio_of_bounds

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaTraceBoundsApiAudit

python - <<'PY'
from pathlib import Path
import re

def report(root, pattern, title, limit):
    print("\n" + title)
    if not root.is_dir():
        print("Source directory unavailable:", root)
        return
    count = 0
    for path in sorted(root.rglob("*.lean")):
        lines = path.read_text(encoding="utf-8-sig").splitlines()
        for i, line in enumerate(lines):
            if pattern.search(line):
                print(f"{path.as_posix()}:{i + 1}: {line.strip()}")
                for extra in lines[i + 1:i + 4]:
                    print("  " + extra.strip())
                count += 1
                if count >= limit:
                    print(f"Output limited to {limit} matches.")
                    return
    if count == 0:
        print("No matching declarations found.")

decl = r"^\s*(?:(?:noncomputable|private|protected)\s+)*(?:def|abbrev|theorem|lemma)\s+"

report(
    Path("HodgeProofHP"),
    re.compile(
        decl + r"\S*(?:Theta|theta|Gaussian)\S*"
        r"(?:series|Series|sum|Sum|tsum|nonneg|pos|lower|upper|bound|Bound)\S*"
    ),
    "PROJECT: theta series, positivity and bounds",
    70,
)

report(
    Path(".lake/packages/mathlib/Mathlib"),
    re.compile(
        decl + r"(?:"
        r"\S*pi_(?:gt|lt|le|ge)\S*|"
        r"\S*exp_(?:bound|neg|le|lt)\S*|"
        r"\S*integral_mono\S*|"
        r"\S*integral_le\S*|"
        r"\S*sum_le_tsum\S*|"
        r"\S*tsum_le_tsum\S*"
        r")"
    ),
    "MATHLIB: numerical bounds and integral/series comparison",
    70,
)
PY

echo "PASS: Stage4ThetaTraceBoundsApiAudit"
