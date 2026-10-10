#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaRealScaledObstruction.lean"),
    Path("create_hodgeproof_hp_stage4_theta_real_scaled_obstruction.sh"),
]
old = """  first
  | nlinarith only [h, hbad]
  | nlinarith only [h, hneg]"""
new = """  nlinarith only [h, hbad]"""

prepared = []
for p in paths:
    if not p.is_file():
        raise SystemExit(f"STOP: missing {p}")
    raw = p.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    if text.count(old) != 1:
        raise SystemExit(f"STOP: unexpected tactic block in {p}")
    a = text.find("  have hneg :\n")
    b = text.find("  field_simp [h0ne] at h\n", a)
    if a < 0 or b < 0:
        raise SystemExit(f"STOP: expected cleanup boundaries missing in {p}")
    fixed = (text[:a] + text[b:]).replace(old, new, 1)
    newline = "\r\n" if b"\r\n" in raw else "\n"
    prepared.append((p, fixed.replace("\n", newline).encode("utf-8")))

audit = Path("HodgeProofHP/Stage4ThetaRealScaledObstructionAudit.lean")
source = r'''import HodgeProofHP.Stage4ThetaRealScaledObstruction

/-!
Final audit of the certified obstruction for real scales.
The conclusion concerns this theta Hankel spectral product.
-/

namespace HodgeProofHP

#check hpThetaHankelSpectralSquareEnergy_gt_triangle_certificate
#check hpThetaHankel_certified_fourthMoment_strict
#check hpThetaHankelScaledSpectralProduct_ne_normalizedXi_certified
#check hpThetaHankel_no_real_scale_normalizedXi

example :
    ¬ ∃ c : ℝ,
      hpThetaHankelScaledSpectralProduct c = hpThetaNormalizedXi :=
  hpThetaHankel_no_real_scale_normalizedXi

#print axioms hpThetaHankelSpectralSquareEnergy_gt_triangle_certificate
#print axioms hpThetaHankel_certified_fourthMoment_strict
#print axioms hpThetaHankelScaledSpectralProduct_ne_normalizedXi_certified
#print axioms hpThetaHankel_no_real_scale_normalizedXi

end HodgeProofHP
'''
prepared.append((audit, source.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for p, data in prepared:
    if p.exists():
        backup = p.with_name(p.name + ".before_finalize_" + stamp)
        shutil.copy2(p, backup)
        print(f"BACKUP: {backup}")
    p.write_bytes(data)
    print(f"WROTE: {p}")
PY

mkdir -p stage4_fourth_certificate_build_logs
log="stage4_fourth_certificate_build_logs/real_scaled_obstruction_final_audit.log"

if lake build HodgeProofHP.Stage4ThetaRealScaledObstructionAudit >"$log" 2>&1; then
    tail -n 80 "$log"
    if rg -n 'sorryAx' "$log"; then
        echo "STOP: sorryAx found in audit output"
        exit 1
    fi
    echo "PASS: Stage4ThetaRealScaledObstructionAudit"
else
    tail -n 110 "$log"
    echo "STOP: build failed; log: $log"
    exit 1
fi
