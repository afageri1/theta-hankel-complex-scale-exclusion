#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

root = Path("HodgeProofHP")
required = root / "Stage4ThetaComplexScaledObstruction.lean"
if not required.is_file():
    raise SystemExit(f"STOP: missing {required}")

p = root / "Stage4ThetaComplexScaledObstructionAudit.lean"
if p.exists():
    backup = p.with_name(
        p.name + ".before_update_" +
        datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    )
    shutil.copy2(p, backup)
    print(f"BACKUP: {backup}")

source = r'''import HodgeProofHP.Stage4ThetaComplexScaledObstruction

/-!
Final audit of the obstruction for every complex scale.
A point of disagreement exists for each scale.
-/

namespace HodgeProofHP

theorem hpThetaHankel_every_complex_scale_exists_mismatch :
    ∀ c : ℂ, ∃ z : ℂ,
      hpThetaHankelSpectralProduct (c * z) ≠ hpThetaNormalizedXi z := by
  classical
  intro c
  by_contra h
  apply hpThetaHankelComplexScaledSpectralProduct_ne_normalizedXi c
  funext z
  change hpThetaHankelSpectralProduct (c * z) = hpThetaNormalizedXi z
  by_contra hz
  exact h ⟨z, hz⟩

example :
    ¬ ∃ c : ℂ,
      (fun z : ℂ => hpThetaHankelSpectralProduct (c * z)) =
        hpThetaNormalizedXi :=
  hpThetaHankel_no_complex_scale_normalizedXi_explicit

#check hpThetaHankel_certified_fourthMoment_strict
#check hpThetaHankelComplexScaledSpectralProduct_match_im_zero
#check hpThetaHankel_no_complex_scale_normalizedXi_explicit
#check hpThetaHankel_every_complex_scale_exists_mismatch

#print axioms hpThetaHankel_certified_fourthMoment_strict
#print axioms hpThetaHankelComplexScaledSpectralProduct_match_im_zero
#print axioms hpThetaHankel_no_complex_scale_normalizedXi_explicit
#print axioms hpThetaHankel_every_complex_scale_exists_mismatch

end HodgeProofHP
'''
p.write_text(source, encoding="utf-8")
print(f"CREATED: {p}")
PY

mkdir -p stage4_fourth_certificate_build_logs
log="stage4_fourth_certificate_build_logs/complex_scaled_obstruction_final_audit.log"

if lake build HodgeProofHP.Stage4ThetaComplexScaledObstructionAudit >"$log" 2>&1; then
    tail -n 85 "$log"
    if rg -n 'sorryAx' "$log"; then
        echo "STOP: sorryAx found in audit output"
        exit 1
    fi
    echo "PASS: Stage4ThetaComplexScaledObstructionAudit"
else
    tail -n 120 "$log"
    echo "STOP: build failed; log: $log"
    exit 1
fi
