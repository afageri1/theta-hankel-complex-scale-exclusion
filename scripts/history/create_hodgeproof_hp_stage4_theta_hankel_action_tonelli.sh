#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelActionParseval

target="HodgeProofHP/Stage4ThetaHankelActionTonelli.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelActionParseval
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
Tonelli exchange for squared theta Hankel actions.
The sums and integrals here take values in ENNReal.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaHankelAction_sq_ofReal_aemeasurable
    (f : HPThetaHankelSpace) :
    AEMeasurable
      (fun x =>
        ENNReal.ofReal (‖hpThetaHankelActionFunction f x‖ ^ 2))
      hpThetaHankelMeasure := by
  have hm :
      AEMeasurable
        (fun x => ‖hpThetaHankelActionFunction f x‖)
        hpThetaHankelMeasure :=
    (hpThetaHankelActionFunction_aestronglyMeasurable f).norm.aemeasurable
  simpa only [pow_two, Pi.mul_apply] using
    (hm.mul hm).ennreal_ofReal

theorem hpThetaHankelAction_sq_lintegral_tsum
    {ι : Type*} [Countable ι]
    (v : ι → HPThetaHankelSpace) :
    (∫⁻ x,
      (∑' i,
        ENNReal.ofReal
          (‖hpThetaHankelActionFunction (v i) x‖ ^ 2))
      ∂hpThetaHankelMeasure) =
    ∑' i, ∫⁻ x,
      ENNReal.ofReal
        (‖hpThetaHankelActionFunction (v i) x‖ ^ 2)
      ∂hpThetaHankelMeasure := by
  exact lintegral_tsum
    (fun i => hpThetaHankelAction_sq_ofReal_aemeasurable (v i))

theorem hpThetaHankelBasis_sq_tsum_lintegral
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (∑' i, ∫⁻ x,
      ENNReal.ofReal
        (‖hpThetaHankelActionFunction (b i) x‖ ^ 2)
      ∂hpThetaHankelMeasure) =
    ∫⁻ x,
      (∑' i,
        ENNReal.ofReal
          (‖hpThetaHankelActionFunction (b i) x‖ ^ 2))
      ∂hpThetaHankelMeasure :=
  (hpThetaHankelAction_sq_lintegral_tsum
    (fun i => b i)).symm

#print axioms hpThetaHankelAction_sq_ofReal_aemeasurable
#print axioms hpThetaHankelAction_sq_lintegral_tsum
#print axioms hpThetaHankelBasis_sq_tsum_lintegral

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelActionTonelli

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib")
folders = [
    root / "Data" / "ENNReal",
    root / "Topology" / "Instances" / "ENNReal",
    root / "MeasureTheory" / "Integral",
]
declaration = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:protected|private|noncomputable)\s+)*"
    r"(?:theorem|lemma|def)\s+"
)
count = 0
print("=== ENNReal sum and nonnegative integral conversions ===")
for folder in folders:
    if not folder.exists():
        continue
    for path in sorted(folder.rglob("*.lean")):
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            if not declaration.search(line):
                continue
            header = "\n".join(lines[i:i + 5])
            sum_match = "ofReal" in header and "tsum" in header
            integral_match = (
                "integral" in line
                and "lintegral" in line
                and "nonneg" in line
            )
            if sum_match or integral_match:
                print(f"\n{path}:{i + 1}")
                print("\n".join(lines[i:i + 12]))
                count += 1
print(f"\nMatched declarations: {count}")
PY

printf '%s\n' 'PASS: Stage4ThetaHankelActionTonelli'
