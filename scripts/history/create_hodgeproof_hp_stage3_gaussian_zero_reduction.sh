#!/usr/bin/env bash
set -euo pipefail

target="HodgeProofHP/Stage3GaussianZeroReduction.lean"

if [ -f "$target" ]; then
  cp "$target" "$target.bak.$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage3GaussianFourierZero
import Mathlib.Analysis.Fourier.Inversion

/-!
Cancellation of the Gaussian factor, pointwise and almost everywhere.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpGaussianGroundFunction_ne_zero (x : ℝ) :
    hpGaussianGroundFunction x ≠ 0 := by
  rw [hpGaussianGroundFunction_eq_real]
  have hreal : Real.exp (-(x ^ (2 : ℕ) / 2)) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  simpa only [ne_eq, Complex.ofReal_eq_zero] using hreal

theorem hpGaussianWeightedL2Function_eq_zero_iff
    (v : HPSpace) (x : ℝ) :
    hpGaussianWeightedL2Function v x = 0 ↔ v x = 0 := by
  unfold hpGaussianWeightedL2Function
  rw [mul_eq_zero]
  simp only [hpGaussianGroundFunction_ne_zero x, false_or]

theorem hpGaussianWeightedL2Function_ae_eq_zero_iff
    (v : HPSpace) :
    (∀ᵐ x : ℝ ∂volume,
      hpGaussianWeightedL2Function v x = 0) ↔
    (∀ᵐ x : ℝ ∂volume, v x = 0) := by
  simp only [hpGaussianWeightedL2Function_eq_zero_iff]

end HodgeProofHP

#check MeasureTheory.Lp.ext
#check MeasureTheory.Lp.coeFn_zero
#check Integrable.fourier_fourierInv_eq
#check Continuous.fourier_fourierInv_eq

#print axioms HodgeProofHP.hpGaussianGroundFunction_ne_zero
#print axioms HodgeProofHP.hpGaussianWeightedL2Function_eq_zero_iff
#print axioms HodgeProofHP.hpGaussianWeightedL2Function_ae_eq_zero_iff
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage3GaussianZeroReduction

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib")
paths = [
    root / "Analysis/Fourier/Inversion.lean",
    root / "Analysis/Fourier/LpSpace.lean",
    root / "Analysis/Distribution/TemperedDistribution.lean",
]

print("\n=== LOCAL FOURIER UNIQUENESS API ===")
for path in paths:
    if not path.exists():
        print(f"\nMISSING: {path}")
        continue

    lines = path.read_text(encoding="utf-8").splitlines()
    print(f"\nFILE: {path}")
    for i, line in enumerate(lines):
        if not re.match(
            r"^\s*(?:(?:protected|private|noncomputable)\s+)*"
            r"(?:theorem|lemma|def)\s+", line
        ):
            continue
        if path.name != "Inversion.lean" and not re.search(
            r"fourier|injectiv|toTemperedDistribution|integrable",
            line, re.I
        ):
            continue
        for following in lines[i:i + 24]:
            print(following)
            if ":= " in following or following.rstrip().endswith(":= by"):
                break
PY
