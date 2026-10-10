#!/usr/bin/env bash
set -euo pipefail

target="HodgeProofHP/Stage3GaussianWeightedL2.lean"

if [ -f "$target" ]; then
  cp "$target" "$target.bak.$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage3GaussianZeroReduction
import Mathlib.Analysis.Fourier.LpSpace

/-!
The Gaussian-weighted representative belongs to L².
Its almost-everywhere vanishing implies vanishing of the original L² vector.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpGaussianGroundFunction_norm_le_one (x : ℝ) :
    ‖hpGaussianGroundFunction x‖ ≤ 1 := by
  rw [hpGaussianGroundFunction_norm_eq_real]
  calc
    Real.exp (-(x ^ 2 / 2)) ≤ Real.exp 0 := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg x]
    _ = 1 := Real.exp_zero

theorem hpGaussianWeightedL2Function_norm_le
    (v : HPSpace) (x : ℝ) :
    ‖hpGaussianWeightedL2Function v x‖ ≤ ‖v x‖ := by
  unfold hpGaussianWeightedL2Function
  rw [norm_mul]
  calc
    ‖hpGaussianGroundFunction x‖ * ‖v x‖ ≤
        1 * ‖v x‖ :=
      mul_le_mul_of_nonneg_right
        (hpGaussianGroundFunction_norm_le_one x) (norm_nonneg _)
    _ = ‖v x‖ := one_mul _

theorem hpGaussianWeightedL2Function_memLp
    (v : HPSpace) :
    MemLp (hpGaussianWeightedL2Function v) 2 volume := by
  have hc : Continuous hpGaussianGroundFunction := by
    have heq : hpGaussianGroundFunction =
        (fun x : ℝ => (Real.exp (-(x ^ 2 / 2)) : ℂ)) := by
      funext x
      exact hpGaussianGroundFunction_eq_real x
    rw [heq]
    fun_prop
  have hm :
      AEStronglyMeasurable (hpGaussianWeightedL2Function v) volume := by
    have h :=
      hc.aestronglyMeasurable.mul
        (Lp.memLp v).aestronglyMeasurable
    change AEStronglyMeasurable
      (fun x : ℝ => hpGaussianGroundFunction x * v x) volume at h
    exact h
  exact (Lp.memLp v).norm.mono' hm
    (Filter.Eventually.of_forall
      (fun x => hpGaussianWeightedL2Function_norm_le v x))

noncomputable def hpGaussianWeightedL2 (v : HPSpace) : HPSpace :=
  (hpGaussianWeightedL2Function_memLp v).toLp
    (hpGaussianWeightedL2Function v)

theorem hpGaussianWeightedL2_coeFn_ae (v : HPSpace) :
    (fun x : ℝ => hpGaussianWeightedL2 v x) =ᵐ[volume]
      hpGaussianWeightedL2Function v := by
  exact (hpGaussianWeightedL2Function_memLp v).coeFn_toLp

theorem hpL2_eq_zero_of_gaussianWeighted_ae_zero
    (v : HPSpace)
    (h : ∀ᵐ x : ℝ ∂volume,
      hpGaussianWeightedL2Function v x = 0) :
    v = 0 := by
  have hv : ∀ᵐ x : ℝ ∂volume, v x = 0 :=
    (hpGaussianWeightedL2Function_ae_eq_zero_iff v).mp h
  apply Lp.ext
  filter_upwards [hv, Lp.coeFn_zero ℂ 2 volume] with x hx hz
  exact hx.trans hz.symm

end HodgeProofHP

#check MeasureTheory.Lp.toTemperedDistribution_apply
#check MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
#check MeasureTheory.Lp.fourier_toTemperedDistribution_eq

#print axioms HodgeProofHP.hpGaussianGroundFunction_norm_le_one
#print axioms HodgeProofHP.hpGaussianWeightedL2Function_memLp
#print axioms HodgeProofHP.hpGaussianWeightedL2_coeFn_ae
#print axioms HodgeProofHP.hpL2_eq_zero_of_gaussianWeighted_ae_zero
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage3GaussianWeightedL2

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib")
paths = [
    root / "Analysis/Fourier/FourierTransform.lean",
    root / "Analysis/Distribution/SchwartzSpace/Fourier.lean",
    root / "Analysis/Distribution/AEEqOfIntegralContDiff.lean",
]

print("\n=== FOURIER INTEGRAL PAIRING API ===")
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
        if path.name != "AEEqOfIntegralContDiff.lean" and not re.search(
            r"integral.*fourier|fourier.*integral|integral.*bilin|fourier.*coe",
            line, re.I
        ):
            continue
        for following in lines[i:i + 32]:
            print(following)
            if ":= " in following or following.rstrip().endswith(":= by"):
                break
PY
