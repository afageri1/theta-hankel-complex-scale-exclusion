#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaPhiFourthMomentIntegrability
lake build HodgeProofHP.Stage4ThetaPhiSecondIntegralDerivative

target="HodgeProofHP/Stage4ThetaPhiThirdMomentIntegrability.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaPhiFourthMomentIntegrability

/-!
Integrability of the third moment of the differential theta kernel
with arbitrary real exponential weights.
-/

noncomputable section

open MeasureTheory Set

namespace HodgeProofHP

theorem hpThetaPhi_thirdPower_le_exp_three_mul
    (u : ℝ) (hu : 0 ≤ u) :
    u ^ 3 ≤ Real.exp (3 * u) := by
  have huexp : u ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    linarith
  have hsq : u ^ 2 ≤ (Real.exp u) ^ 2 := by
    simpa only [pow_two] using
      (mul_le_mul huexp huexp hu
        (le_of_lt (Real.exp_pos u)))
  have hcube :
      u ^ 2 * u ≤ (Real.exp u) ^ 2 * Real.exp u :=
    mul_le_mul hsq huexp hu (sq_nonneg (Real.exp u))
  have hexp :
      Real.exp (3 * u) =
        (Real.exp u) ^ 2 * Real.exp u := by
    rw [show 3 * u = (u + u) + u by ring,
      Real.exp_add, Real.exp_add]
    ring
  calc
    u ^ 3 = u ^ 2 * u := by ring
    _ ≤ (Real.exp u) ^ 2 * Real.exp u := hcube
    _ = Real.exp (3 * u) := hexp.symm

theorem hpThetaPhi_thirdMoment_exp_integrableOn (c : ℝ) :
    IntegrableOn
      (fun u : ℝ =>
        u ^ 3 * Real.exp (c * u) *
          hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume := by
  have hG := hpThetaPhi_exp_weighted_integrableOn (c + 3)
  have hcont :
      Continuous
        (fun u : ℝ =>
          u ^ 3 * Real.exp (c * u) *
            hpRiemannThetaDifferentialKernel u) :=
    ((continuous_id.pow 3).mul
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).mul
      hpRiemannThetaDifferentialKernel_continuous
  apply hG.norm.mono' hcont.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have hu3 : 0 ≤ u ^ 3 := pow_nonneg hu0 3
  have hweight :
      u ^ 3 * Real.exp (c * u) ≤
        Real.exp ((c + 3) * u) := by
    calc
      u ^ 3 * Real.exp (c * u) ≤
          Real.exp (3 * u) * Real.exp (c * u) :=
        mul_le_mul_of_nonneg_right
          (hpThetaPhi_thirdPower_le_exp_three_mul u hu0)
          (le_of_lt (Real.exp_pos (c * u)))
      _ = Real.exp ((c + 3) * u) := by
        rw [← Real.exp_add]
        congr 1
        ring
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hu3,
    abs_of_pos (Real.exp_pos (c * u)),
    abs_of_pos (Real.exp_pos ((c + 3) * u))]
  exact mul_le_mul_of_nonneg_right hweight
    (abs_nonneg (hpRiemannThetaDifferentialKernel u))

theorem hpThetaPhi_thirdMoment_integrableOn :
    IntegrableOn
      (fun u : ℝ => u ^ 3 * hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume := by
  simpa using hpThetaPhi_thirdMoment_exp_integrableOn (0 : ℝ)

#print axioms hpThetaPhi_thirdPower_le_exp_three_mul
#print axioms hpThetaPhi_thirdMoment_exp_integrableOn
#print axioms hpThetaPhi_thirdMoment_integrableOn

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaPhiThirdMomentIntegrability

python - <<'PY'
from pathlib import Path

root = Path("HodgeProofHP")
selected = {root / "Stage4ThetaPhiLocalBounds.lean"}

for path in root.glob("Stage4*.lean"):
    text = path.read_text(encoding="utf-8-sig")
    if "def hpThetaPhiCosIntegrandSecond" in text:
        selected.add(path)

for path in sorted(selected):
    if not path.is_file():
        raise SystemExit(f"STOP: missing source: {path}")
    print(f"\n=== SOURCE: {path} ===")
    print(path.read_text(encoding="utf-8-sig"))
PY

printf '%s\n' 'PASS: Stage4ThetaPhiThirdMomentIntegrability'
