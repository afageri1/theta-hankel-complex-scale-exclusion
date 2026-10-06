#!/usr/bin/env bash
set -euo pipefail

command -v lake >/dev/null || {
  echo "ERROR: lake not found"
  exit 1
}

lake build HodgeProofHP.Stage4ThetaProfileSecondMomentIntegrability

python - <<'PY'
from pathlib import Path
from datetime import datetime

path = Path("HodgeProofHP/Stage4ThetaImproperSecondMomentIBP.lean")
if path.exists():
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    backup = path.with_name(path.name + ".before_create_" + stamp)
    backup.write_bytes(path.read_bytes())
    print(f"BACKUP: {backup}")
path.parent.mkdir(parents=True, exist_ok=True)
PY

cat > HodgeProofHP/Stage4ThetaImproperSecondMomentIBP.lean <<'LEAN'
import HodgeProofHP.Stage4ThetaProfileSecondMomentIntegrability
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
Second-moment integration by parts on the positive half-line.
The polynomial boundary terms vanish at infinity.
-/

namespace HodgeProofHP

open MeasureTheory Filter
open scoped Topology

theorem hpThetaPhi_secondMoment_improper_ibp :
    (∫ u : ℝ in Set.Ioi 0,
      u ^ 2 * hpRiemannThetaDifferentialKernel u) =
      2 * (∫ u : ℝ in Set.Ioi 0,
        hpRiemannThetaLogProfile u) -
      (1 / 4 : ℝ) * (∫ u : ℝ in Set.Ioi 0,
        u ^ 2 * hpRiemannThetaLogProfile u) := by
  have hLeft :
      Tendsto
        (fun R : ℝ =>
          ∫ u in (0 : ℝ)..R,
            u ^ 2 * hpRiemannThetaDifferentialKernel u)
        atTop
        (𝓝 (∫ u : ℝ in Set.Ioi 0,
          u ^ 2 * hpRiemannThetaDifferentialKernel u)) :=
    intervalIntegral_tendsto_integral_Ioi 0
      hpThetaPhi_secondMoment_integrableOn tendsto_id
  have hBase :
      Tendsto
        (fun R : ℝ =>
          ∫ u in (0 : ℝ)..R, hpRiemannThetaLogProfile u)
        atTop
        (𝓝 (∫ u : ℝ in Set.Ioi 0,
          hpRiemannThetaLogProfile u)) :=
    intervalIntegral_tendsto_integral_Ioi 0
      hpRiemannThetaLogProfile_integrableOn tendsto_id
  have hWeighted :
      Tendsto
        (fun R : ℝ =>
          ∫ u in (0 : ℝ)..R,
            u ^ 2 * hpRiemannThetaLogProfile u)
        atTop
        (𝓝 (∫ u : ℝ in Set.Ioi 0,
          u ^ 2 * hpRiemannThetaLogProfile u)) :=
    intervalIntegral_tendsto_integral_Ioi 0
      hpThetaSecondMoment_profile_weight_integrableOn tendsto_id
  have hRight :
      Tendsto
        (fun R : ℝ =>
          R ^ 2 * deriv hpRiemannThetaLogProfile R -
            2 * R * hpRiemannThetaLogProfile R +
            2 * (∫ u in (0 : ℝ)..R,
              hpRiemannThetaLogProfile u) -
            (1 / 4 : ℝ) * (∫ u in (0 : ℝ)..R,
              u ^ 2 * hpRiemannThetaLogProfile u))
        atTop
        (𝓝 (
          2 * (∫ u : ℝ in Set.Ioi 0,
            hpRiemannThetaLogProfile u) -
          (1 / 4 : ℝ) * (∫ u : ℝ in Set.Ioi 0,
            u ^ 2 * hpRiemannThetaLogProfile u))) := by
    simpa only [zero_add] using
      (hpThetaSecondMoment_boundary_tendsto_zero.add
        (hBase.const_mul (2 : ℝ))).sub
          (hWeighted.const_mul (1 / 4 : ℝ))
  have hFunctions :
      (fun R : ℝ =>
        ∫ u in (0 : ℝ)..R,
          u ^ 2 * hpRiemannThetaDifferentialKernel u) =
      (fun R : ℝ =>
        R ^ 2 * deriv hpRiemannThetaLogProfile R -
          2 * R * hpRiemannThetaLogProfile R +
          2 * (∫ u in (0 : ℝ)..R,
            hpRiemannThetaLogProfile u) -
          (1 / 4 : ℝ) * (∫ u in (0 : ℝ)..R,
            u ^ 2 * hpRiemannThetaLogProfile u)) := by
    funext R
    exact hpRiemannThetaDifferentialKernel_finite_secondMoment_ibp R
  rw [← hFunctions] at hRight
  exact tendsto_nhds_unique hLeft hRight

theorem hpThetaPhiMomentTwo_eq_profile_integrals :
    hpThetaPhiMomentTwo =
      2 * (∫ u : ℝ in Set.Ioi 0,
        hpRiemannThetaLogProfile u) -
      (1 / 4 : ℝ) * (∫ u : ℝ in Set.Ioi 0,
        u ^ 2 * hpRiemannThetaLogProfile u) := by
  unfold hpThetaPhiMomentTwo
  exact hpThetaPhi_secondMoment_improper_ibp

#print axioms hpThetaPhi_secondMoment_improper_ibp
#print axioms hpThetaPhiMomentTwo_eq_profile_integrals

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage4ThetaImproperSecondMomentIBP.lean
lake build HodgeProofHP.Stage4ThetaImproperSecondMomentIBP

echo "PASS: Stage4ThetaImproperSecondMomentIBP"
