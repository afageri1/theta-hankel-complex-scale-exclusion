#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

p = Path("HodgeProofHP/Stage4ThetaTriangleSquareMoment.lean")

source = r"""import HodgeProofHP.Stage4ThetaTriangleSquareLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
The nonnegative square integral equals the certified triangle moment.
Its real value therefore inherits the rational lower bound.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

theorem hpThetaTriangleIntegrand_nonneg_ae_positive :
    0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      hpThetaTriangleIntegrand := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact hpThetaTriangleIntegrand_nonneg u (le_of_lt hu)

theorem hpThetaTriangleMoment_nonneg :
    0 ≤ hpThetaTriangleMoment := by
  unfold hpThetaTriangleMoment
  exact integral_nonneg_of_ae
    hpThetaTriangleIntegrand_nonneg_ae_positive

theorem hpThetaTriangleMoment_lintegral :
    (∫⁻ u in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (hpThetaTriangleWeight u) *
        ENNReal.ofReal (hpRiemannThetaDifferentialKernel u)) =
      ENNReal.ofReal hpThetaTriangleMoment := by
  have h :=
    ofReal_integral_eq_lintegral_ofReal
      hpThetaTriangleIntegrand_integrableOn
      hpThetaTriangleIntegrand_nonneg_ae_positive
  calc
    (∫⁻ u in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (hpThetaTriangleWeight u) *
        ENNReal.ofReal (hpRiemannThetaDifferentialKernel u)) =
      ∫⁻ u in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (hpThetaTriangleIntegrand u) := by
      apply lintegral_congr
      intro u
      have hw : 0 ≤ hpThetaTriangleWeight u := by
        unfold hpThetaTriangleWeight
        exact le_max_left _ _
      exact (ENNReal.ofReal_mul hw).symm
    _ = ENNReal.ofReal hpThetaTriangleMoment := by
      exact h.symm

theorem hpThetaTriangle_phi_square_lintegral_eq_moment :
    (∫⁻ x in Set.Ioo (0 : ℝ) (1 / 4),
      ∫⁻ y in Set.Ioo (0 : ℝ) (1 / 4),
        ENNReal.ofReal (hpRiemannThetaDifferentialKernel (x + y))) =
      ENNReal.ofReal hpThetaTriangleMoment := by
  rw [hpThetaTriangle_phi_square_lintegral]
  exact hpThetaTriangleMoment_lintegral

theorem hpThetaTriangle_phi_square_lintegral_ne_top :
    (∫⁻ x in Set.Ioo (0 : ℝ) (1 / 4),
      ∫⁻ y in Set.Ioo (0 : ℝ) (1 / 4),
        ENNReal.ofReal
          (hpRiemannThetaDifferentialKernel (x + y))) ≠ ⊤ := by
  rw [hpThetaTriangle_phi_square_lintegral_eq_moment]
  exact ENNReal.ofReal_ne_top

theorem hpThetaTriangle_phi_square_lintegral_toReal :
    (∫⁻ x in Set.Ioo (0 : ℝ) (1 / 4),
      ∫⁻ y in Set.Ioo (0 : ℝ) (1 / 4),
        ENNReal.ofReal
          (hpRiemannThetaDifferentialKernel (x + y))).toReal =
      hpThetaTriangleMoment := by
  rw [hpThetaTriangle_phi_square_lintegral_eq_moment,
    ENNReal.toReal_ofReal hpThetaTriangleMoment_nonneg]

theorem hpThetaTriangleMoment_gt :
    (117 / 2000 : ℝ) < hpThetaTriangleMoment := by
  have h := hpThetaHankelTriangleRayleighLower_gt
  change (117 / 500 : ℝ) < 4 * hpThetaTriangleMoment at h
  linarith

theorem hpThetaTriangle_phi_square_lintegral_toReal_gt :
    (117 / 2000 : ℝ) <
      (∫⁻ x in Set.Ioo (0 : ℝ) (1 / 4),
        ∫⁻ y in Set.Ioo (0 : ℝ) (1 / 4),
          ENNReal.ofReal
            (hpRiemannThetaDifferentialKernel (x + y))).toReal := by
  rw [hpThetaTriangle_phi_square_lintegral_toReal]
  exact hpThetaTriangleMoment_gt

#print axioms hpThetaTriangle_phi_square_lintegral_eq_moment
#print axioms hpThetaTriangle_phi_square_lintegral_ne_top
#print axioms hpThetaTriangle_phi_square_lintegral_toReal
#print axioms hpThetaTriangle_phi_square_lintegral_toReal_gt

end HodgeProofHP
"""

if p.exists():
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    backup = p.with_name(p.name + ".before_update_" + stamp)
    backup.write_bytes(p.read_bytes())
    print("BACKUP:", backup)

p.write_text(source, encoding="utf-8")
print("CREATED:", p)
PY

mkdir -p stage4_fourth_certificate_build_logs
log=stage4_fourth_certificate_build_logs/triangle_square_moment.log

if lake build HodgeProofHP.Stage4ThetaTriangleSquareMoment >"$log" 2>&1; then
    tail -n 45 "$log"
    echo "PASS: Stage4ThetaTriangleSquareMoment"
else
    tail -n 100 "$log"
    echo "STOP: build failed; log: $log"
    exit 1
fi
