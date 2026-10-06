#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaTriangleRayleighBridge.lean"),
    Path("create_hodgeproof_hp_stage4_theta_triangle_rayleigh_bridge.sh"),
]

start = "theorem hpThetaTriangle_kernel_square_integral_volume"
end = "theorem hpThetaTriangleTestInterval_restrict_measure"

replacement = r"""theorem hpThetaTriangle_kernel_square_integral_volume :
    (∫ x in Set.Ioo (0 : ℝ) (1 / 4),
      ∫ y in Set.Ioo (0 : ℝ) (1 / 4),
        hpThetaHankelKernel x y) =
      (hpThetaTriangleMoment : ℂ) := by
  let g : ℝ → ℝ := fun x =>
    ∫ y in Set.Ioo (0 : ℝ) (1 / 4),
      hpRiemannThetaDifferentialKernel (x + y)
  have hrow (x : ℝ) :
      (∫ y in Set.Ioo (0 : ℝ) (1 / 4),
        hpThetaHankelKernel x y) =
      Complex.ofReal (g x) := by
    exact integral_ofReal
      (𝕜 := ℂ)
      (μ := volume.restrict (Set.Ioo (0 : ℝ) (1 / 4)))
      (f := fun y : ℝ =>
        hpRiemannThetaDifferentialKernel (x + y))
  have houter :
      (∫ x in Set.Ioo (0 : ℝ) (1 / 4),
        Complex.ofReal (g x)) =
      Complex.ofReal
        (∫ x in Set.Ioo (0 : ℝ) (1 / 4), g x) := by
    exact integral_ofReal
      (𝕜 := ℂ)
      (μ := volume.restrict (Set.Ioo (0 : ℝ) (1 / 4)))
      (f := g)
  have hreal :
      (∫ x in Set.Ioo (0 : ℝ) (1 / 4), g x) =
      hpThetaTriangleMoment :=
    hpThetaTriangle_phi_square_integral_eq_moment
  calc
    (∫ x in Set.Ioo (0 : ℝ) (1 / 4),
      ∫ y in Set.Ioo (0 : ℝ) (1 / 4),
        hpThetaHankelKernel x y) =
      ∫ x in Set.Ioo (0 : ℝ) (1 / 4),
        Complex.ofReal (g x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hrow
    _ = Complex.ofReal
        (∫ x in Set.Ioo (0 : ℝ) (1 / 4), g x) := houter
    _ = Complex.ofReal hpThetaTriangleMoment :=
      congrArg Complex.ofReal hreal

"""

updates = []
for p in paths:
    if not p.is_file():
        raise SystemExit(f"STOP: missing file: {p}")
    original = p.read_bytes()
    text = original.decode("utf-8")
    newline = "\r\n" if "\r\n" in text else "\n"
    normalized = text.replace("\r\n", "\n")

    if normalized.count(start) != 1 or normalized.count(end) != 1:
        raise SystemExit(f"STOP: {p}: theorem markers are not unique")

    a = normalized.index(start)
    b = normalized.index(end, a)
    repaired = normalized[:a] + replacement + normalized[b:]

    if newline == "\r\n":
        repaired = repaired.replace("\n", "\r\n")

    updates.append((p, original, repaired.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for p, original, repaired in updates:
    backup = p.with_name(p.name + ".before_cast_v2_" + stamp)
    backup.write_bytes(original)
    p.write_bytes(repaired)
    print("BACKUP:", backup)
    print("REPAIRED:", p)
PY

mkdir -p stage4_fourth_certificate_build_logs
log=stage4_fourth_certificate_build_logs/triangle_bridge_cast_v2.log

if lake build HodgeProofHP.Stage4ThetaTriangleRayleighBridge >"$log" 2>&1; then
    tail -n 50 "$log"
    echo "PASS: Stage4ThetaTriangleRayleighBridge"
else
    tail -n 110 "$log"
    echo "STOP: build failed; log: $log"
    exit 1
fi
