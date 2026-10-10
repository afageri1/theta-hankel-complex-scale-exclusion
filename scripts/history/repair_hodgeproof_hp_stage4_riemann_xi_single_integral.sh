#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4RiemannXiSingleIntegral.lean"),
    Path("create_hodgeproof_hp_stage4_riemann_xi_single_integral.sh"),
]

old = """  simpa only [hpRiemannThetaSymmetricMellinIntegrand, add_smul] using
    (hpRiemannTheta_upper_mellin_integrable (1 - s)).fun_add
      (hpRiemannTheta_upper_mellin_integrable s)"""

new = """  change IntegrableOn
    (fun x : ℝ =>
      ((x : ℂ) ^ ((1 - s) / 2 - 1) +
        (x : ℂ) ^ (s / 2 - 1)) •
          (hpRiemannThetaKernel x : ℂ))
    (Set.Ioi 1)
  simp only [add_smul]
  exact
    (hpRiemannTheta_upper_mellin_integrable (1 - s)).fun_add
      (hpRiemannTheta_upper_mellin_integrable s)"""

prepared = []

for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")

    original = path.read_bytes()
    text = original.decode("utf-8")
    newline = "\r\n" if "\r\n" in text else "\n"
    source = old.replace("\n", newline)
    replacement = new.replace("\n", newline)

    if text.count(source) != 1:
        raise SystemExit(
            f"STOP: expected one matching proof in {path}. "
            "No files changed."
        )

    prepared.append(
        (path, original, text.replace(source, replacement).encode("utf-8"))
    )

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")

for path, original, updated in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(original)
    print(f"BACKUP: {backup}")

for path, original, updated in prepared:
    path.write_bytes(updated)
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_riemann_xi_single_integral.sh
