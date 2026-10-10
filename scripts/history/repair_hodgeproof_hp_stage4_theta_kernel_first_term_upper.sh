#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import re

target = Path("HodgeProofHP/Stage4ThetaKernelFirstTermUpper.lean")
creator = Path("create_hodgeproof_hp_stage4_theta_kernel_first_term_upper.sh")

profile_pattern = re.compile(
    r"(  have hprofile\s*:[\s\S]*?:= by\n)"
    r"[\s\S]*?(?=  have hterm\s*:)"
)

growth_pattern = re.compile(
    r"    have h := mul_le_mul_of_nonneg_right hgrowth"
    r"[\s\S]*?nlinarith\s*\[h\]"
)

profile_body = """\
    unfold hpThetaGaussianProfile hpThetaGaussianParameter
    dsimp [b, m]
    conv_rhs =>
      rw [mul_assoc, ← Real.exp_add]
    congr 2 <;> ring
"""

growth_body = """\
    have hw :
        0 ≤ (2 * hpThetaGaussianKernelTerm Real.pi u) *
          Real.exp (-3 * Real.pi * (n : ℝ)) :=
      mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hfirst)
        (le_of_lt (Real.exp_pos _))
    have h :
        ((n : ℝ) + 1) ^ 4 *
            ((2 * hpThetaGaussianKernelTerm Real.pi u) *
              Real.exp (-3 * Real.pi * (n : ℝ))) ≤
          16 ^ n *
            ((2 * hpThetaGaussianKernelTerm Real.pi u) *
              Real.exp (-3 * Real.pi * (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hgrowth hw
    convert h using 1 <;> dsimp [m] <;> ring"""

paths = [target]
if creator.is_file():
    paths.append(creator)

updates = []
for path in paths:
    with path.open("r", encoding="utf-8", newline="") as f:
        original = f.read()
    newline = "\r\n" if "\r\n" in original else "\n"
    text = original.replace("\r\n", "\n")

    for label, pattern in [
        ("profile identity", profile_pattern),
        ("growth comparison", growth_pattern),
    ]:
        count = len(list(pattern.finditer(text)))
        if count != 1:
            raise SystemExit(
                f"STOP: {path}: expected one {label}, found {count}; "
                "no files changed"
            )

    text = profile_pattern.sub(
        lambda match: match.group(1) + profile_body, text
    )
    text = growth_pattern.sub(lambda match: growth_body, text)
    updates.append((path, original, text.replace("\n", newline)))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, repaired in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    with backup.open("w", encoding="utf-8", newline="") as f:
        f.write(original)
    with path.open("w", encoding="utf-8", newline="") as f:
        f.write(repaired)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

mkdir -p stage4_fourth_certificate_build_logs
log="stage4_fourth_certificate_build_logs/kernel_first_term_upper_repair.log"

if lake build HodgeProofHP.Stage4ThetaKernelFirstTermUpper >"$log" 2>&1; then
  tail -n 35 "$log"
  printf '%s\n' 'PASS: Stage4ThetaKernelFirstTermUpper'
else
  tail -n 100 "$log"
  printf 'STOP: build failed; log: %s\n' "$log"
  exit 1
fi
