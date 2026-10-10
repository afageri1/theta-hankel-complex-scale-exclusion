#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import re

paths = [Path("HodgeProofHP/Stage4ThetaKernelFirstTermUpper.lean")]
creator = Path("create_hodgeproof_hp_stage4_theta_kernel_first_term_upper.sh")
if creator.is_file():
    paths.append(creator)

pattern = re.compile(
    r"^[ \t]*have hw :\n"
    r"[\s\S]*?"
    r"^[ \t]*convert h using 1 <;> dsimp \[m\] <;> ring",
    re.MULTILINE,
)

replacement = """\
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

updates = []
for path in paths:
    with path.open("r", encoding="utf-8", newline="") as f:
        original = f.read()
    newline = "\r\n" if "\r\n" in original else "\n"
    text = original.replace("\r\n", "\n")
    count = len(list(pattern.finditer(text)))
    if count != 1:
        raise SystemExit(
            f"STOP: {path}: expected one repair block, found {count}; "
            "no files changed"
        )
    repaired = pattern.sub(lambda _: replacement, text)
    updates.append((path, original, repaired.replace("\n", newline)))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, repaired in updates:
    backup = path.with_name(path.name + ".before_indent_repair_" + stamp)
    with backup.open("w", encoding="utf-8", newline="") as f:
        f.write(original)
    with path.open("w", encoding="utf-8", newline="") as f:
        f.write(repaired)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

mkdir -p stage4_fourth_certificate_build_logs
log="stage4_fourth_certificate_build_logs/kernel_upper_indent_repair.log"

if lake build HodgeProofHP.Stage4ThetaKernelFirstTermUpper >"$log" 2>&1; then
  tail -n 35 "$log"
  printf '%s\n' 'PASS: Stage4ThetaKernelFirstTermUpper'
else
  tail -n 100 "$log"
  printf 'STOP: build failed; log: %s\n' "$log"
  exit 1
fi
