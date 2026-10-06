#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelQLowerBound.lean"),
    Path("create_hodgeproof_hp_stage4_theta_q_lower_bound.sh"),
]

old1 = """  simpa only [Function.comp_def, Complex.reCLM_apply,
    inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow,
    Complex.ofReal_re, LinearIsometryEquiv.norm_map] using h"""

new1 = """  simpa only [Function.comp_def, Complex.reCLM_apply,
    inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    LinearIsometryEquiv.norm_map] using h"""

old2 = """  simp [inner_smul_left]"""

new2 = """  rw [inner_smul_left_eq_smul]
  change
    (i.1.re : ℂ) * inner ℂ (hpThetaHankelSpectralBasis i) f =
      (i.1.re : ℂ) * inner ℂ (hpThetaHankelSpectralBasis i) f
  rfl"""

prepared = []
for p in paths:
    if not p.is_file():
        raise SystemExit(f"STOP: missing {p}")
    raw = p.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    for label, old in [("Parseval", old1), ("real scalar", old2)]:
        count = text.count(old)
        if count != 1:
            raise SystemExit(
                f"STOP: {p}: expected one {label} block, found {count}"
            )
    fixed = text.replace(old1, new1).replace(old2, new2)
    newline = "\r\n" if b"\r\n" in raw else "\n"
    prepared.append((p, fixed.replace("\n", newline).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for p, data in prepared:
    backup = p.with_name(p.name + ".before_q_repair_" + stamp)
    shutil.copy2(p, backup)
    p.write_bytes(data)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {p}")
PY

mkdir -p stage4_fourth_certificate_build_logs
log="stage4_fourth_certificate_build_logs/q_lower_bound_repair.log"

if lake build HodgeProofHP.Stage4ThetaHankelQLowerBound >"$log" 2>&1; then
    tail -n 55 "$log"
    echo "PASS: Stage4ThetaHankelQLowerBound"
else
    tail -n 100 "$log"
    echo "STOP: build failed; log: $log"
    exit 1
fi
