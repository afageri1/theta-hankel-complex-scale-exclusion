#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelAdjointSquarePairing.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_adjoint_square_pairing.sh"),
]

replacements = [
    (
        "    inner_self_eq_norm_sq_to_K]\n",
        "    inner_self_eq_norm_sq_to_K]\n"
        "  simp only [Complex.ofReal_pow]\n",
    ),
    (
        "  rw [hpThetaHankelAdjointSquare_inner]\n"
        "  simp\n\n"
        "theorem hpThetaHankelAdjointSquare_inner_im",
        "  rw [hpThetaHankelAdjointSquare_inner]\n"
        "  simp only [← Complex.ofReal_pow, Complex.ofReal_re]\n\n"
        "theorem hpThetaHankelAdjointSquare_inner_im",
    ),
    (
        "  rw [hpThetaHankelAdjointSquare_inner]\n"
        "  simp\n\n"
        "theorem hpThetaHankelAdjointSquare_inner_re_nonneg",
        "  rw [hpThetaHankelAdjointSquare_inner]\n"
        "  simp only [← Complex.ofReal_pow, Complex.ofReal_im]\n\n"
        "theorem hpThetaHankelAdjointSquare_inner_re_nonneg",
    ),
]

updates = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    raw = path.read_bytes()
    newline = "\r\n" if b"\r\n" in raw else "\n"
    text = raw.decode("utf-8").replace("\r\n", "\n")
    for old, new in replacements:
        if new in text:
            continue
        if text.count(old) != 1:
            raise SystemExit(
                f"STOP: expected exactly one repair location in {path}"
            )
        text = text.replace(old, new, 1)
    data = text.replace("\n", newline).encode("utf-8")
    if data != raw:
        updates.append((path, data))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, data in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    shutil.copy2(path, backup)
    path.write_bytes(data)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_adjoint_square_pairing.sh
