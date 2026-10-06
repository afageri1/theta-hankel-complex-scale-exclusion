#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4RiemannXiRealZeroCriterion.lean"),
    Path("create_hodgeproof_hp_stage4_riemann_xi_real_zero_criterion.sh"),
]

replacements = [
    (
        "  norm_num [Complex.mul_re]\n",
        "  norm_num [Complex.mul_re, sub_eq_add_neg]\n",
    ),
    (
        "  apply Complex.ext <;>\n"
        "    norm_num [Complex.mul_re, Complex.mul_im] <;> ring\n",
        "  apply Complex.ext <;>\n"
        "    norm_num [Complex.mul_re, Complex.mul_im]\n",
    ),
    (
        "  norm_num [Complex.mul_im] <;> ring\n",
        "  norm_num [Complex.mul_im]\n",
    ),
]

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    content = path.read_bytes().decode("utf-8")
    newline = "\r\n" if "\r\n" in content else "\n"
    for old, new in replacements:
        old = old.replace("\n", newline)
        new = new.replace("\n", newline)
        count = content.count(old)
        if count != 1:
            raise SystemExit(
                f"STOP: expected one matching block in {path}; found {count}"
            )
        content = content.replace(old, new, 1)
    prepared.append((path, content))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, _ in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    shutil.copy2(path, backup)
    print(f"BACKUP: {backup}")

for path, content in prepared:
    path.write_bytes(content.encode("utf-8"))
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_riemann_xi_real_zero_criterion.sh
