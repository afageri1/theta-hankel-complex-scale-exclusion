#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import re

paths = [
    Path("HodgeProofHP/Stage4RiemannXiMellinSplit.lean"),
    Path("create_hodgeproof_hp_stage4_riemann_xi_mellin_split.sh"),
]
names = [
    "hpRiemannModifiedThetaKernel_of_one_lt",
    "hpRiemannModifiedThetaKernel_of_mem_Ioo",
]
prepared = []

for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")

    original = path.read_bytes()
    text = original.decode("utf-8")
    newline = "\r\n" if "\r\n" in text else "\n"

    for name in names:
        pattern = (
            r"^([ \t]*)rw[ \t]*\[[ \t\r\n]*"
            + re.escape(name)
            + r"\b"
        )
        matches = list(re.finditer(pattern, text, re.MULTILINE))
        if len(matches) != 1:
            raise SystemExit(
                f"STOP: expected one rewrite for {name} in {path}; "
                f"found {len(matches)}. No files changed."
            )

        match = matches[0]
        preceding = text[:match.start()].rstrip("\r\n").splitlines()
        if preceding and preceding[-1].strip() == "dsimp only":
            continue

        insertion = match.group(1) + "dsimp only" + newline
        text = text[:match.start()] + insertion + text[match.start():]

    prepared.append((path, original, text.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")

# Back up every file before writing any changes.
for path, original, updated in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(original)
    print(f"BACKUP: {backup}")

for path, original, updated in prepared:
    path.write_bytes(updated)
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_riemann_xi_mellin_split.sh
