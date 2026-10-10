#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-hurwitz-disk-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenHurwitzDisk
lake env lean HodgeProofHP/Stage7ThetaJensenHurwitzDisk.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpComplexDisk_norm_lower_bound \
  --expect HodgeProofHP.hpComplexDisk_uniformLimit_ne_zero
