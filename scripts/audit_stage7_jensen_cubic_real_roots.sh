#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cubic-real-roots-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCubicRealRoots
lake env lean HodgeProofHP/Stage7ThetaJensenCubicRealRoots.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpContinuous_exists_zero_Ioo_of_neg_pos \
  --expect HodgeProofHP.hpContinuous_exists_zero_Ioo_of_pos_neg \
  --expect HodgeProofHP.hpThetaJensenCubic_exists_root_neg90_neg55 \
  --expect HodgeProofHP.hpThetaJensenCubic_exists_root_neg55_neg42 \
  --expect HodgeProofHP.hpThetaJensenCubic_exists_root_neg42_neg15 \
  --expect HodgeProofHP.hpThetaJensenCubic_three_distinct_real_roots
echo "PASS: three distinct real cubic roots; all dependencies allowed"
