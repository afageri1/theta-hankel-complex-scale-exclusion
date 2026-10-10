#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-polynomial-expansion-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenPolynomialExpansion
lake env lean HodgeProofHP/Stage7ThetaJensenPolynomialExpansion.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenRescaledPolynomialValue_eq_sum \
  --expect HodgeProofHP.hpThetaJensenRescaledTerm_eq_zero_of_lt \
  --expect HodgeProofHP.hpThetaJensenRescaledTerm_tendsto \
  --expect HodgeProofHP.hpThetaJensenRescaledTerm_norm \
  --expect HodgeProofHP.hpThetaJensenDiskMajorant_nonneg \
  --expect HodgeProofHP.hpThetaJensenRescaledTerm_norm_le_disk \
  --expect HodgeProofHP.hpThetaJensenDiskMajorant_summable
