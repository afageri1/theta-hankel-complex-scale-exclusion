#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-uniform-convergence-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenUniformConvergence
lake env lean HodgeProofHP/Stage7ThetaJensenUniformConvergence.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenDiskError_nonneg \
  --expect HodgeProofHP.hpThetaJensenDiskError_le_majorant \
  --expect HodgeProofHP.hpThetaJensenDiskError_tendsto \
  --expect HodgeProofHP.hpThetaJensenDiskError_tsum_tendsto \
  --expect HodgeProofHP.hpThetaJensenRescaledPolynomialValue_eq_tsum \
  --expect HodgeProofHP.hpThetaJensenRescaledTerm_error_norm_le_disk \
  --expect HodgeProofHP.hpThetaJensenRescaledPolynomialValue_error_le \
  --expect HodgeProofHP.hpThetaJensenRescaledPolynomialValue_tendstoUniformlyOn_disk
