#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cubic-factorization-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCubicFactorization
lake env lean HodgeProofHP/Stage7ThetaJensenCubicFactorization.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpRealCubic_factor_of_three_roots \
  --expect HodgeProofHP.hpThetaJensenGamma_three_pos \
  --expect HodgeProofHP.hpThetaJensenCubic_exists_real_factorization \
  --expect HodgeProofHP.hpThetaJensenCubic_complex_zero_iff_of_factorization \
  --expect HodgeProofHP.hpThetaJensenCubic_all_complex_zeros_real
echo "PASS: cubic factorization and all complex zeros real; all dependencies allowed"
