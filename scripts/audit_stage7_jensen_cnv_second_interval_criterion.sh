#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cnv-second-interval-criterion-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVSecondIntervalCriterion
lake env lean HodgeProofHP/Stage7ThetaJensenCNVSecondIntervalCriterion.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNVSecondFactor_lower_of_le \
  --expect HodgeProofHP.hpThetaCNVSecondFactor_interval_lower \
  --expect HodgeProofHP.hpThetaCNV_secondDerivative_firstTerm_interval_lower \
  --expect HodgeProofHP.hpThetaCNV_secondDerivative_rational_interval_certificate
echo "PASS: correlated second-derivative interval criterion; numerical coverage of [0, 1/50] remains unproved"
