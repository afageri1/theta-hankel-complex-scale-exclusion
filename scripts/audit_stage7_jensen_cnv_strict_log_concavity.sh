#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-cnv-strict-log-concavity-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVStrictLogConcavity
lake env lean HodgeProofHP/Stage7ThetaJensenCNVStrictLogConcavity.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhiSquareTail_log_secondDeriv_neg \
  --expect HodgeProofHP.hpThetaPhiSquareTail_log_strictConcaveOn \
  --expect HodgeProofHP.hpThetaPhiSquareTailLogSlope_strictAntiOn \
  --expect HodgeProofHP.hpThetaPhiSquareTail_log_fourPoint \
  --expect HodgeProofHP.hpThetaPhiSquareTail_fourPoint_product
echo "PASS: actual square-variable tail has strictly concave logarithm on the positive half-line"
echo "PASS: strict logarithmic slope monotonicity and equal-sum four-point product inequality"
echo "The normalized integral comparison, general Turan inequalities and unbounded good degrees remain unproved"
