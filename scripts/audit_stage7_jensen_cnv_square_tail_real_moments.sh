#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-cnv-square-tail-real-moments-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVSquareTailRealMoments
lake env lean HodgeProofHP/Stage7ThetaJensenCNVSquareTailRealMoments.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_rpow_exp_integrableOn \
  --expect HodgeProofHP.hpThetaCNV_rpow_exp_integral \
  --expect HodgeProofHP.hpThetaPhiSquareTail_rpowMoment_integrableOn \
  --expect HodgeProofHP.hpThetaPhiSquareTail_rpowMoment_truncation_tendsto \
  --expect HodgeProofHP.hpThetaPhiSquareTail_halfMoment_integrableOn
echo "PASS: real square-tail moments are integrable for every exponent p > -1"
echo "PASS: finite truncations converge; all weights x^(n-1/2) are covered"
echo "The theta-to-tail moment identity, normalized moment comparison and general Turan inequalities remain unproved"
