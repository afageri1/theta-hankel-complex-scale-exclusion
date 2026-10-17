#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-cnv-strict-moment-comparison-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVStrictMomentComparison
lake env lean HodgeProofHP/Stage7ThetaJensenCNVStrictMomentComparison.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_integral_pos_of_pos_on_Ioi \
  --expect HodgeProofHP.hpThetaCNV_strict_integral_comparison \
  --expect HodgeProofHP.hpThetaCNVScore_eq_kernel_ratio \
  --expect HodgeProofHP.hpThetaCNVScore_pos \
  --expect HodgeProofHP.hpThetaCNVScore_strictMonoOn \
  --expect HodgeProofHP.hpThetaCNVScore_weighted_integral_comparison
echo "PASS: strict integral comparison on the unbounded positive half-line"
echo "PASS: actual negative logarithmic slope is positive and strictly increasing"
echo "Score-weighted moment identities, normalized moment log concavity and general Turan remain unproved"
