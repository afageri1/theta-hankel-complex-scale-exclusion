#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cnv-weighted-tail-barrier-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVWeightedTailBarrier
lake env lean HodgeProofHP/Stage7ThetaJensenCNVWeightedTailBarrier.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNVWeightedTailBarrier_hasDerivAt \
  --expect HodgeProofHP.hpThetaCNVWeightedTailBarrier_pos \
  --expect HodgeProofHP.hpThetaCNVWeightedTailBarrier_deriv_le \
  --expect HodgeProofHP.hpThetaCNVWeightedTailBarrier_sub_tail_antitoneOn \
  --expect HodgeProofHP.hpThetaCNV_weightedTail_finite_barrier_comparison \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_tendsto_zero_atTop \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_le_explicit_barrier
echo "PASS: actual weighted tail bounded by an explicit first-Gaussian analytic barrier"
echo "Sufficient far-field comparison and global CNV positivity remain unproved"
