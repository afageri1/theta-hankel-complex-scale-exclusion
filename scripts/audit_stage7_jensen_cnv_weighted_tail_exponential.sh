#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-cnv-weighted-tail-exponential-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVWeightedTailExponential
lake env lean HodgeProofHP/Stage7ThetaJensenCNVWeightedTailExponential.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_farKernelRatio_bounds \
  --expect HodgeProofHP.hpThetaCNV_farKernelCoefficient_pos \
  --expect HodgeProofHP.hpThetaCNV_kernelTerm_le_frozen_geometric \
  --expect HodgeProofHP.hpThetaPhi_le_frozen_firstTerm_upper \
  --expect HodgeProofHP.hpThetaCNVFrozenTailBarrier_hasDerivAt \
  --expect HodgeProofHP.hpThetaCNVFrozenTailBarrier_pos \
  --expect HodgeProofHP.hpThetaCNVFrozenTailBarrier_deriv_le \
  --expect HodgeProofHP.hpThetaCNVFrozenTailBarrier_sub_tail_antitoneOn \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_le_frozen_barrier \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_le_dynamic_geometric_barrier
echo "PASS: actual weighted tail bounded by a first-Gaussian barrier with a decaying geometric coefficient"
echo "Sufficient far-field comparison and global CNV positivity remain unproved"
