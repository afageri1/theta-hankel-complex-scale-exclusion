#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-cnv-square-tail-moments-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVSquareTailMoments
lake env lean HodgeProofHP/Stage7ThetaJensenCNVSquareTailMoments.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNVTailDecayRate_pos \
  --expect HodgeProofHP.hpThetaPhiSquareTail_le_certified_constant \
  --expect HodgeProofHP.hpThetaPhiSquareTail_le_tangent_exponential \
  --expect HodgeProofHP.hpThetaPhiSquareTail_le_exponential \
  --expect HodgeProofHP.hpThetaCNV_natPower_exp_bound \
  --expect HodgeProofHP.hpThetaPhiSquareTail_natMoment_integrableOn \
  --expect HodgeProofHP.hpThetaPhiSquareTail_natMoment_truncation_tendsto
echo "PASS: positive exponential decay rate and a global square-tail exponential envelope"
echo "PASS: all natural square-tail moments are integrable and their finite truncations converge"
echo "Normalization with theta moments and general Turan inequalities remain unproved"
