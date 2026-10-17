#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-cnv-tail-moment-identity-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVTailMomentIdentity
lake env lean HodgeProofHP/Stage7ThetaJensenCNVTailMomentIdentity.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_squareSubstitution_factor \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_natMoment_integrableOn \
  --expect HodgeProofHP.hpThetaCNV_tailMomentProduct_hasDerivAt \
  --expect HodgeProofHP.hpThetaCNV_tailMomentProduct_derivative_integrableOn \
  --expect HodgeProofHP.hpThetaCNV_tailMomentProduct_tendsto_zero \
  --expect HodgeProofHP.hpThetaPhiWeightedTail_natMoment_eq \
  --expect HodgeProofHP.hpThetaPhiSquareTail_rpowMoment_substitution \
  --expect HodgeProofHP.hpThetaPhiSquareTail_halfMoment_eq_evenMoment
echo "PASS: all natural weighted-tail moments are integrable; polynomial boundary terms vanish"
echo "PASS: actual half-integer square-tail moment equals 4/(2n+1) times theta moment n+1"
echo "Normalized moment comparison, general Turan inequalities and unbounded good degrees remain unproved"
