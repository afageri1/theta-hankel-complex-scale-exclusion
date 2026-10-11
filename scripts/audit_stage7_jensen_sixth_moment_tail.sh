#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-sixth-moment-tail-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenSixthMomentTailBounds
lake env lean HodgeProofHP/Stage7ThetaJensenSixthMomentTailBounds.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhi_sixthMoment_integrableOn \
  --expect HodgeProofHP.hpThetaPhi_sixthMoment_nonneg \
  --expect HodgeProofHP.hpThetaJensenKernelTailRate_one_gt_six \
  --expect HodgeProofHP.hpThetaJensen_sixthPower_le_shiftedExp \
  --expect HodgeProofHP.hpThetaJensen_sixthIntegrand_le_tailEnvelope \
  --expect HodgeProofHP.hpThetaJensenSixthTailUpper_pos \
  --expect HodgeProofHP.hpThetaJensen_sixthMoment_tail_le \
  --expect HodgeProofHP.hpThetaJensenSixthTailUpper_le_twoEminusEight \
  --expect HodgeProofHP.hpThetaJensen_sixthMoment_tail_le_twoEminusEight
