#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-sixth-moment-certified-axioms.log
bash scripts/prepare_stage5_jensen_batches.sh
lake build HodgeProofHP.Stage7ThetaJensenSixthMomentCertifiedBounds
lake env lean HodgeProofHP/Stage7ThetaJensenSixthMomentCertifiedBounds.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensen_sixthBatchIntegral_of_kernelBounds \
  --expect HodgeProofHP.hpThetaJensen_sixthBatchIntegral_bounds \
  --expect HodgeProofHP.hpThetaJensen_sixthFiniteIntegral_bounds \
  --expect HodgeProofHP.hpThetaJensen_sixthMoment_integral_split \
  --expect HodgeProofHP.hpThetaJensen_sixthMoment_ge_certified \
  --expect HodgeProofHP.hpThetaJensen_sixthMoment_le_certified \
  --expect HodgeProofHP.hpThetaJensen_sixthMoment_certified_bounds
