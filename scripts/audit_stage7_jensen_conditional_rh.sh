#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-conditional-rh-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenConditionalRiemannHypothesis
lake env lean HodgeProofHP/Stage7ThetaJensenConditionalRiemannHypothesis.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenGeneratingFunction_punctured_ne_zero \
  --expect HodgeProofHP.hpThetaJensenGeneratingFunction_exists_nonreal_disk \
  --expect HodgeProofHP.hpThetaJensen_nonrealZeroExclusion_of_rescaledFamily \
  --expect HodgeProofHP.hpThetaJensen_rescaledFamily_of_allDegreesRealZeros \
  --expect HodgeProofHP.hpThetaJensen_RH_of_rescaledFamily \
  --expect HodgeProofHP.hpThetaJensen_RH_of_allDegreesRealZeros
