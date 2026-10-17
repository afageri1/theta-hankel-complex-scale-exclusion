#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

lake build HodgeProofHP.Stage7ThetaJensenCNVGeneralTuran
SCORE_LOG=stage7-jensen-cnv-score-moments-axioms.log
lake env lean HodgeProofHP/Stage7ThetaJensenCNVScoreMoments.lean 2>&1 | tee "$SCORE_LOG"
python scripts/check_axioms.py "$SCORE_LOG" \
  --expect HodgeProofHP.hpThetaCNV_sqrtKernel_substitution_factor \
  --expect HodgeProofHP.hpThetaCNV_sqrtKernelMoment_integrableOn \
  --expect HodgeProofHP.hpThetaCNV_sqrtKernelMoment_integral \
  --expect HodgeProofHP.hpThetaCNVScore_halfWeight_eq \
  --expect HodgeProofHP.hpThetaCNVScore_halfWeight_integrableOn \
  --expect HodgeProofHP.hpThetaCNVScore_halfWeight_integral \
  --expect HodgeProofHP.hpThetaCNV_halfWeight_mul_x \
  --expect HodgeProofHP.hpThetaCNVHalfMoment_strict_inequality

LOG=stage7-jensen-cnv-general-turan-axioms.log
lake env lean HodgeProofHP/Stage7ThetaJensenCNVGeneralTuran.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNVNormalizedHalfMoment_strict_inequality \
  --expect HodgeProofHP.hpThetaJensen_strictTuran_positiveShift \
  --expect HodgeProofHP.hpThetaJensen_strictTuran_zeroShift \
  --expect HodgeProofHP.hpThetaJensen_strictTuran_allShifts
echo "PASS: actual score-weighted moments and strict normalized half-moment inequalities"
echo "PASS: strict Turan inequalities at every natural Jensen shift, including zero"
echo "PASS: 12 complete axiom reports across score moments and general Turan"
echo "Hyperbolicity in unbounded Jensen degrees and RH are not proved by this audit"
