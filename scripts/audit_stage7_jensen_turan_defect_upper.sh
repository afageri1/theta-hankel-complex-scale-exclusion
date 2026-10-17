#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-turan-defect-upper-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenTuranDefectUpper
lake env lean HodgeProofHP/Stage7ThetaJensenTuranDefectUpper.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaPhiEvenMoment_pos_all \
  --expect HodgeProofHP.hpThetaPhiEvenMoment_variance_nonneg \
  --expect HodgeProofHP.hpThetaPhiEvenMoment_logConvex \
  --expect HodgeProofHP.hpThetaJensenGamma_weighted_logConvex \
  --expect HodgeProofHP.hpThetaJensenTuranDefect_le_reciprocal \
  --expect HodgeProofHP.hpThetaJensenTuranDefect_le_quarter_of_three_le \
  --expect HodgeProofHP.hpThetaJensenCubic_root_im_zero_of_step_bound
echo "PASS: actual even moments are positive and log-convex by an integrated square"
echo "PASS: actual Turan defects are at most 2/(2n+3) at every natural shift"
echo "PASS: the quarter bound is unconditional for every shift n >= 3"
echo "The squared step bound, cubic hyperbolicity at all shifts and unbounded good degrees remain unproved"
