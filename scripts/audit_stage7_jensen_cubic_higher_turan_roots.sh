#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-cubic-higher-turan-roots-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCubicHigherTuranRoots
lake env lean HodgeProofHP/Stage7ThetaJensenCubicHigherTuranRoots.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpRealCubic_root_im_zero_of_discr_pos \
  --expect HodgeProofHP.hpThetaJensenCubic_evalComplex_allShifts \
  --expect HodgeProofHP.hpThetaJensenCubic_root_im_zero_of_higherGap \
  --expect HodgeProofHP.hpThetaJensenCubic_eval_pos_of_nonneg_allShifts \
  --expect HodgeProofHP.hpThetaJensenCubic_real_root_neg_allShifts \
  --expect HodgeProofHP.hpThetaJensenCubic_allShifts_realZeros_of_higherGaps
echo "PASS: positive real cubic discriminant excludes all nonreal complex zeros"
echo "PASS: positive higher Turan gap implies real zeros at the corresponding shift"
echo "PASS: every real shifted cubic Jensen zero is negative"
echo "Higher-gap positivity at all shifts and unbounded good degrees remain unproved"
