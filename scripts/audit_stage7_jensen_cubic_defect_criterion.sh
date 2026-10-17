#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-cubic-defect-criterion-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCubicDefectCriterion
lake env lean HodgeProofHP/Stage7ThetaJensenCubicDefectCriterion.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenTuranDefect_pos \
  --expect HodgeProofHP.hpThetaJensenTuranDefect_lt_one \
  --expect HodgeProofHP.hpCubicDefectMargin_pos_of_bounds \
  --expect HodgeProofHP.hpThetaJensenHigherTuranGap_eq_defectMargin \
  --expect HodgeProofHP.hpThetaJensenHigherTuranGap_pos_of_defect_bounds \
  --expect HodgeProofHP.hpThetaJensenCubic_root_im_zero_of_defect_bounds
echo "PASS: actual normalized Turan defects lie strictly between zero and one"
echo "PASS: an exact defect identity and quantitative sufficient condition imply cubic real zeros"
echo "The quarter bounds and squared step bound remain unproved for all theta shifts"
echo "Unbounded good Jensen degrees and RH remain unproved"
