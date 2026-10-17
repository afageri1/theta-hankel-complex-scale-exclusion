#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-turan-defect-limits-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenTuranDefectLimits
lake env lean HodgeProofHP/Stage7ThetaJensenTuranDefectLimits.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenTuranDefect_tendsto_zero \
  --expect HodgeProofHP.hpThetaJensenTuranDefect_inv_ge_linear \
  --expect HodgeProofHP.hpThetaJensenTuranDefect_inv_tendsto_atTop \
  --expect HodgeProofHP.hpThetaJensenGamma_ratio_eq_one_sub_defect \
  --expect HodgeProofHP.hpThetaJensenGamma_adjacent_ratio_tendsto_one \
  --expect HodgeProofHP.hpPositiveDefect_squared_step_iff_inv_step \
  --expect HodgeProofHP.hpThetaJensenTuranDefect_step_iff_inv_step \
  --expect HodgeProofHP.hpPositiveDefect_quarter_bounds_not_sufficient
echo "PASS: actual Turan defects tend to zero and their reciprocals tend to infinity"
echo "PASS: actual adjacent normalized coefficient ratios tend to one"
echo "PASS: the squared step condition is equivalent to the absolute reciprocal step bound"
echo "PASS: positive quarter bounds alone do not imply the step condition"
echo "A uniform reciprocal step bound and unbounded good Jensen degrees remain unproved"
