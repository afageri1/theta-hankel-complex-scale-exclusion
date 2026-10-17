#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-density-curvature-cell-criterion-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenDensityCurvatureCellCriterion
lake env lean HodgeProofHP/Stage7ThetaJensenDensityCurvatureCellCriterion.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaDensityCell_secondTerm_le_geometric \
  --expect HodgeProofHP.hpThetaDensityCell_second_remainder_le \
  --expect HodgeProofHP.hpThetaDensityCell_scaled_second_deriv_le \
  --expect HodgeProofHP.hpThetaDensityCell_interval_pos_of_bounds \
  --expect HodgeProofHP.hpThetaDensityCell_pilot_remainder_le
echo "PASS: 5 complete axiom reports; all dependencies allowed"
echo "PASS: reusable signed infinite second derivative remainder A*r/(1-r)"
echo "PASS: interval density curvature criterion retains signed first-term bounds"
echo "PASS: generic remainder specializes to the certified pilot bound"
echo "Numerical coverage outside the endpoint and pilot intervals remains unproved"
echo "Global density log concavity and all-shift cubic hyperbolicity remain unproved"
