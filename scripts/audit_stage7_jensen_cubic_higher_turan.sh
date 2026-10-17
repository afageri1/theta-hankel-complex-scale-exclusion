#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-cubic-higher-turan-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCubicHigherTuran
lake env lean HodgeProofHP/Stage7ThetaJensenCubicHigherTuran.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenPolynomial_three_allShifts \
  --expect HodgeProofHP.hpThetaJensenShiftedCubic_toPoly \
  --expect HodgeProofHP.hpThetaJensenTuranGap_pos \
  --expect HodgeProofHP.hpThetaJensenCrossGap_balance \
  --expect HodgeProofHP.hpThetaJensenCrossGap_pos \
  --expect HodgeProofHP.hpThetaJensenShiftedCubic_discr_eq_higherGap \
  --expect HodgeProofHP.hpThetaJensenShiftedCubic_discr_pos_iff \
  --expect HodgeProofHP.hpThetaJensenShiftedCubic_zero \
  --expect HodgeProofHP.hpThetaJensen_adjacentTuran_not_sufficient
echo "PASS: shifted cubic discriminant equals 27 times the higher Turan gap"
echo "PASS: adjacent and cross gaps are positive at every natural shift"
echo "PASS: a rational counterexample separates adjacent Turan from cubic discriminant positivity"
echo "Higher-gap positivity, cubic hyperbolicity at all shifts and unbounded good degrees remain unproved"
