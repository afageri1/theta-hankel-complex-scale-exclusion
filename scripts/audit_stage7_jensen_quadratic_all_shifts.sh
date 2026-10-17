#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

LOG=stage7-jensen-quadratic-all-shifts-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenQuadraticAllShifts
lake env lean HodgeProofHP/Stage7ThetaJensenQuadraticAllShifts.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenGamma_pos_allShifts \
  --expect HodgeProofHP.hpThetaJensenQuadratic_discriminant_pos_allShifts \
  --expect HodgeProofHP.hpThetaJensenQuadratic_eval_factorization_allShifts \
  --expect HodgeProofHP.hpThetaJensenQuadratic_rootMinus_lt_rootPlus_allShifts \
  --expect HodgeProofHP.hpThetaJensenQuadratic_factorization_allShifts \
  --expect HodgeProofHP.hpThetaJensenQuadratic_two_distinct_real_roots_allShifts \
  --expect HodgeProofHP.hpThetaJensenQuadratic_complex_factorization_allShifts \
  --expect HodgeProofHP.hpThetaJensenQuadratic_complex_eval_eq_zero_iff_allShifts \
  --expect HodgeProofHP.hpThetaJensenQuadratic_complex_root_im_zero_allShifts \
  --expect HodgeProofHP.hpThetaJensenQuadratic_eval_pos_of_nonneg_allShifts \
  --expect HodgeProofHP.hpThetaJensenQuadratic_real_root_neg_allShifts \
  --expect HodgeProofHP.hpThetaJensenQuadratic_complex_root_negative_real_allShifts
echo "PASS: degree-two Jensen polynomials have two distinct negative real roots at every shift"
echo "PASS: every complex zero equals one of the two real roots"
echo "The degree is fixed at two; unbounded good degrees and RH remain unproved"
