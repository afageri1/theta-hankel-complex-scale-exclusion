#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-turan-moment-equivalence-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenTuranMomentEquivalence
lake env lean HodgeProofHP/Stage7ThetaJensenTuranMomentEquivalence.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaJensenMomentScale_pos \
  --expect HodgeProofHP.hpThetaJensenGamma_succ_momentScale \
  --expect HodgeProofHP.hpThetaJensenGamma_add_two_momentScale \
  --expect HodgeProofHP.hpThetaJensenTuranMomentScale_pos \
  --expect HodgeProofHP.hpThetaJensen_turanGap_eq_momentGap \
  --expect HodgeProofHP.hpThetaJensen_strictTuran_iff_momentInequality
echo "PASS: algebraic Turan moment equivalence; general inequality remains unproved"
