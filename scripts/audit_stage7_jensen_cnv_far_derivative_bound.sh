#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cnv-far-derivative-bound-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVFarDerivativeBound
lake env lean HodgeProofHP/Stage7ThetaJensenCNVFarDerivativeBound.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_sixth_growth \
  --expect HodgeProofHP.hpThetaCNV_exp_thirtyNine_fourths_lower \
  --expect HodgeProofHP.hpThetaCNV_farDerivativeRatio_bounds \
  --expect HodgeProofHP.hpThetaCNV_farDerivativeRatio_quotient_le \
  --expect HodgeProofHP.hpThetaCNV_negDerivativeTerm_le_geometric \
  --expect HodgeProofHP.hpThetaCNV_derivative_remainder_le \
  --expect HodgeProofHP.hpThetaPhi_abs_deriv_le_first_add_remainder_on_far
echo "PASS: quantitative derivative remainder bounded by explicit Gaussian amplitude / 250"
echo "Weighted-tail comparison and global CNV positivity remain unproved"
