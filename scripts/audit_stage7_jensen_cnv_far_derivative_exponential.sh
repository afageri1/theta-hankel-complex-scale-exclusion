#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=stage7-jensen-cnv-far-derivative-exponential-axioms.log
lake build HodgeProofHP.Stage7ThetaJensenCNVFarDerivativeExponential
lake env lean HodgeProofHP/Stage7ThetaJensenCNVFarDerivativeExponential.lean 2>&1 | tee "$LOG"
python scripts/check_axioms.py "$LOG" \
  --expect HodgeProofHP.hpThetaCNV_derivative_remainder_le_geometric \
  --expect HodgeProofHP.hpThetaCNV_farDerivativeRatio_quotient_le_mul_ratio \
  --expect HodgeProofHP.hpThetaCNV_farDerivative_geometric_amplitude_eq \
  --expect HodgeProofHP.hpThetaCNV_derivative_remainder_le_explicit_exponential \
  --expect HodgeProofHP.hpThetaPhi_abs_deriv_le_first_add_exponential_on_far
echo "PASS: far derivative remainder retains explicit exp(-4*pi*exp(2*t)) decay"
echo "Refined weighted-tail comparison and global CNV positivity remain unproved"
