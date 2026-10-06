#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3GaussianEigenApiAudit.lean <<'LEAN'
import HodgeProofHP.Stage3GaussianL2Domain
import HodgeProofHP.Stage3HarmonicActionAE
import HodgeProofHP.Stage3GaussianPointwiseAction

/-! Exact declarations needed for the Gaussian eigenvalue proof. -/

#check HodgeProofHP.hpRealGaussian_harmonic_pointwise
#check HodgeProofHP.hpSchwartzSecondDeriv_apply
#check HodgeProofHP.hpSchwartzQuadraticMul_apply
#check HodgeProofHP.hpHarmonicCoreOperator_apply_ae
#check HodgeProofHP.hpHarmonicCoreOperator_apply
#check HodgeProofHP.hpGaussianGroundL2_apply_ae
#check HodgeProofHP.hpGaussianGroundL2_eq_schwartz
#check HodgeProofHP.hpGaussianGroundL2_mem_harmonic_domain
LEAN

lake env lean HodgeProofHP/Stage3GaussianEigenApiAudit.lean

printf '\n=== Harmonic action definitions ===\n'
sed -n '1,85p' HodgeProofHP/Stage3HarmonicActionAE.lean

printf '\n=== Pointwise Gaussian equation ===\n'
sed -n '1,85p' HodgeProofHP/Stage3GaussianPointwiseAction.lean
