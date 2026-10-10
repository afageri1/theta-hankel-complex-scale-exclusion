#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3HermiteEigenApiAudit.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteCreationAction

/-!
API audit for the Hermite eigenvalue induction.
No eigenvalue or completeness claim is made here.
-/

namespace HodgeProofHP

#check hpSchwartzCreation_apply
#check hpHermiteSchwartz_succ_apply
#check hpSchwartzCoordinateMul_apply
#check hpSchwartzSecondDeriv_apply
#check hpSchwartzQuadraticMul_apply
#check hpHarmonicCoreOperator_apply
#check hpComplexGaussian_core_eigen_equation
#check hpGaussianGroundL2_eigen_equation
#check SchwartzMap.derivCLM_apply

#print hpSchwartzCreation
#print hpSchwartzHarmonicToL2

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HermiteEigenApiAudit.lean
lake build HodgeProofHP.Stage3HermiteEigenApiAudit

printf '\n=== Derivative product-rule candidates ===\n'
rg -n 'theorem (deriv_smul|deriv_mul|HasDerivAt.*smul|HasDerivAt.*mul)' \
  .lake/packages/mathlib/Mathlib/Analysis/Calculus \
  | sed -n '1,60p' || true
