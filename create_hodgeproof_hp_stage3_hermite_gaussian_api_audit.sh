#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3HermiteGaussianApiAudit.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteNonzero
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
Audit the Gaussian convention before identifying the project's
creation-operator family with Mathlib Hermite polynomials.
No completeness theorem is asserted.
-/

namespace HodgeProofHP

#print hpGaussianGroundFunction
#check hpComplexGaussianSchwartz_apply
#check hpHermiteSchwartz_succ_apply

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HermiteGaussianApiAudit.lean
lake build HodgeProofHP.Stage3HermiteGaussianApiAudit

printf '\n=== Mathlib Hermite Basic source ===\n'
cat .lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Hermite/Basic.lean

printf '\n=== Mathlib Hermite Gaussian source ===\n'
cat .lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Hermite/Gaussian.lean
