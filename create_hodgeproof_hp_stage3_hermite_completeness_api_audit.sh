#!/usr/bin/env bash
set -euo pipefail

for file in \
  HodgeProofHP/Stage3HermiteNonzero.lean \
  create_hodgeproof_hp_stage3_hermite_nonzero.sh
do
  sed -i '/^[[:space:]]*change hpSchwartzToL2 hpComplexGaussianSchwartz = 0$/d' "$file"
done

lake env lean HodgeProofHP/Stage3HermiteNonzero.lean
lake build HodgeProofHP.Stage3HermiteNonzero

cat > HodgeProofHP/Stage3HermiteCompletenessApiAudit.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteNonzero

/-!
Audit the current Hermite family and the span interface.
No completeness or density theorem is asserted.
-/

namespace HodgeProofHP

#print hpHermiteSchwartz
#print hpHermiteL2
#print hpSchwartzToL2
#check hpHermiteSchwartz_succ_apply
#check hpHermiteSchwartz_eigen
#check hpHermiteL2_ne_zero
#check Submodule.span

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HermiteCompletenessApiAudit.lean
lake build HodgeProofHP.Stage3HermiteCompletenessApiAudit

printf '\n=== Hermite-related Mathlib files ===\n'
rg --files .lake/packages/mathlib/Mathlib \
  | rg -i 'hermite' || true

printf '\n=== Hermite and polynomial-Gaussian declarations ===\n'
rg -n -i \
  'hermite|polynomial.{0,60}gaussian|gaussian.{0,60}polynomial' \
  .lake/packages/mathlib/Mathlib/Analysis \
  .lake/packages/mathlib/Mathlib/MeasureTheory \
  .lake/packages/mathlib/Mathlib/Probability \
  | head -100 || true

printf '\n=== Polynomial density and completeness candidates ===\n'
rg -n -i \
  '(dense|complete|total).{0,80}(polynomial|gaussian)|(polynomial|gaussian).{0,80}(dense|complete|total)' \
  .lake/packages/mathlib/Mathlib/Analysis \
  .lake/packages/mathlib/Mathlib/MeasureTheory \
  | head -100 || true
