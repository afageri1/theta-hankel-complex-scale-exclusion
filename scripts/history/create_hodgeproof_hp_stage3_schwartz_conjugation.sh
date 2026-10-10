#!/usr/bin/env bash
set -euo pipefail

file=HodgeProofHP/Stage3SchwartzConjugation.lean
if [[ -e "$file" ]]; then
  echo "File already exists: $file" >&2
  exit 1
fi

cat > "$file" <<'LEAN'
import HodgeProofHP.Stage3SecondDerivativeIntegrationByParts

/-! Complex conjugation preserves the real vector space of Schwartz maps. -/

namespace HodgeProofHP

noncomputable def hpSchwartzConj :
    SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap

theorem hpSchwartzConj_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (hpSchwartzConj f) x = (starRingEnd ℂ) (f x) := by
  simp [hpSchwartzConj]

#check hpSchwartzConj
#print axioms hpSchwartzConj_apply

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage3SchwartzConjugation
