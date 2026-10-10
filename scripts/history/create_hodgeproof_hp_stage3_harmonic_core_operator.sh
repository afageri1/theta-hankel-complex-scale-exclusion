#!/usr/bin/env bash
set -euo pipefail

file=HodgeProofHP/Stage3HarmonicCoreOperator.lean
if [[ -e "$file" ]]; then
  echo "File already exists: $file" >&2
  exit 1
fi

cat > "$file" <<'LEAN'
import HodgeProofHP.Stage3HarmonicCoreProperties

/-! The harmonic oscillator restricted to the Schwartz domain. -/

namespace HodgeProofHP

noncomputable def hpSchwartzCoreEquiv :
    SchwartzMap ℝ ℂ ≃ₗ[ℂ] HPSchwartzDomain :=
  LinearEquiv.ofInjective
    hpSchwartzToL2.toLinearMap hpSchwartzToL2_injective

noncomputable def HPHarmonicCoreOperator :
    HPSpace →ₗ.[ℂ] HPSpace where
  domain := HPSchwartzDomain
  toFun :=
    hpSchwartzHarmonicToL2.toLinearMap.comp
      hpSchwartzCoreEquiv.symm.toLinearMap

theorem hpHarmonicCoreOperator_apply (f : SchwartzMap ℝ ℂ) :
    HPHarmonicCoreOperator.toFun (hpSchwartzCoreEquiv f) =
      hpSchwartzHarmonicToL2 f := by
  simp [HPHarmonicCoreOperator]

#check HPHarmonicCoreOperator
#check hpHarmonicCoreOperator_apply
#print axioms HPHarmonicCoreOperator
#print axioms hpHarmonicCoreOperator_apply

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage3HarmonicCoreOperator
