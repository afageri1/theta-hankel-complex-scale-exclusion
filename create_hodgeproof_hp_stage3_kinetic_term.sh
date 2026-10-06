#!/usr/bin/env bash
set -euo pipefail

file="HodgeProofHP/Stage3SchwartzKineticTerm.lean"

if [[ ! -f HodgeProofHP/Stage3SchwartzFoundation.lean ]]; then
  echo "STOP: run from the hodgeproof-hp repository root."
  exit 1
fi

if [[ -e "$file" ]]; then
  echo "STOP: $file already exists; no file was replaced."
  exit 1
fi

cat > "$file" <<'LEAN'
import HodgeProofHP.Stage3SchwartzFoundation

/-! Stage 3.2: the kinetic term on Schwartz functions. -/

namespace HodgeProofHP

/-- The map f ↦ -f'' from complex Schwartz functions into HPSpace. -/
noncomputable def hpSchwartzKineticToL2 :
    SchwartzMap ℝ ℂ →L[ℂ] HPSpace :=
  -(hpSchwartzToL2.comp hpSchwartzSecondDeriv)

#check hpSchwartzKineticToL2
#print axioms hpSchwartzKineticToL2

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage3SchwartzKineticTerm
lake env lean "$file"
