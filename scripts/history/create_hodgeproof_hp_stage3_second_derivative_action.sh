#!/usr/bin/env bash
set -euo pipefail

file=HodgeProofHP/Stage3SecondDerivativeAction.lean
if [[ -e "$file" ]]; then
  echo "File already exists: $file" >&2
  exit 1
fi

cat > "$file" <<'LEAN'
import HodgeProofHP.Stage3HarmonicCoreSpec

/-! Pointwise identification of the second Schwartz derivative. -/

namespace HodgeProofHP

theorem hpSchwartzSecondDeriv_apply
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (hpSchwartzSecondDeriv f) x =
      deriv (deriv (f : ℝ → ℂ)) x := by
  change ((SchwartzMap.derivCLM ℂ ℂ)
    ((SchwartzMap.derivCLM ℂ ℂ) f)) x = _
  rw [SchwartzMap.derivCLM_apply]
  congr 1
  funext y
  exact SchwartzMap.derivCLM_apply ℂ f y

#print axioms hpSchwartzSecondDeriv_apply

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage3SecondDerivativeAction
