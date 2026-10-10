#!/usr/bin/env bash
set -euo pipefail

file=HodgeProofHP/Stage3SecondDerivativeIntegrationByParts.lean
if [[ -e "$file" ]]; then
  echo "File already exists: $file" >&2
  exit 1
fi

cat > "$file" <<'LEAN'
import HodgeProofHP.Stage3DerivativeIntegrationByParts

/-! Two integrations by parts for the second Schwartz derivative. -/

namespace HodgeProofHP

theorem hpSchwartz_second_deriv_integration_by_parts
    (f g : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, f x * (hpSchwartzSecondDeriv g) x) =
      (∫ x : ℝ, (hpSchwartzSecondDeriv f) x * g x) := by
  let D : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
    SchwartzMap.derivCLM ℂ ℂ
  change (∫ x : ℝ, f x * (D (D g)) x) =
    (∫ x : ℝ, (D (D f)) x * g x)
  calc
    _ = -(∫ x : ℝ, (D f) x * (D g) x) :=
      hpSchwartz_deriv_integration_by_parts f (D g)
    _ = -(-(∫ x : ℝ, (D (D f)) x * g x)) :=
      congrArg Neg
        (hpSchwartz_deriv_integration_by_parts (D f) g)
    _ = _ := by simp

#print axioms hpSchwartz_second_deriv_integration_by_parts

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage3SecondDerivativeIntegrationByParts
