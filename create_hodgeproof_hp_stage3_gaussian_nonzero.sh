#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3GaussianNonzero.lean <<'LEAN'
import HodgeProofHP.Stage3GaussianL2EigenEquation

/-!
The Gaussian L² vector is nonzero.
-/

namespace HodgeProofHP

theorem hpGaussianGroundL2_ne_zero :
    hpGaussianGroundL2 ≠ 0 := by
  intro hzero
  have hsch : hpComplexGaussianSchwartz = 0 := by
    apply hpSchwartzToL2_injective
    have heq :
        hpSchwartzToL2 hpComplexGaussianSchwartz = 0 := by
      rw [← hpGaussianGroundL2_eq_schwartz]
      exact hzero
    simpa using heq
  have hpoint :=
    congrArg (fun f : SchwartzMap ℝ ℂ => f (0 : ℝ)) hsch
  rw [hpComplexGaussianSchwartz_apply] at hpoint
  have hone : (1 : ℂ) = 0 := by
    simpa [hpGaussianGroundFunction] using hpoint
  exact one_ne_zero hone

#print axioms hpGaussianGroundL2_ne_zero

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3GaussianNonzero.lean
lake build HodgeProofHP.Stage3GaussianNonzero
