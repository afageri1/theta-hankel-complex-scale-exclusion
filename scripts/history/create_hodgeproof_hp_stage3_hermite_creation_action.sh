#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3HermiteCreationAction.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteSchwartzFamily

/-!
Pointwise action of the creation operator and the resulting
recurrence for the unnormalised Hermite candidates.
-/

namespace HodgeProofHP

theorem hpSchwartzCreation_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (hpSchwartzCreation f) x =
      x • f x - deriv (f : ℝ → ℂ) x := by
  simp [hpSchwartzCreation, hpSchwartzCoordinateMul_apply,
    SchwartzMap.derivCLM_apply]

theorem hpHermiteSchwartz_zero :
    hpHermiteSchwartz 0 = hpComplexGaussianSchwartz := rfl

theorem hpHermiteSchwartz_succ_apply (n : ℕ) (x : ℝ) :
    (hpHermiteSchwartz (n + 1)) x =
      x • (hpHermiteSchwartz n) x -
        deriv (hpHermiteSchwartz n : ℝ → ℂ) x := by
  change (hpSchwartzCreation (hpHermiteSchwartz n)) x = _
  exact hpSchwartzCreation_apply (hpHermiteSchwartz n) x

#print axioms hpSchwartzCreation_apply
#print axioms hpHermiteSchwartz_succ_apply

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HermiteCreationAction.lean
lake build HodgeProofHP.Stage3HermiteCreationAction
