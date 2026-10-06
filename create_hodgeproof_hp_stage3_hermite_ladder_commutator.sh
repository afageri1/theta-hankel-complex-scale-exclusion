#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3HermiteLadderCommutator.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteCreationCoordinate

/-!
The annihilation operator and its commutator with the creation
operator on complex Schwartz space.
-/

namespace HodgeProofHP

noncomputable def hpSchwartzAnnihilation :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  hpSchwartzCoordinateMul + SchwartzMap.derivCLM ℂ ℂ

theorem hpSchwartzAnnihilation_creation
    (f : SchwartzMap ℝ ℂ) :
    hpSchwartzAnnihilation (hpSchwartzCreation f) =
      hpSchwartzCreation (hpSchwartzAnnihilation f) +
        (2 : ℂ) • f := by
  have hX :
      hpSchwartzCoordinateMul (hpSchwartzCreation f) =
        hpSchwartzCreation (hpSchwartzCoordinateMul f) + f := by
    calc
      hpSchwartzCoordinateMul (hpSchwartzCreation f)
          = (hpSchwartzCoordinateMul (hpSchwartzCreation f) - f) + f := by
              abel
      _ = hpSchwartzCreation (hpSchwartzCoordinateMul f) + f := by
            rw [hpSchwartzCreation_coordinateMul]
  calc
    hpSchwartzAnnihilation (hpSchwartzCreation f)
        = hpSchwartzCoordinateMul (hpSchwartzCreation f) +
            (SchwartzMap.derivCLM ℂ ℂ)
              (hpSchwartzCreation f) := by
            simp only [hpSchwartzAnnihilation, add_apply]
    _ = (hpSchwartzCreation (hpSchwartzCoordinateMul f) + f) +
          (hpSchwartzCreation
            ((SchwartzMap.derivCLM ℂ ℂ) f) + f) := by
          rw [hX, hpSchwartzDeriv_creation]
    _ = hpSchwartzCreation (hpSchwartzAnnihilation f) +
          (2 : ℂ) • f := by
          simp only [hpSchwartzAnnihilation, add_apply, map_add, two_smul]
          abel

#print axioms hpSchwartzAnnihilation
#print axioms hpSchwartzAnnihilation_creation

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HermiteLadderCommutator.lean
lake build HodgeProofHP.Stage3HermiteLadderCommutator
