#!/usr/bin/env bash
set -euo pipefail

sed -i 's/ContinuousLinearMap\.sub_apply/sub_apply/g' \
  HodgeProofHP/Stage3HermiteDerivCreation.lean \
  create_hodgeproof_hp_stage3_hermite_deriv_creation.sh

lake env lean HodgeProofHP/Stage3HermiteDerivCreation.lean
lake build HodgeProofHP.Stage3HermiteDerivCreation

cat > HodgeProofHP/Stage3HermiteCreationCoordinate.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteDerivCreation

/-!
Commutation of the Hermite creation operator with multiplication
by the real coordinate on complex Schwartz space.
-/

namespace HodgeProofHP

theorem hpSchwartzCreation_coordinateMul
    (f : SchwartzMap ℝ ℂ) :
    hpSchwartzCreation (hpSchwartzCoordinateMul f) =
      hpSchwartzCoordinateMul (hpSchwartzCreation f) - f := by
  calc
    hpSchwartzCreation (hpSchwartzCoordinateMul f)
        = hpSchwartzCoordinateMul (hpSchwartzCoordinateMul f) -
            (SchwartzMap.derivCLM ℂ ℂ)
              (hpSchwartzCoordinateMul f) := by
          simp only [hpSchwartzCreation, sub_apply]
    _ = hpSchwartzCoordinateMul (hpSchwartzCoordinateMul f) -
          (f + hpSchwartzCoordinateMul
            ((SchwartzMap.derivCLM ℂ ℂ) f)) := by
          rw [hpSchwartzDeriv_coordinateMul]
    _ = hpSchwartzCoordinateMul (hpSchwartzCreation f) - f := by
          simp only [hpSchwartzCreation, sub_apply, map_sub]
          abel

#print axioms hpSchwartzCreation_coordinateMul

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HermiteCreationCoordinate.lean
lake build HodgeProofHP.Stage3HermiteCreationCoordinate
