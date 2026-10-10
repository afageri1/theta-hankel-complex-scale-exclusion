#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3HermiteDerivCreation.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteDerivCoordinate

/-!
Commutation of differentiation with the Hermite creation operator:
D (a† f) = a† (D f) + f.
-/

namespace HodgeProofHP

theorem hpSchwartzDeriv_creation (f : SchwartzMap ℝ ℂ) :
    (SchwartzMap.derivCLM ℂ ℂ) (hpSchwartzCreation f) =
      hpSchwartzCreation ((SchwartzMap.derivCLM ℂ ℂ) f) + f := by
  calc
    (SchwartzMap.derivCLM ℂ ℂ) (hpSchwartzCreation f)
        = (SchwartzMap.derivCLM ℂ ℂ)
            (hpSchwartzCoordinateMul f -
              (SchwartzMap.derivCLM ℂ ℂ) f) := by
              simp only [hpSchwartzCreation,
                sub_apply]
    _ = (SchwartzMap.derivCLM ℂ ℂ)
          (hpSchwartzCoordinateMul f) -
          (SchwartzMap.derivCLM ℂ ℂ)
            ((SchwartzMap.derivCLM ℂ ℂ) f) := by
          rw [map_sub]
    _ = (f + hpSchwartzCoordinateMul
          ((SchwartzMap.derivCLM ℂ ℂ) f)) -
          (SchwartzMap.derivCLM ℂ ℂ)
            ((SchwartzMap.derivCLM ℂ ℂ) f) := by
          rw [hpSchwartzDeriv_coordinateMul]
    _ = hpSchwartzCreation
          ((SchwartzMap.derivCLM ℂ ℂ) f) + f := by
          simp only [hpSchwartzCreation,
            sub_apply]
          abel

#print axioms hpSchwartzDeriv_creation

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HermiteDerivCreation.lean
lake build HodgeProofHP.Stage3HermiteDerivCreation
