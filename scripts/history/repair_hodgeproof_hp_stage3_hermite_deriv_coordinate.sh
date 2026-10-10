#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3HermiteDerivCoordinate.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteZeroEigen
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
The derivative of coordinate multiplication on Schwartz space.
This establishes D (x f) = f + x D f.
-/

namespace HodgeProofHP

theorem hpSchwartzCoordinateMul_deriv_apply
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv
        ((hpSchwartzCoordinateMul f : SchwartzMap ℝ ℂ) : ℝ → ℂ) x =
      f x + x • deriv (f : ℝ → ℂ) x := by
  have hfun :
      ((hpSchwartzCoordinateMul f : SchwartzMap ℝ ℂ) : ℝ → ℂ) =
        (fun y : ℝ => y • f y) := by
    funext y
    exact hpSchwartzCoordinateMul_apply f y
  rw [hfun]
  have hc : DifferentiableAt ℝ (fun y : ℝ => y) x :=
    differentiableAt_id
  have hf : DifferentiableAt ℝ (f : ℝ → ℂ) x :=
    f.differentiableAt
  have hpoint :
      ((fun y : ℝ => y) • (f : ℝ → ℂ)) =
        (fun y : ℝ => y • f y) := by
    funext y
    rfl
  have hprod := deriv_smul hc hf
  rw [hpoint] at hprod
  simpa [add_comm] using hprod

theorem hpSchwartzDeriv_coordinateMul
    (f : SchwartzMap ℝ ℂ) :
    (SchwartzMap.derivCLM ℂ ℂ) (hpSchwartzCoordinateMul f) =
      f + hpSchwartzCoordinateMul ((SchwartzMap.derivCLM ℂ ℂ) f) := by
  apply SchwartzMap.ext
  intro x
  change
    deriv
        ((hpSchwartzCoordinateMul f : SchwartzMap ℝ ℂ) : ℝ → ℂ) x =
      f x +
        (hpSchwartzCoordinateMul ((SchwartzMap.derivCLM ℂ ℂ) f)) x
  rw [hpSchwartzCoordinateMul_deriv_apply,
    hpSchwartzCoordinateMul_apply,
    SchwartzMap.derivCLM_apply]

#print axioms hpSchwartzCoordinateMul_deriv_apply
#print axioms hpSchwartzDeriv_coordinateMul

end HodgeProofHP
LEAN

{
  printf '%s\n' '#!/usr/bin/env bash' 'set -euo pipefail' ''
  printf '%s\n' "cat > HodgeProofHP/Stage3HermiteDerivCoordinate.lean <<'LEAN'"
  cat HodgeProofHP/Stage3HermiteDerivCoordinate.lean
  printf '%s\n' 'LEAN' ''
  printf '%s\n' \
    'lake env lean HodgeProofHP/Stage3HermiteDerivCoordinate.lean' \
    'lake build HodgeProofHP.Stage3HermiteDerivCoordinate'
} > create_hodgeproof_hp_stage3_hermite_deriv_coordinate.sh

chmod +x create_hodgeproof_hp_stage3_hermite_deriv_coordinate.sh
./create_hodgeproof_hp_stage3_hermite_deriv_coordinate.sh
