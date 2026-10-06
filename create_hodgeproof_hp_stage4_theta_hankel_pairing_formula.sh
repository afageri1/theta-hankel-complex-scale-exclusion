#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "STOP: run this script from ~/hodgeproof-hp"
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaHankelPairingIntegrability

target="HodgeProofHP/Stage4ThetaHankelPairingFormula.lean"
mkdir -p HodgeProofHP

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelPairingIntegrability

/-!
The inner-product pairing of the bounded theta Hankel operator,
expressed as an iterated integral in both orders.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

theorem hpThetaHankelOperator_inner_eq_iterated
    (f g : HPThetaHankelSpace) :
    inner ℂ f (hpThetaHankelOperator g) =
      ∫ x, ∫ y,
        hpThetaHankelKernel x y * (star (f x) * g y)
        ∂hpThetaHankelMeasure ∂hpThetaHankelMeasure := by
  rw [L2.inner_def]
  change
    (∫ x, inner ℂ (f x) ((hpThetaHankelOperator g) x)
      ∂hpThetaHankelMeasure) = _
  apply integral_congr_ae
  filter_upwards
    [hpThetaHankelOperator_coeFn_ae g,
     hpThetaHankel_L2_mul_integrable_ae g] with x hx hg
  change
    inner ℂ (f x) ((hpThetaHankelOperator g) x) =
      ∫ y, hpThetaHankelKernel x y * (star (f x) * g y)
        ∂hpThetaHankelMeasure
  rw [hx]
  change
    inner ℂ (f x)
      (∫ y, hpThetaHankelKernel x y * g y
        ∂hpThetaHankelMeasure) =
      ∫ y, hpThetaHankelKernel x y * (star (f x) * g y)
        ∂hpThetaHankelMeasure
  rw [← integral_inner hg (f x)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    change
      inner ℂ (f x) (hpThetaHankelKernel x y * g y) =
        hpThetaHankelKernel x y * (star (f x) * g y)
    simp [RCLike.inner_apply', mul_assoc, mul_comm, mul_left_comm])

theorem hpThetaHankelOperator_inner_eq_swapped
    (f g : HPThetaHankelSpace) :
    inner ℂ f (hpThetaHankelOperator g) =
      ∫ y, ∫ x,
        hpThetaHankelKernel x y * (star (f x) * g y)
        ∂hpThetaHankelMeasure ∂hpThetaHankelMeasure := by
  calc
    inner ℂ f (hpThetaHankelOperator g) =
        ∫ x, ∫ y,
          hpThetaHankelKernel x y * (star (f x) * g y)
          ∂hpThetaHankelMeasure ∂hpThetaHankelMeasure :=
      hpThetaHankelOperator_inner_eq_iterated f g
    _ = ∫ y, ∫ x,
          hpThetaHankelKernel x y * (star (f x) * g y)
          ∂hpThetaHankelMeasure ∂hpThetaHankelMeasure :=
      hpThetaHankelPairing_integral_swap f g

#print axioms hpThetaHankelOperator_inner_eq_iterated
#print axioms hpThetaHankelOperator_inner_eq_swapped

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelPairingFormula

echo "PASS: Stage4ThetaHankelPairingFormula"
