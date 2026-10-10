#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "ERROR: Run from the hodgeproof-hp project root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaHankelRowEnergy

target="HodgeProofHP/Stage4ThetaHankelActionL2.lean"
mkdir -p HodgeProofHP

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp -p "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelRowEnergy

/-!
The Hankel integral action belongs to L², by domination
of its squared norm by the integrable row energy.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

theorem hpThetaHankelActionFunction_norm_sq_integrable
    (f : HPThetaHankelSpace) :
    Integrable (fun x => ‖hpThetaHankelActionFunction f x‖ ^ 2)
      hpThetaHankelMeasure := by
  have hmajor :
      Integrable (fun x => hpThetaHankelRowEnergy x * ‖f‖ ^ 2)
        hpThetaHankelMeasure :=
    hpThetaHankelRowEnergy_integrable.mul_const (‖f‖ ^ 2)
  have hmeas :
      AEStronglyMeasurable
        (fun x => ‖hpThetaHankelActionFunction f x‖ ^ 2)
        hpThetaHankelMeasure :=
    (hpThetaHankelActionFunction_aestronglyMeasurable f).norm.pow 2
  refine hmajor.mono' hmeas ?_
  filter_upwards [hpThetaHankelActionFunction_norm_sq_le_ae f] with x hx
  rw [Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (‖hpThetaHankelActionFunction f x‖))]
  exact hx

theorem hpThetaHankelActionFunction_memLp
    (f : HPThetaHankelSpace) :
    MemLp (hpThetaHankelActionFunction f) 2
      hpThetaHankelMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (hpThetaHankelActionFunction_aestronglyMeasurable f)).2
  exact hpThetaHankelActionFunction_norm_sq_integrable f

/-- The integral action as an L² equivalence class. -/
def hpThetaHankelActionL2 (f : HPThetaHankelSpace) :
    HPThetaHankelSpace :=
  (hpThetaHankelActionFunction_memLp f).toLp
    (hpThetaHankelActionFunction f)

theorem hpThetaHankelActionL2_coeFn_ae
    (f : HPThetaHankelSpace) :
    (fun x => hpThetaHankelActionL2 f x) =ᵐ[hpThetaHankelMeasure]
      hpThetaHankelActionFunction f := by
  exact MemLp.coeFn_toLp (hpThetaHankelActionFunction_memLp f)

#print axioms hpThetaHankelActionFunction_norm_sq_integrable
#print axioms hpThetaHankelActionFunction_memLp
#print axioms hpThetaHankelActionL2
#print axioms hpThetaHankelActionL2_coeFn_ae

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelActionL2
echo "PASS: Stage4ThetaHankelActionL2"
