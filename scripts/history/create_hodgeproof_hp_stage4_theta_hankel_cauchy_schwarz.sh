#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "ERROR: Run this script from the hodgeproof-hp project root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaHankelActionMeasurability

target="HodgeProofHP/Stage4ThetaHankelCauchySchwarz.lean"
mkdir -p HodgeProofHP

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp -p "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelActionMeasurability

/-!
Represent the Hankel kernel row in L² and apply Cauchy–Schwarz
to the integral action.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

/-- The kernel row as an L² vector, whenever the row belongs to L². -/
def hpThetaHankelRowL2 (x : ℝ)
    (hx : MemLp (fun y => hpThetaHankelKernel x y)
      2 hpThetaHankelMeasure) : HPThetaHankelSpace :=
  hx.toLp (fun y => hpThetaHankelKernel x y)

theorem hpThetaHankelRowL2_coeFn_ae (x : ℝ)
    (hx : MemLp (fun y => hpThetaHankelKernel x y)
      2 hpThetaHankelMeasure) :
    (fun y => hpThetaHankelRowL2 x hx y) =ᵐ[hpThetaHankelMeasure]
      (fun y => hpThetaHankelKernel x y) := by
  exact MemLp.coeFn_toLp hx

/-- The real kernel row represents the integral action by an inner product. -/
theorem hpThetaHankelActionFunction_eq_inner
    (f : HPThetaHankelSpace) (x : ℝ)
    (hx : MemLp (fun y => hpThetaHankelKernel x y)
      2 hpThetaHankelMeasure) :
    hpThetaHankelActionFunction f x =
      inner ℂ (hpThetaHankelRowL2 x hx) f := by
  rw [MeasureTheory.L2.inner_def]
  change
    (∫ y, hpThetaHankelKernel x y * f y ∂hpThetaHankelMeasure) =
      ∫ y, inner ℂ (hpThetaHankelRowL2 x hx y) (f y)
        ∂hpThetaHankelMeasure
  apply integral_congr_ae
  filter_upwards [hpThetaHankelRowL2_coeFn_ae x hx] with y hy
  rw [hy]
  simp [RCLike.inner_apply', hpThetaHankelKernel, mul_comm]

theorem hpThetaHankelActionFunction_norm_le
    (f : HPThetaHankelSpace) (x : ℝ)
    (hx : MemLp (fun y => hpThetaHankelKernel x y)
      2 hpThetaHankelMeasure) :
    ‖hpThetaHankelActionFunction f x‖ ≤
      ‖hpThetaHankelRowL2 x hx‖ * ‖f‖ := by
  rw [hpThetaHankelActionFunction_eq_inner f x hx]
  exact norm_inner_le_norm _ _

/-- Almost every row admits the L² Cauchy–Schwarz estimate. -/
theorem hpThetaHankelActionFunction_norm_le_ae
    (f : HPThetaHankelSpace) :
    ∀ᵐ x ∂hpThetaHankelMeasure,
      ∃ hx : MemLp (fun y => hpThetaHankelKernel x y)
          2 hpThetaHankelMeasure,
        ‖hpThetaHankelActionFunction f x‖ ≤
          ‖hpThetaHankelRowL2 x hx‖ * ‖f‖ := by
  filter_upwards [hpThetaHankelKernel_row_memLp_ae] with x hx
  exact ⟨hx, hpThetaHankelActionFunction_norm_le f x hx⟩

#print axioms hpThetaHankelRowL2
#print axioms hpThetaHankelRowL2_coeFn_ae
#print axioms hpThetaHankelActionFunction_eq_inner
#print axioms hpThetaHankelActionFunction_norm_le
#print axioms hpThetaHankelActionFunction_norm_le_ae

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelCauchySchwarz
echo "PASS: Stage4ThetaHankelCauchySchwarz"
