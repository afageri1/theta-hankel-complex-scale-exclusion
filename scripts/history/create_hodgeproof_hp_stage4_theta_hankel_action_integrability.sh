#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "STOP: run from the hodgeproof-hp project root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaHankelKernelL2

target="HodgeProofHP/Stage4ThetaHankelActionIntegrability.lean"
mkdir -p HodgeProofHP

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp -p "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelKernelL2
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
Almost-everywhere integrability of the Hankel action on L2 inputs.
The integral formula is defined here as a function; its L2 bound
and continuous-linear-map construction are separate proof obligations.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

theorem hpThetaHankel_mul_integrable_ae
    (f : ℝ → ℂ) (hf : MemLp f 2 hpThetaHankelMeasure) :
    ∀ᵐ x ∂hpThetaHankelMeasure,
      Integrable
        (fun y : ℝ => hpThetaHankelKernel x y * f y)
        hpThetaHankelMeasure := by
  filter_upwards [hpThetaHankelKernel_row_memLp_ae] with x hx
  have hprod := MemLp.integrable_mul (p := 2) (q := 2) hx hf
  have hmul :
      ((fun y : ℝ => hpThetaHankelKernel x y) * f) =
        (fun y : ℝ => hpThetaHankelKernel x y * f y) := by
    funext y
    rfl
  rw [hmul] at hprod
  exact hprod

theorem hpThetaHankel_L2_mul_integrable_ae
    (f : HPThetaHankelSpace) :
    ∀ᵐ x ∂hpThetaHankelMeasure,
      Integrable
        (fun y : ℝ => hpThetaHankelKernel x y * f y)
        hpThetaHankelMeasure := by
  exact hpThetaHankel_mul_integrable_ae
    (fun y : ℝ => f y) (Lp.memLp f)

def hpThetaHankelActionFunction
    (f : HPThetaHankelSpace) (x : ℝ) : ℂ :=
  ∫ y : ℝ, hpThetaHankelKernel x y * f y
    ∂hpThetaHankelMeasure

theorem hpThetaHankel_integral_congr_ae
    (f g : ℝ → ℂ)
    (hfg : f =ᵐ[hpThetaHankelMeasure] g) (x : ℝ) :
    (∫ y : ℝ, hpThetaHankelKernel x y * f y
      ∂hpThetaHankelMeasure) =
    ∫ y : ℝ, hpThetaHankelKernel x y * g y
      ∂hpThetaHankelMeasure := by
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

#print axioms hpThetaHankel_mul_integrable_ae
#print axioms hpThetaHankel_L2_mul_integrable_ae
#print axioms hpThetaHankelActionFunction
#print axioms hpThetaHankel_integral_congr_ae

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelActionIntegrability

echo "PASS: Stage4ThetaHankelActionIntegrability"
