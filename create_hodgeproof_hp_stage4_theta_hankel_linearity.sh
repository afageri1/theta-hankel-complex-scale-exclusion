#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "ERROR: Run from the hodgeproof-hp project root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaHankelActionL2

target="HodgeProofHP/Stage4ThetaHankelLinearity.lean"
mkdir -p HodgeProofHP

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp -p "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelActionL2

/-!
Linearity of the Hankel action on L², using its
almost-everywhere representation by an inner product.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

theorem hpThetaHankelActionFunction_add_ae
    (f g : HPThetaHankelSpace) :
    (fun x => hpThetaHankelActionFunction (f + g) x)
      =ᵐ[hpThetaHankelMeasure]
    (fun x => hpThetaHankelActionFunction f x +
      hpThetaHankelActionFunction g x) := by
  filter_upwards [hpThetaHankelKernel_row_memLp_ae] with x hx
  rw [hpThetaHankelActionFunction_eq_inner (f + g) x hx,
    hpThetaHankelActionFunction_eq_inner f x hx,
    hpThetaHankelActionFunction_eq_inner g x hx,
    inner_add_right]

theorem hpThetaHankelActionFunction_smul_ae
    (c : ℂ) (f : HPThetaHankelSpace) :
    (fun x => hpThetaHankelActionFunction (c • f) x)
      =ᵐ[hpThetaHankelMeasure]
    (fun x => c • hpThetaHankelActionFunction f x) := by
  filter_upwards [hpThetaHankelKernel_row_memLp_ae] with x hx
  simp only [hpThetaHankelActionFunction_eq_inner (c • f) x hx,
    hpThetaHankelActionFunction_eq_inner f x hx,
    inner_smul_right, smul_eq_mul]

theorem hpThetaHankelActionL2_add
    (f g : HPThetaHankelSpace) :
    hpThetaHankelActionL2 (f + g) =
      hpThetaHankelActionL2 f + hpThetaHankelActionL2 g := by
  apply Lp.ext
  filter_upwards [
    hpThetaHankelActionL2_coeFn_ae (f + g),
    hpThetaHankelActionL2_coeFn_ae f,
    hpThetaHankelActionL2_coeFn_ae g,
    Lp.coeFn_add (hpThetaHankelActionL2 f) (hpThetaHankelActionL2 g),
    hpThetaHankelActionFunction_add_ae f g
  ] with x hsum hf hg hcoe hadd
  simpa only [Pi.add_apply, hsum, hf, hg, hcoe] using hadd

theorem hpThetaHankelActionL2_smul
    (c : ℂ) (f : HPThetaHankelSpace) :
    hpThetaHankelActionL2 (c • f) =
      c • hpThetaHankelActionL2 f := by
  apply Lp.ext
  filter_upwards [
    hpThetaHankelActionL2_coeFn_ae (c • f),
    hpThetaHankelActionL2_coeFn_ae f,
    Lp.coeFn_smul c (hpThetaHankelActionL2 f),
    hpThetaHankelActionFunction_smul_ae c f
  ] with x hcf hf hcoe hsmul
  simpa only [Pi.smul_apply, hcf, hf, hcoe] using hsmul

/-- The Hankel action as a complex-linear map on L². -/
def hpThetaHankelLinearMap :
    HPThetaHankelSpace →ₗ[ℂ] HPThetaHankelSpace where
  toFun := hpThetaHankelActionL2
  map_add' := hpThetaHankelActionL2_add
  map_smul' := hpThetaHankelActionL2_smul

theorem hpThetaHankelLinearMap_apply
    (f : HPThetaHankelSpace) :
    hpThetaHankelLinearMap f = hpThetaHankelActionL2 f := rfl

#print axioms hpThetaHankelActionFunction_add_ae
#print axioms hpThetaHankelActionFunction_smul_ae
#print axioms hpThetaHankelActionL2_add
#print axioms hpThetaHankelActionL2_smul
#print axioms hpThetaHankelLinearMap
#print axioms hpThetaHankelLinearMap_apply

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelLinearity
echo "PASS: Stage4ThetaHankelLinearity"
