#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "Run this script from the hodgeproof-hp project root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaHankelSquareIntegrability

target="HodgeProofHP/Stage4ThetaHankelKernel.lean"

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSquareIntegrability
import Mathlib.MeasureTheory.Integral.Prod

/-!
The complex-valued Hankel kernel K(x,y) = Phi(x+y).
This module proves continuity, symmetry, Hermitian symmetry,
and the pointwise squared-norm identity.
The integral operator and its Hilbert-Schmidt property are not
defined or asserted here.
-/

noncomputable section

namespace HodgeProofHP

def hpThetaHankelKernel (x y : ℝ) : ℂ :=
  (hpRiemannThetaDifferentialKernel (x + y) : ℂ)

theorem hpThetaHankelKernel_continuous :
    Continuous (fun p : ℝ × ℝ => hpThetaHankelKernel p.1 p.2) := by
  unfold hpThetaHankelKernel
  exact Complex.continuous_ofReal.comp
    (hpRiemannThetaDifferentialKernel_continuous.comp
      (continuous_fst.add continuous_snd))

theorem hpThetaHankelKernel_symmetric (x y : ℝ) :
    hpThetaHankelKernel x y = hpThetaHankelKernel y x := by
  simp only [hpThetaHankelKernel, add_comm]

theorem hpThetaHankelKernel_hermitian (x y : ℝ) :
    star (hpThetaHankelKernel y x) = hpThetaHankelKernel x y := by
  simp [hpThetaHankelKernel, add_comm]

theorem hpThetaHankelKernel_norm_sq (x y : ℝ) :
    ‖hpThetaHankelKernel x y‖ ^ 2 =
      hpRiemannThetaDifferentialKernel (x + y) ^ 2 := by
  simp [hpThetaHankelKernel, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

#print axioms hpThetaHankelKernel_continuous
#print axioms hpThetaHankelKernel_symmetric
#print axioms hpThetaHankelKernel_hermitian
#print axioms hpThetaHankelKernel_norm_sq

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelKernel

echo "===== Translation and product integration APIs ====="
rg -n -A 16 -B 2 \
  'theorem (lintegral_prod|integral_prod|integral_add_right|integral_add_left|integral_comp_add_right|integral_comp_add_left|integral.*Ioi.*Ioi|lintegral.*Ioi.*Ioi|integral.*add.*Ioi|integral.*Ioi.*add)' \
  .lake/packages/mathlib/Mathlib/MeasureTheory \
  --glob '*.lean' || true

echo "PASS: theta Hankel kernel properties"
